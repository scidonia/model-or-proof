"""Route B's model port over OMP, the harness's model-call transport (plan D3/D20).

Plan D3 and protocol §4.5/§11 decision 7: **one** model for the whole experiment, with the thinking
level fixed by the harness and recorded per row — and, since D20, everything else about the call owned
by OMP: credentials, provider routing and fallback, retries, and **cost accounting**. The harness prices
nothing itself; the dollars a row reports are the ``cost`` OMP records for the sessions the run opened
(§11 decision 7's "as recorded in the session's ``usage.cost``"), and ``cost_basis`` names that
provenance instead of a price card. The selector and the thinking level are module constants and live
nowhere else; ``harness.route_b`` writes them into every row verbatim, through the loop's ``usage``
channel, and ``resolvedModelIsFallback`` is set when OMP reports it served a turn with a different model
id than the selector.

The transport is one ``omp --mode rpc`` process per **role** (plan D20), each started with its role's
system prompt, ``--model`` and ``--thinking``, ``--no-tools`` (the model must answer with a tactic,
command or plan, not act as an agent), and ``--no-session`` (ephemeral: nothing is written to disk and
no user session is inherited or polluted, which is what makes a run reproducible from the row). A turn
is one ``prompt``; its usage is OMP's ``message_end.message.usage``, and the session totals come from
``get_session_stats``. The client is network-bound and is **never** constructed by a pytest scenario —
the loop's scenarios use a scripted model.

What the model is shown is the client's whole business (plan D14): each turn's message carries the
specification the seed states, the few-shot examples, the current goals, and the tactics tried — every
refused proposal with the REPL's reason the loop recorded, every empty reply with the loop's nudge.
Nothing else reaches the prompt, so no invariant or helper-lemma statement can be shown without the
specification stating it, and the composition is reported per row rather than asserted here.
"""

from __future__ import annotations

import atexit
import json
import queue
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.closure import HistoryEntry, ProviderError  # noqa: E402

# The transport (plan D20). `omp --mode rpc` speaks newline-delimited JSON over stdio: commands in,
# frames out, with one `ready` frame at startup.
OMP_BIN = "omp"
OMP_ROLES = ("proof", "refutation", "plan")
OMP_FIXED_FLAGS = ("--mode", "rpc", "--no-ui", "--no-session", "--no-tools")

# One turn's cap. A reasoning model can think for minutes; the run's own wall-clock budget is the
# loop's business, and this bound only exists so a wedged process becomes a recorded ProviderError
# rather than a run that never returns.
TURN_TIMEOUT_S = 900.0
STARTUP_TIMEOUT_S = 120.0

# Enumerated on this host rather than typed from memory (plan D3's caveat): the provider reaches
# exactly `deepseek-flash` and `deepseek-v4-pro`, and both are reasoning models (effort low/high/max).
# `deepseek-v4-pro` is the stronger of the two, so it is the selector, passed as `--model deepseek/…`.
# OMP reports the id it served, and `resolvedModelIsFallback` compares the selector against *that*
# (`get_state.model.id` / the turn's `message.model`), so an unladen id is what keeps the comparison
# exact.
MODEL_SELECTOR = "deepseek-v4-pro"
THINKING_LEVEL = "high"

SYSTEM_PROMPT = (
    "You are closing a Lean 4 theorem in a proof-assistant REPL, one tactic at a time. "
    "Each turn you are shown the specification the file under test states, the statement under test, "
    "the current goal state, and the tactics already tried — with the REPL's own reason for any "
    "proposal it refused. "
    "Reply with exactly one Lean 4 tactic and nothing else: no explanation, no code fence, no prose. "
    "The tactic is applied to the goal the REPL reports; if it leaves further goals you are asked again "
    "with the new state."
)

REFUTATION_SYSTEM_PROMPT = (
    "You are refuting a Lean 4 theorem in a proof-assistant REPL, one Lean 4 command at a time. "
    "Each turn you are shown the specification the file under test states, the statement under test, "
    "the current goal state, and the commands already tried — with the REPL's own reason for any "
    "command it refused. "
    "Reply with exactly one Lean 4 command and nothing else: no explanation, no code fence, no prose. "
    "The command is run through the REPL's command channel, so an explicit witness "
    "(`example … := by exact …`), a bounded enumeration (`by decide`, `by native_decide`) and a proof "
    "of the statement's negation all execute, and Lean — not you — decides whether it went through. "
    "A refutation counts only when Lean accepts the command with nothing left to prove."
)

# The shape the refutation command must have (plan D16/D17): the negation of the statement under test,
# proved. It is shown in the refutation turn's message and recorded in the row's setup, so a reader can
# see what the model was asked for and check the accepted command against it: the driver certifies from
# the response that Lean closed the command with no hole, never that the command states the goal's
# negation.
REFUTATION_TEMPLATE = "example : ¬ (<the statement under test>) := by\n  <a proof of its negation>"

REFUTATION_INSTRUCTION = (
    "Reply with one Lean 4 command of that form, with the statement under test and a proof of its "
    "negation filled in."
)

# The planning turn (plan D19): once per arm, before that arm acts, the model states how it intends to
# proceed. The slots are neutral — an approach, steps, an expected end state, and a slot for a
# candidate statement the model may want to use — because the experiment's boundary is that the
# *activity* may be invited while the *content* never is: the candidate slot invites a guess without
# naming what token-ring needs, and no line here states, hints at, or exemplifies the missing invariant.
PLAN_SYSTEM_PROMPT = (
    "You are about to close a Lean 4 theorem in a proof-assistant REPL, one tactic at a time. "
    "Before you start, state a short plan for how you intend to proceed, so it can be recorded beside "
    "the run. "
    "Reply with the plan and nothing else: one line per slot, no prose beyond the slots, no code fence."
)

PLAN_TEMPLATE = (
    "approach: <how you intend to close the statement>\n"
    "steps: <the main steps you expect to take>\n"
    "expected end state: <what the goal should look like when it is closed>\n"
    "candidate: <any statement you intend to use that the file does not already state — you may "
    "introduce a helper lemma or a stronger statement, or none>"
)

PLAN_INSTRUCTION = (
    "Reply with a short plan for this run, one line per slot, in exactly this shape:\n\n"
    f"{PLAN_TEMPLATE}"
)

# The committed, versioned few-shot examples (plan D19). They teach *technique* — running an induction
# over an inductive predicate, splitting a disjunctive hypothesis, finishing with the named automation,
# handling a finite set, and, as the one modelling example, a strengthening move on a *different*
# system — and contain no part of this task's own insight: no forbidden hint appears in the file
# (tests/test_route_b_row.py asserts that), and the version below is what the row's setup records, so a
# prompt change is visible in a row rather than implied by it.
EXAMPLES_PATH = Path(__file__).resolve().parents[1] / "proofs" / "lean" / "token-ring" / "prompt_examples.lean"
EXAMPLES_VERSION = "d19-1"


def prompt_examples(path: Path = EXAMPLES_PATH) -> str:
    """The few-shot examples every turn's prompt carries (plan D19), read from the committed file.

    A missing or unreadable file is a hard failure rather than an empty section: the run's prompt would
    silently be a different prompt from the one the row's ``setup`` claims, and the examples are
    evidence a reader is meant to be able to check.
    """
    return path.read_text()


# What one turn's prompt is assembled from (plan D14/D16/D19). The composition is structural rather than a
# note to the model: `user_message` reads the specification, the goals, the examples and the loop's
# history and nothing else, so no invariant or helper-lemma statement can reach the prompt without the
# specification stating it. What the row records is that composition (`row["prompt"]["sections"]`)
# together with what the specification actually showed (`row["prompt"]["shown"]`, written by
# `harness.route_b` from the excerpt's own inventory) — evidence a reader can check, never a claim this
# module makes about what it withheld. A section with nothing to say on a given turn — the history on
# the first turn, a refusal when nothing was refused — is empty there. The refutation sections belong to
# the refutation turn and the plan section to the planning turn, so a run that took neither does not
# claim them.
PROMPT_SECTIONS = ("specification", "examples", "goals", "tactic_history", "refusal_reason")
REFUTATION_SECTIONS = ("refutation_template", "refutation_instruction")
PLAN_SECTIONS = ("plan_instruction",)


def user_message(
    specification: str,
    goals: Sequence[str],
    history: Sequence[HistoryEntry],
    *,
    arm: str = "proof",
    examples: str = "",
) -> str:
    """The turn's user message (plan D14/D16): the specification the seed states, the current goals,
    and what has been tried — every proposal the prover refused with the REPL's own reason, and every
    empty reply with the loop's nudge, so the model can stop guessing at names the goal state never
    refutes.

    ``specification`` is the whole of the context beyond the goal state and the proposals: what the file
    under test states (protocol §8), assembled by ``harness.route_b`` from the seed and its project-local
    imports. A turn the prover applied shows the goal state it left; a refused one shows why the state
    did not move.

    ``arm`` names what the turn asks for: the proof arm asks for the next tactic, the refutation arm for
    one Lean 4 command in :data:`REFUTATION_TEMPLATE`'s shape. The material is the same either way, so a
    refutation is proposed under the same withholding as a proof (plan D14) — nothing but the
    specification, the examples, the goals and the loop's history reaches the prompt, and a refused
    proposal arrives with its reason, which the refutation arm needs as much as the proof arm.

    ``examples`` is the committed few-shot text (plan D19): technique only, carried on every turn so the
    model has the same material whichever arm is asking. It is empty only when a caller has no examples
    to show, and then the composition says so rather than claiming a section it did not send.
    """
    if arm not in ("proof", "refutation"):
        raise ValueError(f"unknown arm {arm!r}: expected 'proof' or 'refutation'")
    noun = "tactic" if arm == "proof" else "command"
    lines = ["The specification under test:", "", specification.strip()]
    if examples.strip():
        lines.extend(["", "Few-shot examples of proof technique:", "", examples.strip()])
    lines.extend(["", "Current goals:", *(f"  {goal}" for goal in goals)])
    if history:
        lines.extend(["", f"{noun.capitalize()}s tried so far:"])
        for index, (proposal, resulting, note) in enumerate(history, 1):
            if not proposal:
                lines.append(f"{noun.capitalize()} {index}: (empty reply)")
                lines.append(f"  no {noun} was applied — {note}")
                continue
            lines.append(f"{noun.capitalize()} {index}: {proposal}")
            if note:
                lines.append(f"  refused by the REPL — {note}")
                continue
            lines.extend(f"  goal now: {goal}" for goal in resulting)
            if not resulting:
                lines.append("  goal now: (closed)")
    if arm == "refutation":
        lines.extend(
            [
                "",
                "The refutation command's shape:",
                "",
                REFUTATION_TEMPLATE,
                "",
                REFUTATION_INSTRUCTION,
            ]
        )
    else:
        lines.extend(["", "Reply with the next tactic."])
    return "\n".join(lines)


def plan_message(
    specification: str,
    goals: Sequence[str],
    history: Sequence[HistoryEntry] = (),
    *,
    examples: str = "",
) -> str:
    """The planning turn's user message (plan D19): what the run is about, and the slots to fill.

    It carries the same material as a turn's message — the specification the file states and the goals,
    with the few-shot examples — and asks for the plan instead of a tactic. The one difference is the
    candidate slot: it invites the model to name a statement it means to use that the file does not
    already state, which is the *activity* the experiment permits inviting; the invariant token-ring
    needs is nowhere in this text, and no line hints at it.

    ``history`` carries what the loop said about an earlier attempt at the plan: an empty plan is
    re-asked rather than dropped (plan D11), and a re-ask the model cannot see would just be the same
    question again.
    """
    lines = ["The specification under test:", "", specification.strip()]
    if examples.strip():
        lines.extend(["", "Few-shot examples of proof technique:", "", examples.strip()])
    lines.extend(["", "Current goals:", *(f"  {goal}" for goal in goals)])
    notes = [note for _, _, note in history if note]
    if notes:
        lines.extend(["", "Earlier attempts at this plan:", *(f"  {note}" for note in notes)])
    lines.extend(["", PLAN_INSTRUCTION])
    return "\n".join(lines)


def extract_plan(content: str) -> str:
    """The plan out of a model reply (plan D19): the reply itself, surrounding whitespace trimmed.

    A plan is recorded **verbatim** — it is evidence of how the model reasoned, not a summary the
    harness composed — so nothing is unwrapped, reformatted or shortened. The trim is what lets an
    empty reply be recognised as empty and take D11's nudge path; everything between the trims is the
    model's own text.
    """
    return content.strip()


def extract_tactic(content: str) -> str:
    """The tactic to apply out of a model reply, unwrapping a code fence if the model used one.

    The reply is otherwise applied verbatim — a tactic may span lines — because a fence is syntax the
    repl would reject, while an unhelpful reply should reach the prover as the model wrote it.
    """
    text = content.strip()
    if "```" in text:
        body = text.split("```", 1)[1]
        if "```" in body:
            body = body.split("```", 1)[0]
        lines = body.split("\n")
        if lines and lines[0].strip().lower() in ("lean", "lean4"):
            body = "\n".join(lines[1:])
        text = body.strip()
    return text




# The system prompt each role's session is started with (plan D16/D19/D20): the transport passes it as
# `--system-prompt`, so every arm's turns run under its own framing rather than a shared one.
SYSTEM_PROMPTS = {
    "proof": SYSTEM_PROMPT,
    "refutation": REFUTATION_SYSTEM_PROMPT,
    "plan": PLAN_SYSTEM_PROMPT,
}

# `omp --version` cannot change while a run is in flight, and a row records it: ask once.
_OMP_VERSION: str | None = None


def omp_version(binary: str = OMP_BIN) -> str:
    """The transport's own version, from ``omp --version`` (plans D17/D20).

    A row is attributable to the exact call shape, and the call shape belongs to a version: the flags,
    the frame schema and the cost record are OMP's, so a row that does not name the version cannot be
    reproduced. Cached because it cannot change mid-run.
    """
    global _OMP_VERSION
    if _OMP_VERSION is None:
        completed = subprocess.run([binary, "--version"], capture_output=True, text=True)
        answer = completed.stdout.strip() or completed.stderr.strip()
        _OMP_VERSION = answer or f"unknown (exit {completed.returncode})"
    return _OMP_VERSION


def omp_command(
    system_prompt: str,
    *,
    selector: str = MODEL_SELECTOR,
    thinking: str = THINKING_LEVEL,
    binary: str = OMP_BIN,
) -> list[str]:
    """The exact command one role's RPC session is started with (plan D20).

    The one place the flags are written, so what the transport runs and what a row's ``setup`` records
    cannot drift apart: RPC over stdio, headless, **ephemeral** (``--no-session`` writes nothing to disk
    and inherits no user session, which is what makes a run reproducible), **no tools** (the model must
    answer with a tactic, a command or a plan — not act as an agent), the fixed selector and thinking
    level, and this role's system prompt.
    """
    return [
        binary,
        *OMP_FIXED_FLAGS,
        "--model",
        selector,
        "--thinking",
        thinking,
        "--system-prompt",
        system_prompt,
    ]


def omp_invocation(
    *, selector: str = MODEL_SELECTOR, thinking: str = THINKING_LEVEL, binary: str = OMP_BIN
) -> dict:
    """The invocation a row's ``setup`` records (plans D17/D20).

    The version, the binary, the roles a run opens, and the flags each session starts with. A role's
    system prompt is *named* rather than inlined — it is a long constant in this module and changes with
    the plan, not with the run — while everything else a reader needs to reproduce the call is here
    verbatim.
    """
    return {
        "version": omp_version(binary),
        "binary": binary,
        "roles": list(OMP_ROLES),
        "flags": [
            *OMP_FIXED_FLAGS,
            "--model",
            selector,
            "--thinking",
            thinking,
            "--system-prompt",
            "<the role's own system prompt>",
        ],
    }


def _drain_lines(stream, sink: "queue.Queue[str | None]") -> None:
    """Feed a child's stdout lines to a queue, with a ``None`` sentinel when the stream ends.

    The caller must see EOF rather than wait out its timeout: a transport that died is a recorded
    failure, not a turn that never returns.
    """
    for line in stream:
        sink.put(line)
    sink.put(None)


def _drain_stderr(stream, sink: list[str]) -> None:
    """Keep the child's diagnostics: a failing `omp` explains itself there, outside the frame stream."""
    for line in stream:
        sink.append(line.rstrip("\n"))


class OmpSession:
    """One ``omp --mode rpc`` process: the transport for one role's turns (plan D20).

    A turn is one ``prompt`` command: acknowledged immediately, completed by its own
    ``prompt_result`` frame (correlated by the id the command carried — responses are matched on ids,
    never on emission order). The turn's answer is the last assistant message; its usage is that
    message's own record, which is OMP's account of what the call cost.
    """

    def __init__(
        self,
        system_prompt: str,
        *,
        selector: str = MODEL_SELECTOR,
        thinking: str = THINKING_LEVEL,
        binary: str = OMP_BIN,
        timeout_s: float = TURN_TIMEOUT_S,
        startup_timeout_s: float = STARTUP_TIMEOUT_S,
    ) -> None:
        self.cmd = omp_command(system_prompt, selector=selector, thinking=thinking, binary=binary)
        self.timeout_s = timeout_s
        self._counter = 0
        self._lines: "queue.Queue[str | None]" = queue.Queue()
        self._stderr: list[str] = []
        try:
            self._process = subprocess.Popen(
                self.cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
        except OSError as error:
            raise ProviderError(0, f"cannot start {self.cmd[0]}: {error}") from error
        threading.Thread(target=_drain_lines, args=(self._process.stdout, self._lines), daemon=True).start()
        threading.Thread(target=_drain_stderr, args=(self._process.stderr, self._stderr), daemon=True).start()
        # A session the loop never closes must not outlive the run: `omp` is a real process, and one
        # per role would otherwise pile up behind a crashed CLI.
        atexit.register(self.close)
        self._await_ready(startup_timeout_s)

    # --- one turn ------------------------------------------------------------
    def prompt(self, message: str, *, timeout: float | None = None) -> dict:
        """Run one model turn and return what it produced: text, model, provider and usage.

        The prompt command is acknowledged before the turn runs, so the turn's end is its
        ``prompt_result``: `status` says how it ended (`completed`, `aborted`, `error`), and an error
        carries the provider's own message and HTTP status. Anything but `completed` is raised as a
        ``ProviderError`` under the loop's D12 rule — an outcome to record, not a run to lose — with
        OMP's message verbatim, because OMP has already exhausted its own retries by then.
        """
        request_id = self._next_id("prompt")
        self._write({"id": request_id, "type": "prompt", "message": message})
        frames: list[dict] = []
        deadline = time.monotonic() + (self.timeout_s if timeout is None else timeout)
        while True:
            frame = self._read(deadline, f"the answer to {request_id}")
            frames.append(frame)
            if frame.get("type") == "prompt_result" and frame.get("id") == request_id:
                self._check_result(frame)
                break
        return self._turn(frames)

    def get_state(self) -> dict:
        """OMP's own report of the session: the model it is on, the thinking level, its context."""
        response, _ = self._request({"type": "get_state"})
        return response.get("data") or {}

    # --- protocol ------------------------------------------------------------
    def _request(self, payload: dict) -> tuple[dict, list[dict]]:
        """Send one command and read until its correlated response, returning the frames read."""
        request_id = self._next_id(payload["type"])
        self._write({"id": request_id, **payload})
        frames: list[dict] = []
        deadline = time.monotonic() + self.timeout_s
        while True:
            frame = self._read(deadline, f"the response to {payload['type']}")
            frames.append(frame)
            if frame.get("type") == "response" and frame.get("id") == request_id:
                if not frame.get("success"):
                    raise ProviderError(0, f"omp refused {payload['type']}: {frame.get('error')}")
                return frame, frames

    def _await_ready(self, timeout: float) -> None:
        """Read the startup `ready` frame, or fail loudly: nothing can be sent before it.

        A client that speaks v2 would negotiate here; this harness stays on v1, whose frames are capped
        at the advertised physical limit, and a larger answer is an explicit error rather than a
        silently truncated one (see :meth:`_read`).
        """
        deadline = time.monotonic() + timeout
        while True:
            frame = self._read(deadline, "the ready frame")
            if frame.get("type") == "ready":
                return

    def _write(self, payload: dict) -> None:
        if self._process is None or self._process.poll() is not None:
            raise ProviderError(0, f"omp is not running{self._stderr_tail()}")
        try:
            self._process.stdin.write(json.dumps(payload) + "\n")
            self._process.stdin.flush()
        except (BrokenPipeError, ValueError, OSError) as error:
            raise ProviderError(0, f"omp is not reading input: {error}{self._stderr_tail()}") from error

    def _read(self, deadline: float, describing: str) -> dict:
        """One frame from stdout, bounded by ``deadline``."""
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            self.close()
            raise ProviderError(0, f"omp did not answer {describing} within {self.timeout_s:g}s")
        try:
            line = self._lines.get(timeout=remaining)
        except queue.Empty:
            self.close()
            raise ProviderError(0, f"omp did not answer {describing} within {self.timeout_s:g}s") from None
        if line is None:
            raise ProviderError(0, f"omp exited while sending {describing}{self._stderr_tail()}")
        try:
            frame = json.loads(line)
        except json.JSONDecodeError as error:
            raise ProviderError(0, f"omp sent a frame that is not JSON: {line[:400]!r}") from error
        if not isinstance(frame, dict):
            raise ProviderError(0, f"omp sent a frame that is not an object: {frame!r}")
        if frame.get("type") == "rpc_chunk":
            raise ProviderError(
                0,
                "omp split a frame into rpc_chunk segments; this harness stays on protocol v1 and will "
                "not guess a reassembly",
            )
        return frame

    def _check_result(self, frame: dict) -> None:
        """Turn a `prompt_result` into an answer or the provider failure it reported."""
        status = frame.get("status")
        if status == "completed":
            return
        failure = frame.get("error") or {}
        message = failure.get("message") or json.dumps({k: v for k, v in frame.items() if k != "type"})[:400]
        status_code = failure.get("httpStatus")
        raise ProviderError(
            status_code if isinstance(status_code, int) else 0,
            f"omp's turn ended {status!r}: {message}",
        )

    def _turn(self, frames: list[dict]) -> dict:
        """The turn's answer: the last assistant message, with its model and its usage record."""
        assistant = [
            frame["message"]
            for frame in frames
            if frame.get("type") in ("message_end", "turn_end")
            and isinstance(frame.get("message"), dict)
            and frame["message"].get("role") == "assistant"
        ]
        if not assistant:
            raise ProviderError(0, "omp's turn carried no assistant message to answer with")
        message = assistant[-1]
        return {
            "text": "\n".join(
                part.get("text", "")
                for part in message.get("content") or []
                if isinstance(part, dict) and part.get("type") == "text"
            ),
            "model": message.get("model"),
            "provider": message.get("provider"),
            "usage": message.get("usage") or {},
            "stop_reason": message.get("stopReason"),
        }

    def _next_id(self, label: str) -> str:
        self._counter += 1
        return f"{label}-{self._counter}"

    def _stderr_tail(self, lines: int = 20) -> str:
        tail = "\n".join(self._stderr[-lines:])
        return f"\nomp stderr:\n{tail}" if tail else ""

    def close(self) -> None:
        """Stop the process: closing its stdin ends the session, and the tail is drained first."""
        process, self._process = getattr(self, "_process", None), None
        if process is None or process.poll() is not None:
            return
        try:
            if process.stdin is not None:
                process.stdin.close()
        except OSError:
            pass
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()


class OmpModel:
    """The ``Model`` port over OMP's RPC sessions (plan D20).

    One session per role (proof, refutation, planning), each started with that role's system prompt and
    the run's fixed selector and thinking level, so the arms are separate conversations with one model
    and the planning turn is a third. The harness sets nothing else about the call — OMP owns
    credentials, routing, retries and cost — and it prices nothing: the dollars a row reports are the
    ``cost.total`` OMP recorded for each turn, summed here (probe-verified equal to the session's own
    ``get_session_stats.cost``), never re-derived from a price card.

    What it shows the model is fixed at construction, as before: ``specification`` every turn's message
    carries beside the goals, the few-shot examples and the loop's history. Which sections a session
    actually sent is recorded from use, so a run that took no refutation turn does not claim the
    refutation turn's sections.

    ``temperature`` and ``max_tokens`` are reported as ``None``: the harness does not set them any more,
    and the invocation that is run is recorded in the row's ``setup.omp`` rather than claimed here.
    Credentials and retries are OMP's, so ``provider_retries`` reads 0 — the port cannot observe OMP's
    internal retries, and a row must not invent a count it did not see.

    Failures are the loop's to record (plan D12): a turn OMP reports as errored — its own retries
    already exhausted — raises ``ProviderError`` with OMP's message and HTTP status, and the loop lands
    a ``provider_failure`` row.
    """

    def __init__(
        self,
        *,
        specification: str,
        selector: str = MODEL_SELECTOR,
        thinking: str = THINKING_LEVEL,
        examples: str | None = None,
        binary: str = OMP_BIN,
        timeout_s: float = TURN_TIMEOUT_S,
    ) -> None:
        self.specification = specification
        self.examples = prompt_examples() if examples is None else examples
        self.selector = selector
        self.thinking = thinking
        self.binary = binary
        self.timeout_s = timeout_s
        self._sessions: dict[str, OmpSession] = {}
        self._arms_used: set[str] = set()
        self._planned_arms: set[str] = set()
        self._input = 0
        self._output = 0
        self._cached_input = 0
        self._cost_usd = 0.0
        self._resolved_model: str | None = None
        self._is_fallback = False

    def propose(self, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str:
        """One tactic for the current goals (plan D14).

        The turn's message carries the specification, the examples, the goals and the history — every
        refused proposal with the REPL's reason, an empty reply with the loop's nudge. An empty reply
        comes back as an empty string for the loop to re-ask (plan D11).
        """
        self._arms_used.add("proof")
        return extract_tactic(
            self._turn("proof", user_message(self.specification, goals, history, examples=self.examples))
        )

    def refute(self, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str:
        """One Lean 4 command that would refute the statement under test (plan D16).

        The refutation arm's proposal step, under its own session and system prompt. Whether the
        command refutes anything is the *prover's* verdict, never this client's: the loop runs it
        through the prover's ``cmd`` channel and records a ``refuted`` outcome only for a command the
        prover accepted with nothing left to prove.
        """
        self._arms_used.add("refutation")
        return extract_tactic(
            self._turn(
                "refutation",
                user_message(self.specification, goals, history, arm="refutation", examples=self.examples),
            )
        )

    def plan(self, arm: str, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str:
        """The arm's plan, returned **verbatim** (plan D19).

        Asked once per arm before that arm acts, in the planning session's own framing: the slots to
        fill, the specification, the examples and the goals. The reply is the model's own text — the
        loop records it in the row unchanged — and an empty one comes back as an empty string for the
        loop to re-ask with the nudge (plan D11).
        """
        self._planned_arms.add(arm)
        return extract_plan(
            self._turn("plan", plan_message(self.specification, goals, history, examples=self.examples))
        )

    def usage(self) -> dict:
        """The run's cumulative usage as OMP recorded it, turn by turn (plan D20).

        Cumulative because the loop reads differences between calls for its per-arm accounting. Every
        number here is OMP's own record of a turn — ``message.usage``'s token counts and ``cost.total``
        — summed over the turns taken, so the dollars are the transport's accounting and not a
        re-derivation. This call does no I/O: the totals are accumulated as turns complete, which also
        means it cannot fail part-way through a run.
        """
        sections = [
            section for section in PROMPT_SECTIONS if section != "examples" or bool(self.examples)
        ]
        if "refutation" in self._arms_used:
            sections += list(REFUTATION_SECTIONS)
        if self._planned_arms:
            sections += list(PLAN_SECTIONS)
        return {
            "input": self._input,
            "output": self._output,
            "cached_input": self._cached_input,
            "cost_usd": round(self._cost_usd, 8),
            "cost_basis": self.cost_basis(),
            # OMP owns retries; the port cannot see them, so the row reports none rather than inventing
            # a count it never observed (plan D12/D20).
            "provider_retries": 0,
            "model": self.selector,
            "thinking": self.thinking,
            # Not set by the harness any more: OMP owns the call shape, and the row's `setup.omp` names
            # the invocation that was actually run.
            "temperature": None,
            "max_tokens": None,
            "resolved_model": self._resolved_model,
            "is_fallback": self._is_fallback,
            "prompt": {"sections": sections},
        }

    def cost_basis(self) -> str:
        """What the dollars are: OMP's own record, and the version that produced it (decision 7)."""
        return f"{omp_version(self.binary)} session usage.cost ({self.selector}, thinking {self.thinking})"

    def close(self) -> None:
        """Stop every session this run opened."""
        for session in list(self._sessions.values()):
            session.close()
        self._sessions.clear()

    def _session(self, role: str) -> OmpSession:
        """The role's session, started on first use (plan D20).

        One process per role: each arm's turns run with that arm's system prompt and none of the other
        arms' context, and a role that is never used costs nothing.
        """
        session = self._sessions.get(role)
        if session is None:
            session = OmpSession(
                SYSTEM_PROMPTS[role],
                selector=self.selector,
                thinking=self.thinking,
                binary=self.binary,
                timeout_s=self.timeout_s,
            )
            self._sessions[role] = session
        return session

    def _turn(self, role: str, message: str) -> str:
        """One model turn through the role's session, with OMP's usage record added to the totals."""
        turn = self._session(role).prompt(message, timeout=self.timeout_s)
        usage = turn.get("usage") or {}
        cost = usage.get("cost")
        if not isinstance(cost, dict) or "total" not in cost:
            # The dollars are the transport's to report (§11 decision 7): a turn whose record carries no
            # cost is a failure to report them, not a call that cost nothing.
            raise ProviderError(0, f"omp's turn carries no cost record: {json.dumps(usage)[:300]}")
        self._input += int(usage.get("input", 0))
        self._output += int(usage.get("output", 0))
        self._cached_input += int(usage.get("cacheRead", 0))
        self._cost_usd += float(cost["total"])
        served = turn.get("model")
        if served:
            self._resolved_model = served
            if served != self.selector:
                self._is_fallback = True
        return turn["text"] or ""
