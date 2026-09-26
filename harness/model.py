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
system prompt, the run's ``--model`` and ``--thinking``, the tool-access decision, the ``--no-*`` context
flags, and a **run-scoped ``--session-dir``**. That decision has two settings, and ``tools`` is it: the
default ``None`` gives ``--no-tools``, so the model must answer with a tactic, command or plan rather
than act as an agent, and a comma-separated ``tools`` string gives file mode (plan D26) — the session
gets ``--tools=<tools>`` and ``--approval-mode=yolo``, so the prover can edit its working copy and run
Lean itself — with ``tools=None`` reproducing the default mode byte for byte. OMP's own session
transcript is the run's per-turn record — the same records the
cost comes from, one format, inspectable live and afterwards — while the directory is ours, so nothing
of the user's store is touched or inherited. Each role's working directory is a clean temporary
directory *outside* the repository, because otherwise a session discovers the repository's ``AGENTS.md``
and the prompt stops being the one the row records (measured: 18 849 characters of repository context
without the flags). A turn is one ``prompt``; its usage is OMP's own ``message_end.message.usage``
record, summed as turns complete, and the client is network-bound and is **never** constructed by a
pytest scenario — the loop's scenarios use a scripted model.

What the model is shown is the client's whole business (plan D14): each turn's message carries the
specification the seed states, the few-shot examples, the current goals, and the tactics tried — every
refused proposal with the REPL's reason the loop recorded, every empty reply with the loop's nudge.
Nothing else reaches the prompt, so no invariant or helper-lemma statement can be shown without the
specification stating it, and the composition is reported per row rather than asserted here.
"""

from __future__ import annotations

import atexit
import hashlib
import json
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.closure import HistoryEntry, ProviderError, heartbeat  # noqa: E402

# The transport (plan D20). `omp --mode rpc` speaks newline-delimited JSON over stdio: commands in,
# frames out, with one `ready` frame at startup.
OMP_BIN = "omp"
OMP_ROLES = ("proof", "refutation", "plan")
# The flags every role's session starts with (plan D20), split around the one flag the run varies. The
# `--no-*` set is not decoration: without it a session picks up the repository's `AGENTS.md`, the
# discovered skills and rules, LSP and every extension, and the whole lot lands in the system prompt
# ahead of ours — 18 849 characters of it, measured — so the run's condition would be neither what the
# row records nor what the experiment claims. With them (and a working directory outside the repository,
# see `OmpModel._cwd`) the prompt is our text plus OMP's own 440-character project/environment footer,
# which the row records verbatim.
OMP_HEAD_FLAGS = ("--mode", "rpc", "--no-ui")
OMP_CONTEXT_FLAGS = ("--no-rules", "--no-skills", "--no-extensions", "--no-lsp")


def _tools_flags(tools: str | None) -> list[str]:
    """The tool-access decision, in exactly one place (plans D20/D26).

    ``None`` — the default, and what every caller that does not ask for file mode gets — gives
    ``--no-tools``: the model must answer with a tactic, a command or a plan, not act as an agent. A
    comma-separated ``tools`` string gives the session ``--tools=<tools>`` and ``--approval-mode=yolo``:
    a headless session has nobody to answer an approval prompt, so a prompt would be a stall, and D26
    item 5's sandbox is the working copy the harness hands the session rather than an approver.

    Both the command the transport runs (``omp_command``) and the flags a row records
    (``omp_invocation``) read this, so a session cannot run in one mode while the row claims the other.
    """
    if tools is None:
        return ["--no-tools"]
    return [f"--tools={tools}", "--approval-mode=yolo"]


# One turn's cap, in seconds. A legitimate turn is not a stall and a stall must not be invisible, and
# the two pull opposite ways:
#
# * Legitimate turns are long. The measured worst case on the real seed is 268 s (a `thinking high`
#   proof-arm turn); the setup's own direction — the planning turn, the technique examples, the
#   invitation to invent — is to make them longer, not shorter. A bound under that aborts a healthy run
#   and labels it `provider_failure`, which costs the whole run's budget.
# * A stalled turn is silence. With the old 900 s bound a wedged turn (OMP retrying a transient provider
#   failure internally) burned a quarter of the two-hour cap before the row said anything, and the first
#   fifteen minutes of it looked exactly like thinking.
#
# 360 s sits between them: it is four times the largest healthy turn observed other than the 268 s
# outlier (which keeps ~90 s of headroom), and it turns a stall into a recorded `provider_failure` in
# six minutes rather than fifteen. 300 s was the other candidate and is *nearly* right — but 32 s of
# headroom over the worst legitimate turn we have measured is not enough when the plan asks the model to
# think harder, and aborting a healthy turn is the more expensive mistake of the two.
TURN_TIMEOUT_S = 360.0
STARTUP_TIMEOUT_S = 120.0

# The prefix OMP's footer starts with (see `OMP_CONTEXT_FLAGS`): what a row records as the part of the
# system prompt that is not ours.
OMP_FOOTER_MARKER = "PROJECT"

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
    "Reply with the next tactic for the current goal, and nothing else: no explanation, no code fence, "
    "no prose. If you can see the complete proof, you may send it as `exact by <term>` — that is one "
    "tactic, applied whole; a proof sent as a bare sequence of tactics on separate lines loses every "
    "line but the first, so use `exact by` when the proof is ready. The tactic is applied to the goal "
    "the REPL reports; if it leaves further goals you are asked again with the new state. "
    "A name printed with a superscript dagger (\u271d), such as `a\u271d`, is Lean's display of an "
    "inaccessible hypothesis and cannot be written literally; rename it first with `rename_i` (or bind "
    "it in a `case`) before referring to it."
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
    "A refutation counts only when Lean accepts the command with nothing left to prove. "
    "If you can find no such witness — the expected answer when the statement under test is true — "
    "reply with exactly `no_witness` instead of a command, and your arm stops: this rig wants a "
    "counterexample, or nothing."
)

# The shape the refutation command must have (plan D16/D17): the negation of the statement under test,
# proved — the same wrap the harness itself uses (`¬ (…)`), so what the model writes and what Lean is
# handed are the same sentence. It is shown in the refutation turn's message and recorded in the row's
# setup, so a reader can see what the model was asked for and check the accepted command against it: the
# driver certifies from the response that Lean closed the command with no hole, never that the command
# states the goal's negation.
REFUTATION_TEMPLATE = "example : ¬ (<the statement under test>) := by\n  <a proof of its negation>"

REFUTATION_INSTRUCTION = (
    "This arm has one job: a counterexample to the statement under test, or nothing. Reply with "
    "exactly one Lean 4 command — an explicit witness that contradicts the statement, or a proof of "
    "its negation in the shape below. A proof of the statement itself is not a refutation and will be "
    "rejected: the harness wraps what you send in the negation, so Lean judges the refutation, not "
    "you. If you cannot find such a witness — which is the expected answer when the statement is "
    "true — reply with exactly `no_witness`, and this arm stops."
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

# File mode's system prompt (plan D26): the prover gets a shell and the file itself, rather than a REPL
# and one tactic per turn. It is a role prompt like the others — held here, so this module stays the one
# place the system prompts live — and the file-mode driver owns the messages its session is prompted
# with. The fixed part of the file (everything up to the theorem's ``:=``) is stated as fixed because
# D26 item 2a's integrity check enforces it: a file edited above the assignment is reported, not
# accepted, and the prompt says so before the model finds out. The naming traps at the end are Lean
# hygiene, not a hint: they name two syntax mistakes the host itself hit while doing the proof by hand
# (an ``induction ... with`` alternative's fixed pattern count, and an induction state shadowing an outer
# binder), and they name nothing about the statement under test.
FILE_MODE_SYSTEM_PROMPT = (
    "You are closing a Lean 4 theorem. The theorem and its surrounding definitions are written in a "
    "file in your working directory, with its proof left as `sorry`. You have a shell: edit the file and "
    "run Lean on it yourself until the proof is complete. "
    "The statement and every definition above it are fixed — the proof body is the only free part, and "
    "changing anything before the theorem's `:=` means the file no longer proves the theorem you were "
    "asked for. "
    "Available: `lake env lean <file>` (the package's Mathlib build is already in place) and any tools "
    "your shell has. Work only inside your working directory. "
    "Two traps worth avoiding, both about names rather than mathematics: an `induction ... with` "
    "alternative takes a fixed number of pattern names, so do not name the alternative's binders "
    "(`| step s t hs ih hst =>` fails where three are expected) - write `| step =>` and `rename_i` the "
    "ones you need; and an induction state can shadow an outer binder of the same name, so rename it "
    "immediately at the start of a case (`rename_i s'`) before writing anything that mentions the state. "
    "Reply with a short report of what you did and what Lean said, not with the proof text alone."
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


def negated_goal(goal: str) -> str:
    """A goal as the refutation arm must see it: the same target, negated (plan D16).

    A goal string is the repl's rendering, ``⊢ <target>``. The arm is asked for a witness against the
    *negation* of that target — the harness wraps whatever it proposes in ``¬ (…)`` before Lean judges
    it — so the prompt shows the negated form, parenthesised the way the wrap is, rather than inviting a
    proof of the statement the arm is supposed to refute.
    """
    target = goal.split("⊢", 1)[1].strip() if "⊢" in goal else goal.strip()
    return f"⊢ ¬ ({target})"


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
    one Lean 4 command that witnesses the **negation** of the statement under test (plan D16) — so the
    refutation turn shows the *negated* goal, states what the arm is for in one line, and says plainly
    that a proof of the statement is not a refutation. The material is otherwise the same either way, so
    a refutation is proposed under the same withholding as a proof (plan D14) — nothing but the
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
    if arm == "refutation":
        # The arm is asked for a witness against the *negation* (plan D16): showing the goal as stated
        # invited the model to prove it — the proof arm's job — at a 7× cost on a true statement.
        lines.extend(["", "The goal, negated — what a refutation must exhibit against:"])
        lines.extend(f"  {negated_goal(goal)}" for goal in goals)
    else:
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
        # The incremental default, with the whole-reply form available (plan D24, amended): a bare
        # sequence of tactics loses every line but the first in the repl's tactic channel, and a bare
        # `by …` is rejected there outright, so `exact by …` is the way to send a finished proof whole.
        lines.extend(["", "Reply with the next tactic — or `exact by <term>` if you can see the complete proof."])
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


def _unwrap_fence(text: str) -> str:
    """The body of a surrounding code fence, if the reply carries one (plan D24).

    Models fence their answers and write prose around them. The fence is syntax the repl would reject, so
    it comes off; prose *outside* the fence comes off with it, while everything between the fences is
    kept verbatim — the whole reply, not its first line.
    """
    if "```" not in text:
        return text
    body = text.split("```", 1)[1]
    if "```" in body:
        body = body.split("```", 1)[0]
    lines = body.split("\n")
    if lines and lines[0].strip().lower() in ("lean", "lean4"):
        body = "\n".join(lines[1:])
    return body.strip()


def extract_tactic(content: str) -> str:
    """The tactic to apply out of a model reply, unwrapping a code fence if the model used one.

    The reply is otherwise applied verbatim — a tactic may span lines — because a fence is syntax the
    repl would reject, while an unhelpful reply should reach the prover as the model wrote it.

    One normalisation (plan D24 option 2): a *bare* ``by …`` block — what a model writes when it has the
    whole proof, and the reply this policy exists to apply — is not a standalone tactic in the repl's
    tactic channel (measured: ``expected tactic``), so it is wrapped as ``exact by …``. That is the same
    syntactic normalisation as the refutation arm's negation wrap and it changes no meaning; a reply that
    already names a tactic (``exact by …``) or begins with a tactic whose name starts with ``by``
    (``by_cases h : p``) is passed through untouched.
    """
    text = _unwrap_fence(content.strip())
    if re.match(r"by(\s|$)", text):
        text = f"exact {text}"
    return text


def extract_command(content: str) -> str:
    """The command to run out of a refutation-arm reply (plan D16).

    The fence comes off; nothing else does. This arm is asked for one Lean *command* — a witness, or the
    ``no_witness`` sentinel — and its instruction is deliberately unchanged by plan D24 option 2, so
    nothing here may rewrite what it said: no ``exact`` normalisation, no rewriting of a reply that
    happens to begin with ``by``.
    """
    return _unwrap_fence(content.strip())




# The system prompt each role's session is started with (plan D16/D19/D20/D26): the transport passes it
# as `--system-prompt`, so every arm's turns run under its own framing rather than a shared one. `file`
# is file mode's one session (D26); it is not in `OMP_ROLES`, which lists the roles a tactic run opens,
# because a run takes one configuration or the other.
SYSTEM_PROMPTS = {
    "proof": SYSTEM_PROMPT,
    "refutation": REFUTATION_SYSTEM_PROMPT,
    "plan": PLAN_SYSTEM_PROMPT,
    "file": FILE_MODE_SYSTEM_PROMPT,
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


def role_session_dir(session_root: Path | str, role: str) -> Path:
    """The directory one role's session writes to, canonical (finding P2).

    The single definition of the path: the directory the port creates and the ``--session-dir`` it hands
    OMP are the same resolved path by construction, not by two expressions that happen to agree. It must
    be absolute, because OMP resolves a relative one against the session's ``--cwd`` (see
    :func:`omp_command`).
    """
    return (Path(session_root) / role).resolve()


def omp_command(
    *,
    session_root: Path | str,
    role: str,
    cwd: Path | str | None = None,
    system_prompt: str | None = None,
    tools: str | None = None,
    selector: str = MODEL_SELECTOR,
    thinking: str = THINKING_LEVEL,
    binary: str = OMP_BIN,
) -> list[str]:
    """The exact command one role's RPC session is started with (plan D20).

    The one place the flags are written, so what the transport runs and what a row's ``setup`` records
    cannot drift apart: RPC over stdio, headless, **no repository context** (``--no-rules``,
    ``--no-skills``, ``--no-extensions``, ``--no-lsp``), the fixed selector and thinking level, and this
    role's system prompt. ``tools`` is the one decision that varies (plan D26) and :func:`_tools_flags`
    makes it: ``None`` gives ``--no-tools`` — the model must answer with a tactic, a command or a plan,
    not act as an agent — and a comma-separated string gives file mode, where the session gets those
    tools and ``--approval-mode=yolo``.

    Two paths matter as much as the flags. The session directory — ``<session_root>/<role>`` — is
    run-scoped and *persisted*: OMP's own session transcript is the run's per-turn record, and it touches
    nothing of the user's store, because the directory is ours. **It is passed absolute**, because OMP
    resolves a relative ``--session-dir`` against the session's ``--cwd`` — the clean temporary directory
    below — so a relative one silently puts the transcript beside that directory instead of in the run
    (measured: ``/tmp/nix-shell.*/omp-cwd-*/<the relative path>``, deleted with the shell). ``cwd`` is a
    clean directory *outside* the repository, because context discovery walks up from it: from the
    repository, a session picks up ``AGENTS.md`` and puts it in the system prompt, and from any directory
    inside the repository tree it still does (both measured).
    """
    command = [binary, *OMP_HEAD_FLAGS, *_tools_flags(tools), *OMP_CONTEXT_FLAGS]
    if cwd is not None:
        # A full session always names one: without it OMP starts in the caller's cwd, which is the
        # repository when a run is launched from it, and the session's context discovery then puts
        # `AGENTS.md` in the system prompt (measured). `None` leaves the flag out for a caller that
        # wants the flag list, not a session.
        command += ["--cwd", str(cwd)]
    command += [
        "--session-dir",
        str(role_session_dir(session_root, role)),
        "--model",
        selector,
        "--thinking",
        thinking,
    ]
    if system_prompt is not None:
        # `None` omits the flag rather than sending an empty prompt: a session is only ever started for
        # a role, and every role has a prompt (this module's `SYSTEM_PROMPTS`), so the default is for a
        # caller that wants the flag list and not a session.
        command += ["--system-prompt", system_prompt]
    return command


def omp_invocation(
    *,
    selector: str = MODEL_SELECTOR,
    thinking: str = THINKING_LEVEL,
    tools: str | None = None,
    binary: str = OMP_BIN,
    turn_deadline_s: float = TURN_TIMEOUT_S,
    startup_deadline_s: float = STARTUP_TIMEOUT_S,
) -> dict:
    """The invocation a row's ``setup`` records (plans D17/D20).

    The version, the binary, the roles a run opens, and the flags each session starts with. Two values
    are *named* rather than inlined, because they are per-run and per-role: the session directory (the
    row records the real one in ``artifacts``) and the role's system prompt (a long constant in this
    module). Everything else a reader needs to reproduce the call is here verbatim, including the
    tool-access decision of ``tools`` (plan D26): a file-mode row records ``--tools=<tools>`` and
    ``--approval-mode=yolo``, a default row records ``--no-tools``, and each is the same
    :func:`_tools_flags` the command was built with — so the flags cannot claim a mode the session did
    not run in.
    """
    return {
        "version": omp_version(binary),
        "binary": binary,
        "roles": list(OMP_ROLES),
        # The bounds the run itself ran under (plan D24): a stalled turn is cut at `turn_deadline_s` and
        # recorded as a provider failure, so a row that ends that way states the deadline it was cut at
        # instead of leaving a reader to guess whether the model was thinking or wedged.
        "turn_deadline_s": turn_deadline_s,
        "startup_deadline_s": startup_deadline_s,
        "flags": [
            *OMP_HEAD_FLAGS,
            *_tools_flags(tools),
            *OMP_CONTEXT_FLAGS,
            "--cwd",
            "<a clean temporary directory outside the repository>",
            "--session-dir",
            "<the run's session directory>/<role>",
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
        session_root: Path | str,
        cwd: Path | str,
        role: str,
        tools: str | None = None,
        selector: str = MODEL_SELECTOR,
        thinking: str = THINKING_LEVEL,
        binary: str = OMP_BIN,
        timeout_s: float = TURN_TIMEOUT_S,
        startup_timeout_s: float = STARTUP_TIMEOUT_S,
    ) -> None:
        # The canonical role directory (finding P2): the same call `omp_command` makes for
        # `--session-dir`, so the path created here and the path OMP is handed cannot drift.
        self.session_root = Path(session_root).resolve()
        self.session_dir = role_session_dir(self.session_root, role)
        self.session_dir.mkdir(parents=True, exist_ok=True)
        # Which turn this session takes (plan D16): proof, refutation or planning. It is what a
        # deadline failure names, so a row says *which* turn stalled and under what bound rather than
        # leaving a reader to infer it from a prompt id.
        self.role = role
        self.turn_deadline_s = timeout_s
        self.cmd = omp_command(
            system_prompt=system_prompt,
            session_root=self.session_root,
            role=role,
            cwd=cwd,
            tools=tools,
            selector=selector,
            thinking=thinking,
            binary=binary,
        )
        self.timeout_s = timeout_s
        self._counter = 0
        self._turns = 0  # turns this session has taken, for the heartbeat's numbering (plan D24)
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
        self._turns += 1
        turn = self._turns
        bound = self.timeout_s if timeout is None else timeout
        deadline = time.monotonic() + bound
        # The heartbeat (plan D24): one line when the turn is sent, one when it comes back. A wedged
        # turn is then a `sent` line with no `ended` line, which is the thing the session transcripts
        # cannot show, since they only ever hold finished turns.
        heartbeat(f"sent {self.role} turn {turn} (deadline {bound:g}s)")
        started = time.monotonic()
        self._write({"id": request_id, "type": "prompt", "message": message})
        frames: list[dict] = []
        try:
            while True:
                frame = self._read(deadline, f"its reply to {request_id}")
                frames.append(frame)
                if frame.get("type") == "prompt_result" and frame.get("id") == request_id:
                    self._check_result(frame)
                    break
        except ProviderError as failure:
            # A short reason on the heartbeat (the full message is in the row, which is the record): the
            # first clause names what happened — a deadline cut says so in its first six words.
            reason = failure.message.splitlines()[0].split(":", 1)[0]
            heartbeat(
                f"<- {self.role} turn {turn} ended (failed: {reason}, {time.monotonic() - started:.1f}s)"
            )
            raise
        heartbeat(f"<- {self.role} turn {turn} ended (completed, {time.monotonic() - started:.1f}s)")
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

    def _deadline_message(self, describing: str, timeout: float) -> str:
        """What the row says about a turn that did not finish in time (plan D24).

        Named precisely: the role whose turn it was, what the session was waiting for, and the bound —
        and it stays a `ProviderError`, so the loop records it in D12's shape (`provider_failure`) and
        the run's spent turns, tokens and dollars survive in the row. The alternative reading of a long
        silence — a model that is merely thinking — is what the recorded bound lets a reader separate
        from a stall: a healthy turn of the largest prompt we send has been measured at 5–40 s, with one
        268 s outlier on the real seed.
        """
        return (
            f"the {self.role} turn did not finish within {timeout:g}s ({describing}): the model call was "
            "cut at its deadline, which is a recorded provider failure rather than a run that hangs"
            f"{self._stderr_tail()}"
        )

    def _read(self, deadline: float, describing: str) -> dict:
        """One frame from stdout, bounded by ``deadline``.

        A turn that blows its deadline is a *recorded* failure, not a run that hangs: the message names
        the turn (its role and the command it was answering) and the bound it ran under, so the row the
        loop lands says which turn stalled and against what — the difference between a row a reader can
        act on and a silence that has to be diagnosed from process tables (plan D24).
        """
        remaining = deadline - time.monotonic()
        timeout = self.turn_deadline_s
        if remaining <= 0:
            self.close()
            raise ProviderError(0, self._deadline_message(describing, timeout))
        try:
            line = self._lines.get(timeout=remaining)
        except queue.Empty:
            self.close()
            raise ProviderError(0, self._deadline_message(describing, timeout)) from None
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


class _UsageTotals:
    """OMP's own usage record, summed turn by turn for a row (plan D20).

    Every number is the transport's: ``message.usage``'s token counts and ``cost.total``, added as turns
    complete rather than re-derived from a price card. Both the tactic port and file mode's session
    accumulate here, so the two cannot disagree about what a turn cost, and a turn whose record carries
    no cost is raised as the failure to report it that it is — never counted as a free call.
    """

    def __init__(self) -> None:
        self.input = 0
        self.output = 0
        self.cached_input = 0
        self.cost_usd = 0.0
        # The last model OMP reported serving, and whether any turn was served by one other than the
        # selector. The fallback flag is sticky: a run that fell back and later came back did not stay
        # on the selector, so it is not reported as if it had.
        self.resolved_model: str | None = None
        self.is_fallback = False

    def add(self, turn: dict, *, selector: str) -> None:
        """Add one turn's OMP-reported usage to the totals."""
        usage = turn.get("usage") or {}
        cost = usage.get("cost")
        if not isinstance(cost, dict) or "total" not in cost:
            # The dollars are the transport's to report (§11 decision 7): a turn whose record carries no
            # cost is a failure to report them, not a call that cost nothing.
            raise ProviderError(0, f"omp's turn carries no cost record: {json.dumps(usage)[:300]}")
        self.input += int(usage.get("input", 0))
        self.output += int(usage.get("output", 0))
        self.cached_input += int(usage.get("cacheRead", 0))
        self.cost_usd += float(cost["total"])
        served = turn.get("model")
        if served:
            self.resolved_model = served
            if served != selector:
                self.is_fallback = True


def _cost_basis(binary: str, selector: str, thinking: str) -> str:
    """What the dollars are: OMP's own record, and the version that produced it (decision 7)."""
    return f"{omp_version(binary)} session usage.cost ({selector}, thinking {thinking})"


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

    ``tools`` is the transport's tool-access decision (plan D26) and is passed to every session this
    port opens. It defaults to ``None``, which is ``--no-tools``: a tactic run's command is then exactly
    what it was before file mode existed. A tool-using session is file mode's own port,
    :class:`OmpFileModel`.
    """

    def __init__(
        self,
        *,
        specification: str,
        tools: str | None = None,
        selector: str = MODEL_SELECTOR,
        thinking: str = THINKING_LEVEL,
        examples: str | None = None,
        binary: str = OMP_BIN,
        timeout_s: float = TURN_TIMEOUT_S,
        session_root: Path | str | None = None,
    ) -> None:
        self.specification = specification
        self.tools = tools
        self.examples = prompt_examples() if examples is None else examples
        self.selector = selector
        self.thinking = thinking
        self.binary = binary
        self.timeout_s = timeout_s
        # The run-scoped session directory each role's transcript lives in (plan D17/D20). A caller
        # that names one — `harness.route_b` names `results/omp/<run>/` — gets a record a reader can
        # find; a standalone caller gets a temporary one, so nothing is written into the repository by
        # accident. Either way it is *ours*: the user's session store is never touched or inherited.
        # Absolute, always: OMP resolves ``--session-dir`` against the session's ``--cwd`` (a clean
        # temporary directory of ours, not the process's), so a relative root silently puts every
        # transcript beside that temp directory instead of the run's — where a nix-shell's exit deletes
        # it. `route_b` passes ``results/omp/<run>`` and a direct invocation often passes it relatively,
        # so the resolution has to happen here (measured: the file landed under
        # ``/tmp/nix-shell.*/omp-cwd-*/results/omp/...`` and vanished with the shell).
        self.session_root = (
            Path(session_root).resolve()
            if session_root is not None
            else Path(tempfile.mkdtemp(prefix="omp-sessions-"))
        )
        self._owns_session_root = session_root is None
        # The session's working directory: a clean temporary directory *outside* the repository, because
        # context discovery walks up from it and would otherwise put `AGENTS.md` in the system prompt
        # (measured — see `omp_command`). Created on the first session and removed on close.
        self._cwd: Path | None = None
        self._sessions: dict[str, OmpSession] = {}
        self._arms_used: set[str] = set()
        self._planned_arms: set[str] = set()
        self._usage = _UsageTotals()

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
        return extract_command(
            self._turn(
                "refutation",
                user_message(self.specification, goals, history, arm="refutation", examples=self.examples),
            )
        )

    def plan(self, arm: str, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str:
        """The arm's plan, returned **verbatim** (plan D19).

        Asked once per run, for the proof arm — the only arm that plans (the refutation arm goes straight
        to its command; `harness.closure.PLANNING_ARMS` is the list) — in the planning session's own
        framing: the slots to fill, the specification, the examples and the goals. The reply is the
        model's own text — the loop records it in the row unchanged — and an empty one comes back as an
        empty string for the loop to re-ask with the nudge (plan D11).
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
            "input": self._usage.input,
            "output": self._usage.output,
            "cached_input": self._usage.cached_input,
            "cost_usd": round(self._usage.cost_usd, 8),
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
            "resolved_model": self._usage.resolved_model,
            "is_fallback": self._usage.is_fallback,
            "prompt": {"sections": sections},
        }

    def cost_basis(self) -> str:
        """What the dollars are: OMP's own record, and the version that produced it (decision 7)."""
        return _cost_basis(self.binary, self.selector, self.thinking)

    def close(self) -> None:
        """Stop every session this run opened, and clean up what this client created itself."""
        for session in list(self._sessions.values()):
            session.close()
        self._sessions.clear()
        if self._cwd is not None:
            shutil.rmtree(self._cwd, ignore_errors=True)
            self._cwd = None
        if self._owns_session_root:
            shutil.rmtree(self.session_root, ignore_errors=True)

    def identity(self) -> dict:
        """Each open role's session identity and prompt, as a row records it (plans D17/D20).

        Per role: where its transcript lives, the session id and file OMP assigned, the model and
        thinking level OMP reports, and the system prompt it **actually ran with** — digested, and with
        the part beyond ours quoted verbatim. That last field is the point: the row then shows the
        condition the model was under, not the one the harness intended, and a change in OMP's own
        footer shows up as a change in the row rather than as an unexplained difference between runs.
        """
        recorded: dict = {}
        for role, session in sorted(self._sessions.items()):
            state = session.get_state()
            prompt = "\n".join(state.get("systemPrompt") or [])
            ours = SYSTEM_PROMPTS[role]
            recorded[role] = {
                "session_dir": session.session_dir.name,
                "session_id": state.get("sessionId"),
                "session_file": Path(state["sessionFile"]).name if state.get("sessionFile") else None,
                "model": (state.get("model") or {}).get("id"),
                "thinking_level": state.get("thinkingLevel"),
                "system_prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                "prompt_beyond_ours": prompt[len(ours):].strip() if prompt.startswith(ours) else prompt,
            }
        return recorded

    def _session(self, role: str) -> OmpSession:
        """The role's session, started on first use (plan D20).

        One process per role: each arm's turns run with that arm's system prompt and none of the other
        arms' context, and a role that is never used costs nothing. Each role gets its own directory
        under the run's session root, so one transcript per role is one file to read.
        """
        session = self._sessions.get(role)
        if session is None:
            if self._cwd is None:
                # Deliberately not inside the repository: see `omp_command`.
                self._cwd = Path(tempfile.mkdtemp(prefix="omp-cwd-"))
            session = OmpSession(
                SYSTEM_PROMPTS[role],
                role=role,
                session_root=self.session_root,
                cwd=self._cwd,
                tools=self.tools,
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
        self._usage.add(turn, selector=self.selector)
        return turn["text"] or ""


class OmpFileModel:
    """File mode's model port: one tool-using OMP session the driver prompts (plan D26).

    D26's unit of work is the file, not a tactic: the prover is handed a working copy holding the seed
    theorem with its proof left as ``sorry``, and is given a shell to close it itself. This port is that
    session and nothing more — one ``omp --mode rpc`` process, started under ``<session_root>/file`` with
    ``FILE_MODE_SYSTEM_PROMPT``, the driver's ``cwd``, and ``tools`` — while the driver owns the messages,
    the file edits, the closure oracle and the row. ``tools`` defaults to ``bash``, which is what the mode
    needs: the session edits the file and runs ``lake env lean`` on it.

    One session, not one per arm: file mode has no arms. It is opened on the first :meth:`attempt`, so a
    driver that never prompts it starts no process, and :meth:`close` is what stops it.
    """

    def __init__(
        self,
        *,
        specification: str,
        session_root: Path | str,
        cwd: Path | str,
        examples: str | None = None,
        tools: str = "bash",
        selector: str = MODEL_SELECTOR,
        thinking: str = THINKING_LEVEL,
        binary: str = OMP_BIN,
        timeout_s: float = TURN_TIMEOUT_S,
        startup_timeout_s: float = STARTUP_TIMEOUT_S,
    ) -> None:
        self.specification = specification
        self.examples = prompt_examples() if examples is None else examples
        self.tools = tools
        self.selector = selector
        self.thinking = thinking
        self.binary = binary
        self.timeout_s = timeout_s
        self.startup_timeout_s = startup_timeout_s
        # The session root is the run's, resolved exactly as `OmpModel` resolves it: `--session-dir` must
        # be absolute (see `omp_command`), and the transcript belongs in the run rather than beside the
        # session's working directory.
        self.session_root = Path(session_root).resolve()
        # The working copy the session acts on. Deliberately *not* created here: the driver owns the
        # scratch directory and what is in it — the seed file — and making it behind the driver's back
        # would hide a caller that handed over a path it never made.
        self.cwd = Path(cwd).resolve()
        self._usage = _UsageTotals()
        self._session_obj: OmpSession | None = None

    def attempt(self, message: str) -> dict:
        """Prompt the session once and return the turn: text, model, provider and usage.

        One turn of file mode. The driver writes the message — the seed file, the goal, the previous
        attempt's Lean output — and this port carries it to the session and back. A provider failure
        raises ``ProviderError`` exactly as the tactic path does, a turn cut at its deadline included, so
        the driver records it under D12 rather than seeing a silence.
        """
        turn = self._session().prompt(message, timeout=self.timeout_s)
        self._usage.add(turn, selector=self.selector)
        return turn

    def usage(self) -> dict:
        """The session's cumulative usage, in the shape the tactic port's rows carry (plan D20).

        The same keys ``OmpModel.usage()`` returns, so a file-mode row copies them unchanged. ``prompt``
        carries no sections: file mode's message is the driver's to assemble and to record, and this port
        composes none of it.
        """
        return {
            "input": self._usage.input,
            "output": self._usage.output,
            "cached_input": self._usage.cached_input,
            "cost_usd": round(self._usage.cost_usd, 8),
            "cost_basis": self.cost_basis(),
            # OMP owns retries; the port cannot see them (plan D12/D20).
            "provider_retries": 0,
            "model": self.selector,
            "thinking": self.thinking,
            # Not set by the harness: OMP owns the call shape, and the row's `setup.omp` names the
            # invocation that was run.
            "temperature": None,
            "max_tokens": None,
            "resolved_model": self._usage.resolved_model,
            "is_fallback": self._usage.is_fallback,
            "prompt": {"sections": []},
        }

    def cost_basis(self) -> str:
        """What the dollars are: OMP's own record, and the version that produced it (decision 7)."""
        return _cost_basis(self.binary, self.selector, self.thinking)

    def close(self) -> None:
        """Stop the session, if it was ever opened."""
        if self._session_obj is not None:
            self._session_obj.close()
            self._session_obj = None

    def _session(self) -> OmpSession:
        """The one session, started on first use (plan D26)."""
        if self._session_obj is None:
            self._session_obj = OmpSession(
                FILE_MODE_SYSTEM_PROMPT,
                role="file",
                session_root=self.session_root,
                cwd=self.cwd,
                tools=self.tools,
                selector=self.selector,
                thinking=self.thinking,
                binary=self.binary,
                timeout_s=self.timeout_s,
                startup_timeout_s=self.startup_timeout_s,
            )
        return self._session_obj
