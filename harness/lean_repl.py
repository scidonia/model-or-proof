"""Route B: the Lean prover driver — the ``Prover`` port over the ``lean-repl`` JSON protocol (D2).

``LeanReplProver`` speaks to the ``repl`` executable from ``leanprover-community/repl`` over a
subprocess's stdin/stdout, one JSON command per line and one JSON response per command, in the shape
the plan fixes (``{"tactic", "proofState"}`` in, ``{"proofState", "goals"}`` out). It mirrors
``harness.tlc_run``'s subprocess handling — its own process group, a bounded wait, a kill-tree
teardown — because a hung prover must not hang a run.

The statement is the human's and the tactics are the loop's (protocol §11 decision 5), so the driver
writes no tactic of its own: it loads the seed artifact (the statement under test, with one ``sorry``
where the proof goes), reports the goal state at that ``sorry`` to the loop, applies whatever tactic
the loop hands back to the goal the repl reports, and writes the accepted script back into the
artifact. An artifact the driver wrote is therefore the seed with its ``sorry`` replaced.

The seed is loaded in **two payloads**, threading the repl's ``env`` (``split_seed``): the prelude with
no ``env`` — a fresh environment is the only one ``import`` is allowed in — and then the goal
declaration with the prelude's ``env``, so the proof state opens over the declarations the goal is
stated in. Loading a whole file as one payload leaves the goal stated in constants its own tactic
environment cannot resolve, and then no tactic can ever make progress.

Closure and failure, in protocol §8's terms:

* the proof is closed only when the repl reports an empty goal list **and** a proof status beginning
  ``Completed`` (plan D6). A goal "closed" by ``sorry`` reports an empty goal list too, with
  ``Incomplete: contains sorry``; the driver refuses it and leaves the state where it was, so the loop
  cannot record a success that ``count_unclosed`` would have to catch afterwards.
* a tactic that does not elaborate changes nothing: the goal state stays, the next turn sees the same
  goals, and the failure is named in ``failures`` rather than being a silent no-op.
* every refusal is named in ``failures``, which the loop reads into the row: a run that timed out
  after a string of rejected proposals then says what the prover refused, instead of leaving the row
  undiagnosable.

A run of a mutant (a statement that is false) never writes its artifact: ``mutant=True`` refuses the
write, because a run that closed a false statement has a broken rig (protocol §5) and the tree must
keep the honest seed rather than a false "proof" spliced into it (plan D7).

No test spawns a real repl. ``count_unclosed`` is a pure function over strings, ``split_seed`` is a
pure function over seed text, and the driver's channels are exercised through a **scripted responder**
that stands in for the repl (``responder=``, tests/lean-driver-contract.md): it answers the load, the
goal-state channel and the command channel without Lean, and a seed file given to it is split exactly
as the real path splits one. ``harness.closure``'s stubs cover the loop.
"""

from __future__ import annotations

import atexit
import json
import os
import queue
import signal
import subprocess
import sys
import threading
from pathlib import Path
from typing import Callable, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.closure import (  # noqa: E402
    Failure,
    ProverError,
    SeedAlreadyClosedError,
    declaration_matches,
)
from harness.lean_lex import count_holes, is_identifier_char, skip_noncode  # noqa: E402

# `repl` holds the goal state in memory and the loop drives it turn by turn, so a step that hangs
# would hang the run rather than bind a budget; these bounds turn that into a named failure. Loading
# the seed is the slow one (the seed's imports; a cold Mathlib olean load is tens of seconds), while a
# step is generous because a single Mathlib tactic can legitimately run for minutes.
START_TIMEOUT_S = 1800.0
STEP_TIMEOUT_S = 600.0

# How the repl is started from inside the seed's project. The `repl` package itself has no
# dependencies (`lakefile.toml` requires nothing), so its binary finds only core Lean; the seed's
# imports resolve through the project's environment, which is what `lake env` sets up (the repl's own
# README: "Using the REPL from another project").
LAKE_ENV = ("lake", "env")

# Protocol §8, plan D6: an artifact carrying any of these is not a closed proof. `admit` is the same
# hole as `sorry` under another name; `sorryAx` is what a `sorry` term elaborates to. They are matched
# as whole identifiers by `count_unclosed` rather than by a regex over the raw text: a regex cannot
# tell whether it is reading code, and the seed's own prose explains the placeholder it sits next to.
# Lean's synthetic `?name` is a sixth spelling, matched by `harness.lean_lex`'s synthetic-hole scan; it
# is not in this set, because it is a `?` followed by a name rather than one identifier.
UNCLOSED_TOKENS = frozenset({"sorry", "sorryAx", "admit", "Admitted", "axiom"})

# What runs ahead of every command on the refutation channel (plan D16). Lean's autoImplicit binds a
# name the seed does not declare as a *fresh variable*, so a statement written with a typo can be
# vacuously true and still answer with no errors and no holes — accepted as a machine-checked witness.
# With the option off, a wrong name is an error, i.e. a rejection carrying Lean's reason, so the arm
# stays falsifiable both ways. The option is set in the same payload, ahead of the command, so it
# applies to it, and it persists in the session state, so commands continuing from that state keep it.
# The load's own payloads come first and are untouched: the seed elaborates the way its file intends.
# The verdict's `witness` stays the caller's command, which is what is being judged.
AUTOIMPLICIT_OFF = "set_option autoImplicit false"

# What `unclosed()` counts when the repl's answer is not a proof and names no goal to work on: a
# response without a readable goal list, or an empty one the close-guard refused. It is not a Lean
# goal — it is the driver keeping the run open, so a response that is not a proof can never read as
# closure; `failures` carries the reason.
NOT_CLOSED_GOAL = "⊢ <the repl did not report a closed proof>"


class LeanReplError(ProverError):
    """The driver could not speak to the repl, or the repl answered outside the protocol.

    It is the ``ProverError`` the loop's port names, so ``run_loop`` records a mid-run driver failure
    as an ``error`` row — the turns, tokens and dollars spent so far, the partial artifact kept —
    instead of letting the traceback lose the row (``harness.closure``).
    """


def _goals_of(response: object) -> list[str]:
    """The goal strings a lean-repl response carries, in order.

    A response without a well-formed ``goals`` list is a protocol violation, not an empty proof: the
    two must never be confused, because ``[]`` is the loop's only evidence of closure (§8).
    """
    goals = response.get("goals") if isinstance(response, dict) else None
    if not isinstance(goals, list):
        raise LeanReplError(f"lean-repl response carries no goals list: {response!r}")
    for goal in goals:
        if not isinstance(goal, str):
            raise LeanReplError(f"lean-repl goal is not a string: {goal!r}")
    return list(goals)


def _status_of(response: dict) -> str | None:
    """The repl's own verdict on the state, when it stated one the driver can read (finding P1.2).

    ``proofStatus`` is Lean's judgment when the repl sends a string the driver recognises —
    ``Completed``, or an ``Incomplete: …`` naming what is left. A missing key, or a value that is not a
    readable status, is *not* a judgment: nothing in such a response shows Lean considered the step, so
    recording it as a Lean refusal would blame the model for the rig's inability to read the answer.
    """
    status = response.get("proofStatus")
    if isinstance(status, str) and status.startswith(("Completed", "Incomplete")):
        return status
    return None


def _closed_by(response: dict) -> bool:
    """Whether a response is the repl's word that the proof is closed (protocol §8, plan D6).

    Only a present, empty ``goals`` list together with a ``proofStatus`` beginning ``Completed`` is
    closure. A missing ``goals`` list is not an empty one — ``[]`` is the loop's only evidence of
    closure, so a response the driver could not read must never supply it — and ``goals: []`` with
    ``Incomplete: contains sorry`` is the repl saying the proof still rests on a hole.
    """
    goals = response.get("goals")
    if not isinstance(goals, list) or goals:
        return False
    status = response.get("proofStatus")
    return isinstance(status, str) and status.startswith("Completed")


def count_unclosed(artifact_text: str) -> int:
    """How many unclosed-proof tokens a Lean artifact carries (protocol §8, plan D6).

    Only code counts. ``harness.lean_lex`` skips Lean's comments (``--`` to end of line, ``/- … -/``
    with nesting), string literals, character literals and ``« … »`` quoted identifiers, so a ``sorry``
    in the seed's own prose or in a prover error message does not refuse a genuinely closed proof and
    lose its row — while every spelling that really is a hole (``sorry``, ``sorryAx``, ``admit``,
    ``Admitted``, ``axiom``, and Lean's synthetic ``?name``) still counts.

    A ``sorry`` inside a string *interpolation* (``s!"{sorry}"``) reads as string text and is missed
    here; the driver's close-guard covers that spelling, because the repl reports a proof containing
    ``sorry`` as ``Incomplete`` however the term is written (D6).
    """
    return count_holes(artifact_text, UNCLOSED_TOKENS)


def _goal_payload_start(seed_text: str, goal_start: int) -> int:
    """Where the goal's payload begins: the declaration, with the comments attached above it.

    ``/--`` is a *doc* comment — its own syntactic category, not whitespace (reference manual §5.2.2) —
    so the comment block sitting directly above the goal travels with it: left at the end of the
    prelude, it would be a doc comment attached to nothing. A plain comment would be harmless in either
    payload and costs nothing to carry along; the whitespace between the two declarations stays behind,
    where it means nothing.
    """
    spans: list[tuple[int, int]] = []
    index = 0
    while index < goal_start:
        skipped = skip_noncode(seed_text, index)
        if skipped is not None and skipped > index:
            spans.append((index, skipped))
            index = skipped
        else:
            index += 1
    # Walk back over the comments that reach the declaration with nothing but whitespace between them.
    boundary = goal_start
    for start, end in reversed(spans):
        if seed_text[end:boundary].strip():
            break
        boundary = start
    return boundary


def _starts_scope_close(seed_text: str, index: int) -> bool:
    """Whether a top-level ``end …`` statement begins at ``index``.

    ``end`` is a command, and a seed writes it as the first token of its own line; a spelling inside a
    longer identifier (``append``) is not one.
    """
    if not seed_text.startswith("end", index):
        return False
    if index and is_identifier_char(seed_text[index - 1]):
        return False
    after = seed_text[index + 3 : index + 4]
    if after and is_identifier_char(after):
        return False
    return not seed_text[seed_text.rfind("\n", 0, index) + 1 : index].strip()


def _goal_payload_end(seed_text: str, payload_start: int) -> int:
    """Where the goal's payload ends: before the file's trailing ``end …`` statements.

    A seed ends with the closes of the scopes its declarations sit in (``end TokenRing``). They are
    not part of the goal declaration, and carrying them in the same payload runs them: they close the
    namespace the goal is stated in, so every later command would run at the root namespace, where the
    seed's own names are not in scope. Lean's ``autoImplicit`` then does not even fail — it binds the
    names as fresh variables and *accepts* a statement written with them — so the payload must end at
    the first scope-closing statement. The artifact still carries the closes: only the payload is
    trimmed.
    """
    index = payload_start
    while index < len(seed_text):
        skipped = skip_noncode(seed_text, index)
        if skipped is not None and skipped > index:
            index = skipped
            continue
        if _starts_scope_close(seed_text, index):
            return seed_text.rfind("\n", payload_start, index) + 1
        index += 1
    return len(seed_text)


def split_seed(seed_text: str) -> tuple[str, str]:
    """The seed as two payloads: everything before the goal declaration, and that declaration itself.

    The repl runs a ``cmd`` in the environment of an ``env`` a previous response returned, and creates
    a fresh environment when it is absent; with ``env`` it continues from the previous command
    snapshot's whole state, so namespaces, options and ``open``s come along
    (``tools/repl/REPL/Main.lean``, ``runCommand``: ``IO.processInput s.cmd initialCmdState?``). Loading
    a whole file as one payload therefore leaves the proof state's environment *without* the file's own
    declarations: the goal is stated in them (``TokenRing.Mutex N s``) while the tactic environment
    cannot resolve them, and no tactic can make progress. Two payloads fix that — the prelude with no
    ``env`` (a fresh environment is the only one ``import`` is allowed in), then the goal declaration
    with the prelude's ``env`` — and the proof state then opens over the declarations it is stated in.

    The goal is the seed's **last** declaration (plan D5/D15: a seed carries exactly one statement, one
    ``sorry`` and nothing after it). A seed with no declaration, or whose last declaration does not
    carry exactly one hole, raises rather than producing a state the run would measure wrongly: a broken
    split must not look like a model that cannot make progress.

    The positions the repl reports for the goal — the ``sorries`` entry's ``pos``/``endPos`` — are
    relative to the payload it ran, so a caller locating the ``sorry`` in the file must locate it in
    ``goal`` and shift by ``len(prelude)`` (as ``start`` does for the artifact splice).
    """
    if not seed_text.strip():
        # Nothing to split: a blank text has no prelude and no goal. The real path cannot reach this
        # (a seed file always states a declaration), while the responder seam answers an empty payload
        # with a goal state, which is how the close-guard scenarios load.
        return seed_text, ""
    matches = declaration_matches(seed_text)
    if not matches:
        raise LeanReplError(
            "the seed states no declaration: a Route B seed carries the statement under test as its "
            "last declaration, with one `sorry` where its proof goes (plan D5/D15)"
        )
    payload_start = _goal_payload_start(seed_text, matches[-1].start())
    prelude, goal = seed_text[:payload_start], seed_text[payload_start : _goal_payload_end(seed_text, payload_start)]
    holes = count_unclosed(goal)
    if holes == 0:
        raise SeedAlreadyClosedError(
            "the seed's last declaration carries no `sorry`, so there is no goal to close: a measured "
            "run starts from the recorded baseline, never from a file a previous run rewrote (plan D15)"
        )
    if holes > 1:
        raise LeanReplError(
            f"the seed's last declaration carries {holes} holes, not one: the seed must state the "
            "statement under test with exactly one `sorry` where its proof goes"
        )
    return prelude, goal


def _env_of(response: dict) -> int | None:
    """The environment id a response reports, or ``None`` when it carries none usable.

    Every answered command reports the id of the command snapshot it left (``runCommand`` records one
    per answer), and that snapshot is the session's state: the prelude's id is what the goal command
    continues from, and each later command continues from the newest id.
    """
    env = response.get("env")
    return env if isinstance(env, int) and not isinstance(env, bool) else None


def _errors_in(response: dict) -> list[str]:
    """The repl's error messages in a response; ``messages`` is optional in the protocol."""
    messages = response.get("messages") or []
    return [
        str(message.get("data", "")).strip()
        for message in messages
        if isinstance(message, dict) and message.get("severity") == "error"
    ]


def _message_texts(response: dict) -> list[str]:
    """Every message a response carries, verbatim and in order, whatever its severity.

    The command channel's output is itself a message — ``#eval``/``#check``/``#reduce`` print there —
    so this is where a command's own answer is surfaced for the row rather than summarised here
    (plan D16). Trailing newlines are dropped: the framing is the repl's, not the output's.
    """
    messages = response.get("messages") or []
    return [
        str(message.get("data", "")).rstrip("\n")
        for message in messages
        if isinstance(message, dict)
    ]


def _resolve_binary(binary: str) -> str:
    """The repl binary as an absolute path, resolved before the child's working directory changes.

    The child runs in the project directory, so a relative binary path would resolve against the wrong
    cwd — the same reason ``harness.tlc_run`` resolves ``--tlc-bin`` before launching.
    """
    if os.sep not in binary and not Path(binary).exists():
        return binary  # a bare name: leave it to PATH, under `lake env`'s environment
    path = Path(binary).resolve()
    if not path.exists():
        raise LeanReplError(
            f"repl binary {binary!r} does not exist at {path}: the Lean prover is provisioned by "
            "plan step 1b (see tools/repl/PROVENANCE.md)"
        )
    return str(path)


def _kill_tree(process: subprocess.Popen) -> None:
    """Kill a process and everything it spawned (the repl runs under ``lake env``)."""
    if process.poll() is not None:
        return
    try:
        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        process.kill()
    process.wait()


def _offsets(text: str, start: dict, end: dict, *, bytes: bool) -> tuple[int, int]:
    """The ``[start, end)`` offsets a lean-repl position pair points at under one column reading.

    A position is a 1-based line and a column counted from that line's start; ``bytes`` says whether
    that column counts UTF-8 bytes or characters (Python's own indexing).
    """
    def offset(position: dict) -> int:
        line = int(position["line"])
        column = int(position["column"])
        if line < 1:
            raise LeanReplError(f"lean-repl position has no line: {position!r}")
        running = 0
        for index, text_line in enumerate(text.split("\n"), start=1):
            if index == line:
                return running + column
            running += (len(text_line.encode("utf-8")) if bytes else len(text_line)) + 1
        raise LeanReplError(f"lean-repl position {position!r} is past the end of the text it indexes")

    return offset(start), offset(end)


def locate_token(text: str, token: str, start: dict, end: dict) -> tuple[int, int]:
    """The character span of ``token`` at a lean-repl position pair, checked rather than assumed.

    The readings agree on ASCII and diverge as soon as a line carries non-ASCII before the goal
    (``theorem t (n : ℕ) : … := by sorry``), and splicing a proof into the wrong offsets would corrupt
    the artifact silently. So the reading that reproduces the token wins, and a pair pointing at
    anything else is raised rather than guessed at.

    ``text`` must be the text the positions were reported against: the repl reports them in the frame
    of the *payload it ran* (``split_seed``), so a caller working in the file's frame passes the goal
    payload here and shifts the result by ``len(prelude)``.
    """
    beginning, ending = _offsets(text, start, end, bytes=False)
    if text[beginning:ending] == token:
        return beginning, ending
    data = text.encode("utf-8")
    byte_beginning, byte_ending = _offsets(text, start, end, bytes=True)
    if data[byte_beginning:byte_ending].decode("utf-8") == token:
        # Byte offsets: express them as character offsets, which is what the caller splices with.
        return len(data[:byte_beginning].decode("utf-8")), len(data[:byte_ending].decode("utf-8"))
    raise LeanReplError(
        f"the repl reported the goal at {text[beginning:ending]!r} ({start!r}..{end!r}), not "
        f"{token!r}: refusing to splice a proof there"
    )


def splice_proof(seed_text: str, start: int, end: int, tactics: Sequence[str]) -> str:
    """The artifact: the seed with the ``sorry`` at ``[start, end)`` replaced by the script.

    Each tactic keeps its own relative layout and the whole script is indented, so it sits inside the
    ``by`` block whatever indentation the seed used.
    """
    span = seed_text[start:end]
    if span != "sorry":
        raise LeanReplError(
            f"the repl reported the goal at {span!r}, not `sorry`: refusing to splice a proof there"
        )
    body = "\n" + "\n".join(f"  {line}" for line in "\n".join(tactics).split("\n"))
    return seed_text[:start] + body + seed_text[end:]


class LeanReplProver:
    """The ``Prover`` port (``harness.closure``) over a ``repl`` subprocess (plan D2).

    ``proof`` is the working copy the run closes: the file carrying the statement under test, which
    ``harness.route_b`` writes from the committed seed's recorded baseline before the run (plan D15).
    It is read on ``start`` and written once — and only once — the prover reports the proof closed, so
    the copy carries a proof exactly when a run closed it, and a run that failed leaves it as it found
    it (plan D5: the copy lives inside the lake package, which is what keeps the seed's imports
    resolvable). The committed seed itself is never written.

    The seed is loaded in **two** payloads, threading the environment (``split_seed``): the prelude
    first, with no ``env`` — a fresh environment is the only one ``import`` is allowed in — and then the
    goal declaration with the prelude's ``env``, so the proof state opens over the declarations the goal
    is stated in. Every later command carries that environment as well, and adopts the one each answer
    reports. Loading the whole file in one payload leaves the goal stated in constants its own tactic
    environment cannot resolve, and then no tactic can ever make progress.

    ``responder`` replaces the repl process for tests: it is called with the command the driver would
    write and returns the response it would read, so the close-guard is exercised without Lean
    (tests/lean-driver-contract.md). ``mutant`` marks a run of a statement that is false, whose
    artifact is never written (plan D7).
    """

    def __init__(
        self,
        proof: Path | str,
        repl_cmd: Sequence[str],
        *,
        responder: Callable[[dict], dict] | None = None,
        mutant: bool = False,
        start_timeout_s: float = START_TIMEOUT_S,
        step_timeout_s: float = STEP_TIMEOUT_S,
    ) -> None:
        self.proof = Path(proof)
        self.repl_cmd = [str(part) for part in repl_cmd]
        self.responder = responder
        self.mutant = mutant
        self.start_timeout_s = start_timeout_s
        self.step_timeout_s = step_timeout_s

        self.seed_text = ""  # the artifact as the run found it
        self.tactics: list[str] = []  # accepted tactics, in order: the script the artifact carries
        # Refused answers, each with its kind and the reason verbatim: the row reads this (plan D24).
        self.failures: list[Failure] = []

        self._process: subprocess.Popen | None = None
        self._stdin = None
        self._responses: queue.Queue[str | None] = queue.Queue()
        self._stderr: list[str] = []
        self._proof_state: int | None = None
        self._env: int | None = None  # the repl's newest command snapshot: what the next cmd continues
        self._goals: list[str] = []
        self._sorry_span: tuple[int, int] | None = None

    # --- the Prover port -----------------------------------------------------
    def start(self) -> None:
        """Spawn the repl, load the seed, and return once the goal at its ``sorry`` is ready.

        ``harness.closure.run_loop`` times this call and records it as ``startup_s`` (protocol §4.6):
        the seed's imports and oleans are loaded here, the proof search is not.
        """
        self.close()
        # A run's record is this run's own: `start()` closes and re-establishes the session, and the
        # row reads `tactics`/`failures`, so a restart must not carry the previous run's steps into it.
        self.tactics = []
        self.failures = []
        # Until the repl reports a goal state, the driver has none of its own: a start that fails must
        # not leave `unclosed()` reading 0 — the loop's only closure signal — and a restart must not
        # report the previous run's goals. The sentinel is the one a rejected answer leaves behind
        # (plan D6).
        self._goals = [NOT_CLOSED_GOAL]
        # A restart's environment is the one this load establishes, never the previous session's.
        self._env = None
        if self.responder is not None:
            # The scripted responder stands in for the repl's channels, so the load is the same two
            # payloads the real path sends (`split_seed`) whenever a seed file is there to split — a
            # scenario can then pin the sequence and the `env` threading — while the close-guard
            # scenarios, whose path need not exist, get the one empty payload they answer.
            self.seed_text = self.proof.read_text() if self.proof.is_file() else ""
            prelude, goal = split_seed(self.seed_text)
            if prelude.strip():
                loaded = self._ask({"cmd": prelude}, self.start_timeout_s, f"loading {self.proof}")
                self._adopt_env(loaded)
            payload: dict = {"cmd": goal}
            if self._env is not None:
                payload["env"] = self._env
            describing = f"opening {self.proof}'s statement"
            response = self._ask(payload, self.start_timeout_s, describing)
            self._adopt_env(response)
            self._adopt_state(response, describing)
            return
        self.seed_text = self.proof.read_text()
        prelude, goal = split_seed(self.seed_text)
        self._spawn()
        if prelude.strip():
            # The prelude goes first with no `env`: a fresh environment is the only one `import` is
            # allowed in, and its answer is what carries the seed's declarations into the proof state
            # opened below (`split_seed`). A seed that is only its statement has no prelude to run.
            loaded = self._ask({"cmd": prelude}, self.start_timeout_s, f"loading {self.proof}")
            if "message" in loaded:
                raise LeanReplError(f"the repl could not load {self.proof}: {loaded['message']}")
            errors = _errors_in(loaded)
            if errors:
                raise LeanReplError(f"{self.proof}'s prelude does not elaborate: {'; '.join(errors)}")
            self._adopt_env(loaded)
        payload: dict = {"cmd": goal}
        if self._env is not None:
            payload["env"] = self._env
        response = self._ask(payload, self.start_timeout_s, f"opening {self.proof}'s statement")

        if "message" in response:
            raise LeanReplError(f"the repl could not load {self.proof}: {response['message']}")
        errors = _errors_in(response)
        if errors:
            raise LeanReplError(f"{self.proof} does not elaborate: {'; '.join(errors)}")
        sorries = [
            sorry for sorry in response.get("sorries") or [] if isinstance(sorry, dict) and sorry.get("proofState") is not None
        ]
        if not sorries:
            # No goal to close: the file carries no placeholder the loop can replace, which is what a
            # seed already closed by a legacy in-place run looks like (plan D15). It is a refusal to
            # run, not a step that failed, so it is its own kind for the row and the exit code.
            raise SeedAlreadyClosedError(
                f"{self.proof} presents no goal with a proof state: the seed is already closed, or "
                "carries no `sorry` for the run to close — a measured run starts from the recorded "
                "baseline, never from a file a previous run rewrote (plan D15)"
            )
        if len(sorries) > 1:
            raise LeanReplError(
                f"{self.proof} presents {len(sorries)} goals with a proof state, not one: the seed "
                "must carry the statement under test and exactly one `sorry` where its proof goes"
            )
        sorry = sorries[0]
        if not isinstance(sorry.get("pos"), dict) or not isinstance(sorry.get("endPos"), dict):
            raise LeanReplError(f"the repl did not report where {self.proof}'s sorry is: {sorry!r}")
        self._proof_state = int(sorry["proofState"])
        self._goals = [str(sorry["goal"])]
        # The repl reports positions in the payload it ran, which is the goal command — not the file —
        # so the `sorry` is located there and shifted into the file frame the splice works in. The
        # shift is exact: the goal payload is a suffix of the seed text (`split_seed`).
        span_start, span_end = locate_token(goal, "sorry", sorry["pos"], sorry["endPos"])
        offset = len(prelude)  # the goal payload begins where the prelude ends
        self._sorry_span = (span_start + offset, span_end + offset)
        # The state the goal declaration left: the declarations are in it, and every later command
        # continues from it (`split_seed`).
        self._adopt_env(response)

    def _adopt_state(self, response: dict, describing: str) -> None:
        """Take the goal state a response reports, refusing anything that is not a closed proof.

        This is the close-guard (plan D6) read the way ``apply`` reads it: an empty goal list is
        closure only with a ``proofStatus`` beginning ``Completed``. An answer the driver cannot read
        as a goal state, and an empty one that is not closure, both leave the run open — ``unclosed()``
        must stay positive, since the loop reads it as the run's only success signal — and the reason
        is recorded in ``failures``.
        """
        if _closed_by(response):
            self._goals = []
            return
        try:
            goals = _goals_of(response)
        except LeanReplError as unreadable:
            self._reject(describing, str(unreadable), kind="transport")
            return
        if goals:
            self._goals = goals
            if isinstance(response.get("proofState"), int):
                self._proof_state = int(response["proofState"])
            return
        status = _status_of(response)
        if status is None:
            # No readable verdict: the rig could not tell what happened, so this is not Lean refusing
            # the step (finding P1.2).
            self._reject(
                describing,
                f"the repl's answer states no readable proof status: {response!r}",
                kind="transport",
            )
            return
        self._reject(describing, f"the repl reports {status!r}, not a closed proof", kind="lean")

    def _reject(self, describing: str, reason: str, *, kind: str) -> None:
        """Record a refused answer and hold the run open: ``unclosed()`` must stay positive.

        ``kind`` is whose refusal it is (plan D24): ``"lean"`` when Lean judged the step,
        ``"transport"`` when the step never reached it.
        """
        self.failures.append({"kind": kind, "message": f"{describing}: {reason}"})
        self._goals = [NOT_CLOSED_GOAL]

    def _adopt_env(self, response: dict) -> None:
        """Continue from the environment a response reports, when it reports one.

        The load establishes it (``split_seed``: the prelude's answer, then the goal declaration's) and
        every command continues from the newest one, or the next command would run in a fresh
        environment that holds none of the seed's declarations (P0, D16's channel).
        """
        env = _env_of(response)
        if env is not None:
            self._env = env

    def goals(self) -> list[str]:
        """The goals the repl reports at the current proof state, in order."""
        return list(self._goals)

    def unclosed(self) -> int:
        """How many goals remain: ``0`` only once the repl reported a completed proof (§8)."""
        return len(self._goals)

    def apply(self, tactic: str) -> None:
        """Apply one tactic to the goal the repl reports and keep the state it produces, if any.

        A tactic that does not elaborate — including the empty tactic a reasoning model can return —
        a tactic that "closes" the goal with ``sorry`` or a metavariable, and an answer the driver
        cannot read as a goal state all leave the proof state where it was, so the loop's next turn
        sees the same goal; each is recorded in ``failures``.

        A reply carrying a ``;`` is handed over **parenthesised**. The repl parses this field with
        Lean's ``tactic`` category (``REPL/Snapshots.lean``: ``runParserCategory … `tactic``), and ``;``
        belongs to ``tacticSeq``, not to ``tactic`` — so a model's perfectly valid ``t1; t2`` used to
        come back as ``expected end of input`` at the ``;``, a *transport* refusal recorded as if Lean
        had rejected the proof (measured live: ``'skip; skip'`` fails at 1:4, ``'(skip; skip)'`` runs,
        and ``'skip <;> skip'`` runs because ``<;>`` *is* in the category). Parentheses change no
        semantics; the reply itself stays verbatim everywhere it is recorded, and only what the repl is
        handed is wrapped.
        """
        if self._proof_state is None:
            raise LeanReplError("apply() before start()")
        if not tactic.strip():
            # Nothing to hand over. The loop never applies an empty reply (D11 consumes and re-asks
            # it), so this is a guard rather than a path — but if it is ever reached, the refusal is the
            # rig's, not Lean's, and must be recorded as such (plan D24).
            self.failures.append(
                {"kind": "transport", "message": "the reply was empty: nothing to hand Lean"}
            )
            return
        sent = f"({tactic})" if ";" in tactic else tactic
        response = self._ask(
            {"tactic": sent, "proofState": self._proof_state},
            self.step_timeout_s,
            f"applying {sent!r}",
        )
        if "message" in response:
            self.failures.append(
                {"kind": "lean", "message": f"{sent!r}: {' '.join(str(response['message']).split())}"}
            )
            return
        try:
            goals = _goals_of(response)
        except LeanReplError as unreadable:
            self.failures.append({"kind": "transport", "message": f"{sent!r}: {unreadable}"})
            return
        if not goals and not _closed_by(response):
            # The close-guard (plan D6): no goals, but not the repl's word that the proof is closed.
            # That is its shape both for a tactic it recovered from as a `sorry` goal and for a proof
            # that still ends in one, so the state stays where it was and the loop cannot read this as
            # closure; the message, when the repl sent one, is the only account of what went wrong.
            status = _status_of(response)
            errors = _errors_in(response)
            if status is None and not errors:
                # Nothing here shows Lean considered the tactic: an unreadable answer is the rig's
                # failure to read the repl, not the model's bad tactic (finding P1.2).
                self.failures.append(
                    {
                        "kind": "transport",
                        "message": (
                            f"{sent!r}: the repl's answer states no readable proof status: {response!r}"
                        ),
                    }
                )
                return
            detail = f" — {' '.join(errors[0].split())}" if errors else ""
            self.failures.append(
                {
                    "kind": "lean",
                    "message": f"{sent!r}: the repl reports {status!r}, not a closed proof{detail}",
                }
            )
            return
        if not isinstance(response.get("proofState"), int):
            raise LeanReplError(f"the repl's answer to {tactic!r} carries no proof state: {response!r}")
        self._proof_state = response["proofState"]
        self._goals = goals
        self.tactics.append(tactic)
        if not goals:
            self._write_artifact()

    def cmd(self, command: str) -> dict:
        """Run one Lean command through the repl's command channel and report Lean's verdict on it.

        The command channel elaborates the command in the seed's environment: its response is the
        repl's ``CommandResponse``, whose ``messages`` carry the command's own output (``#eval``,
        ``#check``, ``#reduce``) and whose ``sorries`` is empty when what ran closed with nothing left
        to prove (``tools/repl/README.md``; ``REPL/JSON.lean``). That is the refutation arm's channel
        (plan D16): the model proposes a command, and only Lean's own answer is reported, never the
        model's say-so.

        The verdict is mechanical, and the command is sent as the caller wrote it:

        * ``refuted`` — ``True`` only for an answer read as *accepted with no hole*: a readable answer
          (it reports an ``env``), no error-severity message, and no remaining ``sorries``. The repl
          **omits** an empty list (``Json.nonemptyList`` in ``REPL/JSON.lean``), so an absent
          ``sorries`` means *no holes* — unlike an absent ``goals`` in the proof channel, where the
          emptiness is itself the closure signal and must not be inferred.
        * ``witness`` — the accepted command itself, verbatim. It is what the acceptance is evidence
          *of*: a reader can check that the closed example is the goal's negation, which is the
          template's requirement and not something the driver can certify from the response.
        * ``messages`` — every message the repl sent, verbatim and in order, so a command's output is
          recorded rather than summarised.
        * ``sorries`` — the proof states the answer left open (``[]`` when it left none).
        * ``reason`` — why the answer was not a witness (the repl's refusal, the errors it reported, or
          the goals it left open), else ``None``. A rejection is appended to ``failures`` as well, the
          port's own record of what the driver refused and why, which the loop reads into the next
          turn's history so a refused command reaches the model with its reason (plan D14) instead of
          leaving it to guess again from a goal state that did not move.

        A rejection is data, never an exception: an arm that keeps proposing until a budget binds must
        not lose the run to a wrong proposal (plan D16). Only a transport or protocol failure raises
        ``LeanReplError``, exactly as the proof channel's :meth:`apply` does.

        The command carries the session's ``env`` (``start`` established it by loading the seed in two
        payloads, ``split_seed``): without it the repl would run the command in a *fresh* environment
        that holds none of the seed's declarations, so a ``#check``/``#eval``/``example`` about them
        would be answered from an environment in which they do not exist. An **accepted** answer's
        environment is adopted, so the next command continues from the state that command left; a
        rejected one changes nothing, so the environment stays where it was.

        The payload also carries :data:`AUTOIMPLICIT_OFF` ahead of the command (plan D16): with Lean's
        autoImplicit on, a name the seed does not declare is silently bound as a fresh variable, so a
        typo'd statement can be vacuously true and still answer with no errors and no holes — accepted
        here as a machine-checked witness. With the option off, a wrong name is an error: a rejection
        that names the mistake, which is what a falsifiable refutation arm needs.
        """
        payload: dict = {"cmd": f"{AUTOIMPLICIT_OFF}\n{command}"}
        if self._env is not None:
            payload["env"] = self._env
        response = self._ask(payload, self.step_timeout_s, f"running {command!r}")
        messages = _message_texts(response)
        sorries = response.get("sorries")
        holes = sorries if isinstance(sorries, list) else []
        errors = _errors_in(response)
        kind = "lean"
        if "message" in response:
            reason: str | None = f"the repl refused the command: {response['message']}"
        elif _env_of(response) is None:
            reason = f"the repl's answer carries no environment: {response!r}"
            kind = "transport"  # nothing to run the command against: we could not hand it over
        elif errors:
            reason = f"the command errors: {'; '.join(errors)}"
        elif holes:
            reason = f"the command leaves {len(holes)} goal(s) open"
        else:
            reason = None
        if reason is not None:
            self.failures.append({"kind": kind, "message": f"{command!r}: {reason}"})
        else:
            self._adopt_env(response)
        return {
            "refuted": reason is None,
            "witness": None if reason is not None else command,
            "reason": reason,
            "messages": messages,
            "sorries": holes,
        }

    # --- process lifecycle ---------------------------------------------------
    def close(self) -> None:
        """Stop the repl: closing its stdin ends the session by the repl's own protocol."""
        process, self._process = self._process, None
        self._stdin = None
        if process is None or process.poll() is not None:
            return
        try:
            if process.stdin is not None:
                process.stdin.close()
        except OSError:
            pass
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            _kill_tree(process)

    def _project_root(self) -> Path:
        """The lake package the repl runs in: where the seed's imports resolve."""
        for directory in self.proof.resolve().parents:
            if (directory / "lakefile.toml").is_file() or (directory / "lakefile.lean").is_file():
                return directory
        return self.proof.resolve().parent

    def _spawn(self) -> None:
        binary = _resolve_binary(self.repl_cmd[0])
        cmd = [*LAKE_ENV, binary, *self.repl_cmd[1:]]
        try:
            self._process = subprocess.Popen(
                cmd,
                cwd=str(self._project_root()),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
        except OSError as error:
            raise LeanReplError(f"cannot start the repl ({' '.join(cmd)}): {error}") from error
        self._stdin = self._process.stdin
        self._stderr = []
        threading.Thread(
            target=_drain_responses, args=(self._process.stdout, self._responses), daemon=True
        ).start()
        threading.Thread(target=_drain_stderr, args=(self._process.stderr, self._stderr), daemon=True).start()
        # The loop never closes the prover; the CLI's exit must not leave a repl (and its ~GB of
        # Mathlib oleans) behind.
        atexit.register(self.close)

    def _ask(self, payload: dict, timeout: float, describing: str) -> dict:
        """Send one command and return the repl's response to it.

        With a ``responder`` the command goes to it rather than to the repl's stdin: the responder is
        called with the payload the driver would write and returns the response it would read, which
        is how the close-guard is exercised without a Lean installation.
        """
        if self.responder is not None:
            response = self.responder(payload)
            if not isinstance(response, dict):
                raise LeanReplError(f"the scripted responder answered {response!r} for {describing}")
            return response
        if self._process is None:
            raise LeanReplError("the repl is not running")
        # Commands are framed by a blank line; the repl answers each with its (pretty-printed, hence
        # multi-line) JSON object and a blank line of its own.
        try:
            self._stdin.write(json.dumps(payload) + "\n\n")
            self._stdin.flush()
        except (BrokenPipeError, ValueError, OSError) as error:
            raise LeanReplError(f"the repl is not reading input: {error}{self._stderr_tail()}") from error
        try:
            line = self._responses.get(timeout=timeout)
        except queue.Empty:
            self.close()
            raise LeanReplError(
                f"the repl did not answer {describing} within {timeout:g}s{self._stderr_tail()}"
            ) from None
        if line is None:
            raise LeanReplError(
                f"the repl exited while {describing}{self._stderr_tail()}"
            )
        try:
            response = json.loads(line)
        except json.JSONDecodeError as error:
            raise LeanReplError(f"the repl answered non-JSON for {describing}: {line!r}") from error
        if not isinstance(response, dict):
            raise LeanReplError(f"the repl answered {response!r} for {describing}")
        return response

    def _stderr_tail(self, lines: int = 20) -> str:
        tail = "\n".join(self._stderr[-lines:])
        return f"\nrepl stderr:\n{tail}" if tail else ""

    def _write_artifact(self) -> None:
        """Write the accepted script into the artifact in place (plan D5: the seed's own file).

        A mutant run never writes: its statement is false, so a run that closed it has a broken rig
        rather than a proof (protocol §5), and the tree must keep the honest seed instead of a false
        "proof" spliced into it. The run still reports the closure, and the loop records it as a
        ``mutant_closed`` error row rather than raising, so the rig defect survives in the data
        (plan D7, ticket P2-3).
        """
        if self.mutant:
            return
        if self._sorry_span is None:
            return
        start, end = self._sorry_span
        self.proof.write_text(splice_proof(self.seed_text, start, end, self.tactics))


def _drain_responses(stream, sink: queue.Queue[str | None]) -> None:
    """Collect the repl's responses, one blank-line-framed block at a time.

    A response is a **pretty-printed, multi-line** JSON object followed by a blank line (the repl's
    own framing), so the block — not the line — is the unit. The caller holds one outstanding command
    at a time, so the blocks arrive in order; a ``None`` sentinel marks the stream ending, which the
    caller must see rather than wait out its timeout.
    """
    block: list[str] = []
    for line in stream:
        if line.strip():
            block.append(line.rstrip("\n"))
        elif block:
            sink.put("\n".join(block))
            block = []
    if block:
        sink.put("\n".join(block))
    sink.put(None)


def _drain_stderr(stream, sink: list[str]) -> None:
    """Keep the child's diagnostics: ``lake env`` reports there, outside the JSON stream."""
    for line in stream:
        sink.append(line.rstrip("\n"))
