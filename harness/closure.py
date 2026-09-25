"""Route B: the AI closure loop (docs/protocol.md §8).

The loop alternates between a prover's goal state and a model's proposed tactic, under a wall-clock,
token and dollar budget. Four invariants hold whatever the model does:

* success is asserted from the prover reporting no unclosed goals, never from what the model said;
* running out of budget is reported as ``timeout`` with the binding budget named;
* a statement that is false is never recorded as closed — a mutant run that fails to close is reported
  as ``fail_to_close``: the repl's tactic channel cannot exhibit a counterexample, so no disproof is
  claimed (protocol §5, plan D7), while ``proof.tactics`` keeps the steps the prover applied and
  ``proof.failures`` the ones it refused. A mutant run that *does* close is a rig defect, and the row
  is where a negative control reports it: ``outcome: "error"`` with ``error.kind: "mutant_closed"``,
  never an exception that loses the observation with the run. The refutation arm (plan D16) is the
  other way a mutant ends as predicted: a witness the *prover* machine-checked ends the race as
  ``refuted``, and a witness against a statement the caller does not declare false is the mirror
  defect — ``error.kind: "rig_refutation"`` — recorded the same way;
* any change to the seed's declarations other than a ``theorem``/``lemma`` ``sorry`` replaced by a
  proof is recorded rather than refused: the row names what changed and marks the run ``assisted``
  (protocol §11 decision 5, plan D5);
* a failure in the middle of a run is an outcome, not a lost budget: an empty-content reply is a
  consumed, billed turn that is re-asked with a nudge and never an abort — only a budget ends such a
  run, as ``timeout`` (D11) — while a provider failure lands an ``error`` row carrying the turns,
  tokens and dollars already spent (D12). The prover side of the port behaves the same way: a driver
  that cannot load the seed or run a step (``ProverError``) lands an ``error`` row with
  ``error.kind: "prover_failure"``, the driver's message verbatim and the partial artifact kept, never
  a traceback that loses a run's budget.

Startup (the prover's environment/olean load) and the proof search are reported as separate intervals
of the wall-clock: ``startup_s`` ends when the prover's first goal state is ready, ``proof_s`` is what
follows it (protocol §4.6).
"""

from __future__ import annotations

import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness import lean_lex  # noqa: E402
from harness.result import COST_BASIS, compute_basis, compute_cost_usd  # noqa: E402


class Prover(Protocol):
    """The prover's observable surface: start it, read goals, apply a tactic, ask what is left.

    ``tactics`` and ``failures`` are what the driver did with the loop's proposals: the steps it
    applied — what the artifact carries — and the steps it refused, with the prover's own reason.
    ``run_loop`` reads both when the prover provides them, because only the driver can tell an applied
    step from a refused one; a prover that reports neither has its own proposals as the row's tactics
    and no refusals to report (plan D7). A driver that cannot load the seed or run a step at all — a
    repl that timed out, died, or answered outside the protocol — raises ``ProverError``: the loop
    records it as an ``error`` row rather than letting it escape and lose the run.

    ``cmd`` runs one Lean command through the repl's command channel (plan D16) and returns Lean's
    verdict on it, as the driver read that verdict — never the model's claim. Four rules of that
    reading carry the arm, and a driver that gets one wrong turns a refusal into a result:

    * ``refuted`` is ``True`` only for an answer the driver read as *accepted with nothing left to
      prove*: a readable answer (one that reports an environment), no error-severity message, and no
      remaining holes. The repl **omits** an empty ``sorries`` list, so an absent ``sorries`` means *no
      holes*, unlike the proof channel's ``goals``, where an absent list is unreadable and never
      closure. A missing or unreadable environment is a rejection, not an acceptance.
    * the command runs in the **session's environment** — the seed's declarations have to be in scope —
      so the payload carries the session ``env``, and an accepted answer's environment is adopted for
      the next command while a rejected one's is not. The payload is also sent with Lean's
      ``autoImplicit`` turned off: with it on, a name the seed does not declare is silently bound as a
      fresh variable, and a typo'd statement can be vacuously true and still answer with no errors and
      no holes — accepted as a witness.
    * ``witness`` is the accepted command, verbatim: what the acceptance is evidence *of*, so a reader
      can check it against the negated-statement template rather than take the driver's word that the
      closed command states the negation.
    * a rejection is data, never an exception — ``{"refuted": False, …}`` with the driver's ``reason``
      and anything it learned (``messages``, the ``sorries`` left open) — and the driver appends it to
      ``failures``, which the loop reads into the next turn's history so the arm is told why it was
      refused instead of guessing again from a goal state that did not move. Only a transport or
      protocol failure raises ``ProverError``, exactly as on the proof channel.
    """

    def start(self) -> None: ...

    def goals(self) -> Sequence[str]: ...

    def apply(self, tactic: str) -> None: ...

    def cmd(self, command: str) -> dict: ...

    def unclosed(self) -> int: ...

    tactics: Sequence[str]
    failures: Sequence[str]


# One turn as the model sees it (plan D14): the tactic proposed, the goals it left, and — when the
# prover refused it, or when the reply carried no tactic and the loop re-asked instead of applying it —
# the reason, verbatim: the driver's own words for a refusal, the loop's nudge for an empty reply. A
# turn the prover applied carries no reason; its resulting goal state is the account of what it did.
HistoryEntry = tuple[str, Sequence[str], str | None]


class Model(Protocol):
    """A model that proposes one tactic for the current goals and reports cumulative usage.

    ``propose`` receives the loop's ``HistoryEntry`` list, so a proposal the prover refused reaches
    the next turn with the reason it was refused: without it the model sees the goal state stay put
    and no account of why, and guesses again (plan D14).

    ``refute`` is the refutation arm's proposal (plan D16): one Lean command, proposed in the same
    history, which the prover's ``cmd`` channel then checks. The arm is named by which method the loop
    calls, so the client assembles the two prompts — "propose a tactic" and "propose a refutation" —
    and nothing in the loop decides what a refutation looks like.

    ``usage()`` carries what the row records beside the token counts: ``input``, ``output``,
    ``cached_input`` and ``cost_usd`` (summed over the session), the configured ``model``,
    ``thinking`` and ``temperature``, the provider's ``resolved_model``, whether any turn was served
    by a fallback (``is_fallback``), the ``prompt`` composition the model was shown (plan D14), and
    the ``cost_basis`` the dollars were computed against.

    ``plan`` is the planning turn (plan D19): once per arm, before that arm acts, the model states how
    it intends to proceed, in neutral slots — its own approach, its steps, the end state it expects,
    and any statement it intends to use that the file does not already state. The text is recorded
    verbatim in the row, so it is evidence of how the model reasoned rather than a summary the harness
    composed. A model port without a ``plan`` turn is a run without one: the loop asks for a plan only
    when the port has it, and records ``None`` for the arms it could not ask.
    """

    def propose(self, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str: ...

    def refute(self, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str: ...

    def plan(self, arm: str, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str: ...

    def usage(self) -> dict: ...


class ProviderError(RuntimeError):
    """A provider call that failed, as the provider reported it (plan D12).

    ``status`` is the HTTP status the provider answered with (0 when the call never got one) and
    ``message`` its own message, verbatim. ``run_loop`` turns this into an ``error`` row instead of
    letting a mid-run failure lose the budget already spent.
    """

    def __init__(self, status: int, message: str) -> None:
        super().__init__(f"provider call failed: HTTP {status}: {message}")
        self.status = status
        self.message = message


class ProverError(RuntimeError):
    """The prover failed: the driver could not load the seed or run a step (protocol §8).

    A repl that exceeds its step timeout, exits, answers outside the protocol, or cannot load the seed
    is the prover's own machinery failing, not a tactic the model proposed. ``message`` is the
    driver's message, verbatim — it is what the row records — and ``kind`` is the row's error kind,
    which a subclass narrows for a condition the CLI treats differently (``SeedAlreadyClosedError``):
    ``run_loop`` records ``failure.kind`` rather than assuming one, so a distinguishable failure stays
    distinguishable in the row and in the exit code. Every driver of the ``Prover`` port raises this
    (``harness.lean_repl.LeanReplError`` is one), so that ``run_loop`` can turn a mid-run failure into
    an ``error`` row carrying the turns, tokens and dollars already spent, and leave the partial
    artifact where it is (D12's rule, applied to the prover side of the port).
    """

    kind = "prover_failure"

    def __init__(self, message: str) -> None:
        super().__init__(message)
        self.message = message


class SeedAlreadyClosedError(ProverError):
    """The seed carries no goal to close (plan D15).

    The driver loads the statement under test from the seed's one ``sorry``; a seed that presents no
    goal has already been closed (the legacy in-place run wrote its proof over the placeholder) or was
    never a fresh seed. It is the failure the immutable baseline and the per-run working copy exist to
    make impossible, so it is its own kind — the row says ``seed_already_closed`` and the CLI refuses
    with a distinct exit code — rather than being pooled with a prover that died mid-run.
    """

    kind = "seed_already_closed"


# What the row says when a mutant run closed (protocol §5). A rig that reports success on a false
# statement is broken and its numbers are discarded; the observation is the single thing a negative
# control exists to report, so it is recorded in the row — an `error` naming the defect — rather than
# raised into a traceback that loses the row (and the run's spent budget with it).
MUTANT_CLOSED_MESSAGE = (
    "the loop closed the mutant's statement: a rig that reports success on a mutant is broken "
    "and its numbers are discarded (protocol §5)"
)

# The mirror defect (plan D16, protocol §5): the refutation arm produced a witness against a statement
# the reference semantics says holds. `--mutant` is what declares a statement false, so any other run's
# accepted witness is a rig defect — recorded loudly, never pooled as a result.
RIG_REFUTATION_MESSAGE = (
    "the refutation arm produced a machine-checked witness against a statement the reference semantics "
    "says holds: a rig that can refute a theorem TLC proves is broken, and its numbers are discarded "
    "(protocol §5, plan D16)"
)

# The two arms a run can field (plan D16/D17): the proof arm alone (the pre-D16 behaviour), or the
# proof arm racing the refutation arm under one shared budget.
ARM_PROOF = "proof"
ARM_REFUTATION = "refutation"
ARMS_CONFIGURATIONS = ("proof", "proof+refutation")


# What the loop says to a model that answered with no tactic (plan D11). It is carried in the history
# as that turn's note, so the re-ask is a nudge rather than the identical prompt again — and it never
# terminates the run: the budget binds long before a model that answers nothing can be called a
# failure, which is what makes a mutant's `fail_to_close` reachable.
EMPTY_REPLY_NUDGE = "you returned no tactic; propose one for the current goals"

# The same for a planning turn (plan D19): an empty plan is a consumed turn, re-asked with the slots it
# did not fill rather than the tactic nudge, because the two turns ask for different things.
EMPTY_PLAN_NUDGE = "you returned no plan; state your approach, steps, expected end state and candidate"

# The cheap automation the loop tries before asking the model (plan D19), in the order it tries them:
# deterministic closers first, search-based ones last. It holds only tactics that either close the goal
# or leave it exactly as they found it — an attempt that does not close must not silently rewrite the
# goal the model is working on — which is why `simp_all` is named in the prompt for the model to use
# but is not in the pass: a `simp_all` that fails has already simplified the goal. `decide` is here
# because a goal it closes is exactly the no-induction close §5's vacuousness guard must see.
AUTOMATION_TACTICS = ("omega", "decide", "aesop", "exact?", "apply?")

# Every declaration spelling the seed-diff looks for, and the spellings it tolerates in front of one:
# an attribute or a modifier does not make a declaration a proof step, and a spelling the diff cannot
# see is a human's declaration it would call faithful (plan D5). The match tolerates indentation: a
# declaration is real wherever Lean accepts one — inside `namespace`/`section`/`mutual`, a `where`
# clause's member, or simply how a human appends a helper — and a column-0-only match read every one of
# those as part of the declaration above it (ticket P1-1).
_DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "opaque",
    "example", "macro", "notation", "syntax", "axiom",
)
_MODIFIERS = ("private", "protected", "noncomputable", "local")
_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:@\[[^\]]*\]|" + "|".join(_MODIFIERS) + r")\s+)*"
    r"(?P<kind>" + "|".join(_DECL_KINDS) + r")\b(?P<rest>[^\n]*)"
)
# A declaration's name is a Lean identifier, subscripts and all: `abbrev N₀` is `N₀`, never `N`, and
# an invariant named `inv₀` must be recorded as such. ``[^\W\d]`` is "a word character that is not a
# digit" — Lean's own rule that an identifier does not start with one.
_NAME_RE = re.compile(r"\s*(?P<name>[^\W\d][\w'.]*)")
_WHITESPACE_RE = re.compile(r"\s+")

# The declaration spellings whose text *is* a proof: for those, replacing the seed's `sorry` with a
# real proof leaves the declaration faithful — it still states the same thing and what changed is the
# evidence for it. Every other change (a type, a `def`'s value, an added or missing declaration) is a
# rewrite a human made (plan D5, protocol §11 decision 5).
_PROOF_KINDS = ("theorem", "lemma")


@dataclass(frozen=True)
class Declaration:
    """One declaration a Lean file carries: `have` is local, so anything here is a human's doing.

    ``statement`` is the declaration as stated — its text up to the ``:=`` that introduces its value
    or proof — and ``text`` is the whole declaration, both with runs of whitespace collapsed: they are
    what the diff compares, so a proof the loop rewrote changes its own declaration and nothing else's.
    A ``theorem``/``lemma`` is compared by statement (the loop writes their proofs, never their
    claims); every other kind is compared by text, because a ``def``'s or an ``opaque``'s value *is*
    what the declaration means (plan D5).

    ``source`` is the same declaration exactly as it stands in the file, and ``lines`` its height. What
    must be *read as Lean* — whether a body still carries a hole (plan D15), or what its `where` clause
    is — uses ``source``, because collapsing whitespace moves a line comment's end: a ``--`` comment
    ahead of a declaration's `sorry` would take the rest of the collapsed line with it and hide the
    hole.
    """

    kind: str
    name: str
    statement: str
    text: str
    source: str
    lines: int


def declaration_matches(text: str) -> list[re.Match]:
    """The declarations a Lean text states, in order: one match per declaration, code only.

    A declaration begins where Lean's lexer would begin one, at any indentation, so a declaration
    nested in a `namespace`, a `section` or a `where` clause is a declaration too (ticket P1-1). What
    is *not* one is a spelling inside a comment or a string: ``harness.lean_lex`` skips those, so a
    commented-out declaration, or the word `def` in a docstring, is prose rather than a declaration the
    diff would report as a human's (plan D5).
    """
    matches: list[re.Match] = []
    index = 0
    while index < len(text):
        skipped = lean_lex.skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        match = _DECL_RE.match(text, index)
        if match is None:
            index += 1
            continue
        matches.append(match)
        index = match.end()
    return matches


def where_clause(text: str) -> str:
    """A declaration's `where` clause as written, or ``""`` when it has none.

    The clause is the declaration's own local machinery — ``where`` and every helper under it — and it
    follows the ``:=`` that introduces the declaration's value or proof. A declaration with no body
    introducer has none: a `structure`/`inductive`'s own ``where`` opens its fields or constructors,
    which is the declaration's statement, not machinery beside it. Only a `where` in *code* counts: a
    `where` in a comment or a string is text (plan D15, ticket P1-3).

    A run's tactics are spliced into the declaration's ``by`` block and cannot introduce a clause, so
    any difference between the seed's clause and the artifact's is a human's — which is what the
    faithful-closure test compares, rather than ignoring everything after the statement.
    """
    index = _body_introducer(text)
    if index is None:
        return ""
    while index < len(text):
        skipped = lean_lex.skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        token = lean_lex.identifier_at(text, index)
        if token is None:
            index += 1
        elif token == "where":
            return _WHITESPACE_RE.sub(" ", text[index:]).strip()
        else:
            index += len(token)
    return ""


def _body_introducer(text: str) -> int | None:
    """Where a declaration's value or proof begins: the ``:=`` that introduces it, or ``None``.

    The first ``:=`` in the text is not always the declaration's own. A ``let`` in a signature binds
    with one (``theorem t : let y := 1; y = 1``), and a ``:=`` inside a comment or a string literal is
    text, not syntax. So the scan skips non-code (``harness.lean_lex``), tracks bracket depth — a
    parenthesised ``let`` or a ``match`` arm is inside one — and consumes a ``let``/``letI`` binder's
    own ``:=`` as part of the signature, continuing after it. Cutting on the first ``:=`` regardless
    is what produced malformed fragments like ``theorem withLet : (let y`` (plan D15).
    """
    depth = 0
    binder_pending = False
    index = 0
    while index < len(text):
        skipped = lean_lex.skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        char = text[index]
        if char in "([{":
            depth += 1
            index += 1
        elif char in ")]}":
            depth = max(depth - 1, 0)
            index += 1
        elif depth == 0 and text.startswith(":=", index):
            if binder_pending:
                binder_pending = False  # a `let`'s binder, not the declaration's body
            else:
                return index
            index += 2
        elif depth == 0 and (token := lean_lex.identifier_at(text, index)) in ("let", "letI"):
            binder_pending = True
            index += len(token)
        elif (token := lean_lex.identifier_at(text, index)) is not None:
            index += len(token)
        else:
            index += 1
    return None


def _statement_of(body: str) -> str:
    """A declaration's text up to the ``:=`` that introduces its value or proof (plan D5/D15).

    With no body introducer the whole text is the statement: a declaration whose value is missing is
    shown as it stands rather than cut into a fragment (plan D15).
    """
    cut = _body_introducer(body)
    return _WHITESPACE_RE.sub(" ", body[:cut] if cut is not None else body).strip()


def parse_declarations(text: str) -> list[Declaration]:
    """The declarations a Lean artifact carries, in order (plan D5, ticket P1-1).

    A declaration runs to the next one, so its ``text`` is everything it carries at that level: a proof
    the loop rewrote changes its own declaration's text and nothing else's, and loop tactics cannot
    introduce a declaration (``have`` is local). A declaration at any indentation is a declaration — a
    `namespace`'s, a `section`'s, or how a human appends a helper — and a declaration's `where` clause
    stays part of that declaration, which is what its ``source`` shows.
    """
    matches = declaration_matches(text)
    declarations: list[Declaration] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        body = text[match.start() : end]
        name_match = _NAME_RE.match(match.group("rest"))
        declarations.append(
            Declaration(
                kind=match.group("kind"),
                name=name_match.group("name") if name_match else "",
                statement=_statement_of(body),
                text=_WHITESPACE_RE.sub(" ", body).strip(),
                source=body,
                lines=body.count("\n") + (0 if body.endswith("\n") else 1),
            )
        )
    return declarations


# The declaration spellings whose text a run is shown as a *statement*: the proof declarations, plus
# `example` (an unnamed claim whose body is human work, and which the assisted diff must keep treating
# as an ordinary declaration) and `axiom` (a statement with no body at all). What a run is shown of
# them is the declaration up to its body, and one whose body is a hole is not shown at all (plan
# D14/D15). An import carrying an `axiom` is refused before anything runs (``harness.route_b``, plan
# D13), so the spelling is here for the excerpt's own contract rather than for a run.
_STATEMENT_KINDS = _PROOF_KINDS + ("example", "axiom")

# The spellings of a hole in a declaration's own text (plan D15): the `sorry` family, which is what a
# proof that is not finished carries. `axiom` is not here — an axiom is a declaration, not a hole in a
# body — and `harness.lean_repl.UNCLOSED_TOKENS` is the artifact-level set that includes it.
_HOLE_TOKENS = frozenset({"sorry", "sorryAx", "admit", "Admitted"})


def incomplete_body(text: str) -> bool:
    """Whether a declaration still carries a hole in its value or proof (plan D15).

    ``sorry`` in any spelling, ``admit``, or Lean's synthetic ``?name``: the hole spellings read with
    the same lexer the artifact-level count uses (``harness.lean_lex``), so a ``sorry`` in the
    declaration's own prose is prose and not a hole. A declaration whose value is incomplete is not a
    statement the run may show as established, and its presence is human work (protocol §11
    decision 5).
    """
    return lean_lex.count_holes(text, _HOLE_TOKENS) > 0


def excerpt_of(text: str) -> tuple[str, list[dict]]:
    """A Lean module reduced to the specification it states, with an account of what it showed.

    Each non-proof declaration is kept as written — a ``def``'s value is its meaning, and an
    ``instance``'s fields come with it — while a ``theorem``/``lemma``/``example``/``axiom`` is cut at
    the ``:=`` that introduces its proof, or shown as it stands when it has none: what a run is shown
    of an imported module is what that module *states*, never a proof body (plan D14). A proof
    declaration whose body is still a hole (``incomplete_body``) is not shown at all — a statement
    nobody proved is not part of a specification, it is the artifact of a run that did not finish — and
    the account says so, which is what marks the run ``assisted`` (plan D15). The module header, which
    precedes every declaration, states no part of the specification and is dropped.

    The second element is the inventory the row records: one entry per declaration, ``shown`` being
    ``"body"``, ``"statement"`` or ``None``, so "no helper-lemma statement was shown" is a fact a
    reader derives from the row rather than a promise the row makes (plan D15, P1-2).
    """
    parts: list[str] = []
    shown: list[dict] = []
    for declaration in parse_declarations(text):
        entry = {"name": declaration.name, "kind": declaration.kind, "lines": declaration.lines}
        if declaration.kind in _STATEMENT_KINDS:
            if incomplete_body(declaration.source):
                shown.append(
                    {**entry, "shown": None, "reason": "its proof is incomplete, so nothing is established"}
                )
                continue
            # An `axiom`, and a declaration whose body is missing altogether, have no `:=` to cut at:
            # what stands is the statement, never a fragment (plan D15).
            cut = _body_introducer(declaration.source)
            statement = declaration.source if cut is None else declaration.source[:cut]
            parts.append(statement.strip("\n").rstrip())
            shown.append({**entry, "shown": "statement"})
            continue
        parts.append(declaration.source.strip("\n").rstrip())
        shown.append({**entry, "shown": "body"})
    return "\n\n".join(parts), shown


def specification_excerpt(text: str) -> str:
    """A Lean module reduced to the specification it states (plan D14) — the shown text alone.

    ``excerpt_of``'s first element: the query shape the harness had before the row started recording
    what a run was shown (plan D15). Callers that need the account use ``excerpt_of``.
    """
    return excerpt_of(text)[0]


def seed_work(seed_text: str) -> list[str]:
    """Human work inside a recorded seed beyond the statement under test (plan D15, protocol §11
    decision 5).

    The record itself is ground truth — a seed's definitions are what the model is shown (plan D14), so
    their *presence* is not human work; anything a human added to the committed seed after it was
    recorded is caught against the record instead (``harness.route_b``'s baseline diff, any kind of
    declaration). What this reports is the work that is inside the record and still a human's beyond the
    goal: another ``theorem``/``lemma`` (a helper lemma or a supplied invariant, proved or not), an
    ``example``, an ``axiom``, or proof machinery parked in a declaration's `where` clause. Each is a
    reason the run is ``assisted``; the goal is not, because its ``sorry`` is the placeholder the run
    closes.
    """
    reasons: list[str] = []
    goal_seen = False
    for declaration in parse_declarations(seed_text):
        label = declaration.name or f"<{declaration.kind}>"
        if where_clause(declaration.source):
            # A `where` clause carries helpers, and a run's tactics cannot write one: it is machinery a
            # human put beside the declaration, and the model is shown it verbatim (ticket P1-3).
            reasons.append(
                f"{declaration.kind} {label} in the seed carries a `where` clause: local proof "
                "machinery the model was shown"
            )
        elif declaration.kind == "axiom":
            reasons.append(f"axiom {label} in the seed: an unproved statement the model was shown")
        elif declaration.kind in _PROOF_KINDS:
            if incomplete_body(declaration.source) and not goal_seen:
                goal_seen = True  # the statement under test: the one hole the run is closing
            else:
                reasons.append(
                    f"{declaration.kind} {label} in the seed: human work beyond the statement under test"
                )
        elif declaration.kind == "example":
            reasons.append("example in the seed: an unnamed claim and its proof the model was shown")
    return reasons


def detect_assisted(older: str, newer: str, *, human: bool = True) -> dict:
    """Diff two texts' declarations — a seed against an artifact, or a record against a seed (D5/D19).

    Returns ``assisted`` — true iff ``newer`` gained a declaration, lost one, or changed one's statement
    or value, subject to ``human`` — and the three lists naming what did it: ``auxiliary_invariants``
    (the declarations ``older`` did not have, with their line counts), ``changed_declarations`` and
    ``missing_declarations``.

    ``human`` is the **provenance** of an *added* declaration (plan D19), and it is the experiment's
    central distinction:

    * ``human=True`` — the additions are a human's work: an invariant written into a committed seed
      beyond its goal, or a helper someone added by hand. The run is ``assisted``.
    * ``human=False`` — the additions are the loop's own: a helper lemma or a strengthened statement the
      *model* guessed, and which the loop proved as part of closing the artifact. The run is **not**
      assisted, and the additions are still listed in ``auxiliary_invariants`` so a reader can see what
      the model introduced and how large it was (§4.9).

    A *changed* or *missing* declaration is a rewrite rather than a guess, and is assisted either way:
    loop tactics are spliced into a proof body and cannot restate a top-level declaration, so only a
    human can have done it (protocol §11 decision 5). The other change that is *not* a human's, and
    leaves ``assisted`` false even under ``human=True``, is a ``theorem``/``lemma`` whose statement is
    untouched and whose ``sorry`` became a proof: that is the loop doing its job.
    """
    seed = parse_declarations(older)
    artifact = parse_declarations(newer)

    def key(declaration: Declaration) -> tuple[str, str]:
        """A declaration's identity: its name, or its statement when it is anonymous."""
        return ("name", declaration.name) if declaration.name else ("statement", declaration.statement)

    def label(declaration: Declaration) -> str:
        return declaration.name or f"<{declaration.kind}>"

    seeded = {key(declaration): declaration for declaration in seed}
    present = {key(declaration): declaration for declaration in artifact}

    changed: list[str] = []
    missing: list[str] = []
    for declaration in seed:
        found = present.get(key(declaration))
        if found is None:
            missing.append(label(declaration))
        elif found.text != declaration.text and not _faithful(declaration, found):
            changed.append(label(declaration))

    extra = [declaration for declaration in artifact if key(declaration) not in seeded]
    auxiliary = [label(declaration) for declaration in extra]
    return {
        "assisted": bool(changed or missing or (human and extra)),
        "auxiliary_invariants": auxiliary,
        "auxiliary_invariant_lines": {
            label: declaration.lines for label, declaration in zip(auxiliary, extra)
        },
        "changed_declarations": changed,
        "missing_declarations": missing,
    }


def _faithful(seed: Declaration, artifact: Declaration) -> bool:
    """Whether what changed is only a proof replacing the seed's ``sorry`` (plan D5).

    The claim has to be the same one, down to the kind: a changed statement is a rewritten goal, and a
    ``theorem`` turned into a ``def`` is not a proof of anything.

    The `where` clause has to be the same too. It is written *without* a declaration keyword
    (``where\\n  helper : T := …``), so it is not a declaration the diff can compare by name, and it sits
    inside this declaration's slice where a proof is free to change: leaving it out of the comparison
    let a human park a helper beside the goal — or, at promotion, into the committed seed — with the run
    still reading ``assisted: false`` (ticket P1-3). Tactic text cannot introduce one, so any difference
    here is human work.
    """
    return (
        seed.kind in _PROOF_KINDS
        and artifact.kind == seed.kind
        and artifact.statement == seed.statement
        and where_clause(artifact.source) == where_clause(seed.source)
    )


def arm_order(arms: str) -> list[str]:
    """The arms a run fields, in the order they take their turns (plan D16).

    The race opens with the proof arm: D16's even/odd numbering counts turns from zero, so the first
    turn — the one a reader of the row sees as turn 1 — is the proof arm's.
    """
    return [ARM_PROOF] if arms == ARM_PROOF else [ARM_PROOF, ARM_REFUTATION]


def arm_of(turn: int, arms: str) -> str:
    """Which arm takes turn ``turn`` (1-based) — the proof arm on odd turns, refutation on even.

    Alternating is what makes the arms a race rather than two sequential searches: every turn the
    refutation arm is the one that acts, the proof arm's goal state is untouched, and the shared pool
    pays for whichever arm moved.
    """
    if arms == ARM_PROOF:
        return ARM_PROOF
    return ARM_PROOF if turn % 2 else ARM_REFUTATION


def _arm_totals(arms: str) -> dict:
    """The per-arm accounting a row starts with: nothing spent (plan D16).

    One entry per arm the run fields. A turn is billed to the arm that took it, so the row shows both
    arms' totals — what each spent, and what the other was doing when the race ended. The refutation
    arm's entry also carries what it did: the commands it proposed, the ones the prover rejected, and
    the witness it was accepted on.
    """
    totals: dict = {}
    for arm in arm_order(arms):
        totals[arm] = {
            "turns": 0,
            "empty_turns": 0,
            "input_tokens": 0,
            "output_tokens": 0,
            "cached_input_tokens": 0,
            "cost_usd": 0.0,
            "provider_retries": 0,
        }
        if arm == ARM_REFUTATION:
            totals[arm].update({"commands": [], "rejections": [], "witness": None})
    return totals


def _bill(totals: dict, before: dict, after: dict) -> None:
    """Add a call's usage to the arm that made it (plan D16): tokens, dollars and retries.

    ``usage()`` is cumulative over the session — one shared pool — so what a call cost is what the
    counters gained between the reading before it and the reading after it. The readings are the same
    ones the pool's own budget checks use, so the per-arm parts sum to the row's totals.

    The *turn count* is not added here: a call that never produced a proposal is not a billed turn
    (D12), and a provider failure still spends its retries under the arm that made it. The loop counts
    a turn where it counts one for the row, so the parts stay equal to the whole.
    """
    totals["input_tokens"] += int(after.get("input", 0)) - int(before.get("input", 0))
    totals["output_tokens"] += int(after.get("output", 0)) - int(before.get("output", 0))
    totals["cached_input_tokens"] += int(after.get("cached_input", 0)) - int(
        before.get("cached_input", 0)
    )
    totals["cost_usd"] += float(after.get("cost_usd", 0.0)) - float(before.get("cost_usd", 0.0))
    totals["provider_retries"] += int(after.get("provider_retries", 0)) - int(
        before.get("provider_retries", 0)
    )


def _new_refusals(prover: Prover, before: Sequence[str]) -> str | None:
    """What the prover said about the step that just ran, if it said anything new (plan D14).

    Only the driver knows which of the loop's proposals it refused and why: it records the repl's own
    reason, which is read here so the next turn can say what was refused instead of leaving the model
    to infer it from a goal state that did not move.
    """
    refused = list(getattr(prover, "failures", ()) or ())
    return refused[-1] if len(refused) > len(before) else None


def _propose(model: Model, arm: str, goals: Sequence[str], history: Sequence[HistoryEntry]) -> str:
    """The arm's proposal: a tactic for the proof arm, a Lean command for the refutation arm (D16)."""
    if arm == ARM_PROOF:
        return model.propose(goals, history)
    return model.refute(goals, history)


def _exhausted(
    usage: dict, elapsed_s: float, cap_s: float, cap_usd: float, cap_tokens: int | None
) -> str | None:
    """The pool a run has exhausted, or ``None`` while it may continue (plans D11/D16).

    One shared pool for the whole race: wall-clock, then dollars, then tokens, which is the order the
    row's ``budget_exceeded`` names when more than one has bound. The check is *between* turns, never a
    hard interrupt of one, so a turn that overshoots the cap is recorded honestly in ``wall_clock_s``.
    """
    if elapsed_s > cap_s:
        return "wall_clock"
    if usage.get("cost_usd", 0.0) > cap_usd:
        return "usd"
    if cap_tokens is not None and usage.get("input", 0) + usage.get("output", 0) > cap_tokens:
        return "tokens"
    return None


def _automation_pass(prover: Prover) -> str | None:
    """Try the cheap automation tactics on the goal, and name the one that closed it (plan D19).

    Returns ``None`` when none of them closed the goal, having left the proof state where it was — the
    pass holds only tactics that close or leave the goal alone, so an attempt that fails costs nothing
    but the call. The closing tactic is the driver's to record in the artifact like any other applied
    step, and the loop records *which* one closed it, because §5's vacuousness guard reads that: a goal
    automation closed needed no induction from the model.
    """
    for tactic in AUTOMATION_TACTICS:
        prover.apply(tactic)
        if prover.unclosed() == 0:
            return tactic
    return None


def mutant_outcome(outcome: str) -> str | None:
    """How a mutant run ended (protocol §5, plan D7).

    ``"fail_to_close"`` is the expected observation: the statement is false, so the loop cannot close
    it — and the repl's tactic channel cannot run ``#eval``/``#reduce`` (they parse as tactics and
    error), so a counterexample was never exhibited and the row claims none. ``"refuted"`` is the other
    way a mutant run ends as predicted (plan D16): the refutation arm produced a machine-checked witness,
    which is the informative success a negative control is for. ``"closed"`` is the rig defect — the loop
    reported the false statement closed — which ``run_loop`` records as an ``error`` row rather than
    raising, so the observation survives. ``None`` is a run that ended without a verdict on the mutant:
    it stopped for a reason its own ``error`` names, and nothing is claimed about the statement.
    """
    if outcome == "success":
        return "closed"
    if outcome == "refuted":
        return "refuted"
    if outcome == "error":
        return None
    return "fail_to_close"


def _ms(seconds: float) -> int:
    """A duration in whole milliseconds — the resolution Route A records (``round(…, 3)``)."""
    return int(round(seconds * 1000.0))


def run_loop(
    prover: Prover,
    model: Model,
    *,
    task: str = "",
    param_N: int | None = None,
    tier: int = 2,
    repetition: int = 1,
    cap_s: float = 7200.0,
    cap_usd: float = 50.0,
    cap_tokens: int | None = None,
    mutant: bool = False,
    seed_text: str = "",
    artifact_path: Path | str | None = None,
    assisted_before: Sequence[str] = (),
    seed_diff_before: dict | None = None,
    arms: str = ARM_PROOF,
    setup: dict | None = None,
    exploratory: bool = False,
    clock=time.monotonic,
) -> dict:
    """Run the closure loop until the proof closes or a budget binds, and return the row.

    ``tier`` is 2 for the general theorem and 1 for the ``N₀`` corollary (plan D4). ``mutant`` marks a
    run of a statement that is false, whose ``outcome`` must not be ``success`` and whose row records
    the observation: ``fail_to_close`` when the loop could not close it, and — when it did close it,
    which is a rig defect — an ``error`` naming the defect and ``mutant: "closed"`` (ticket P2-3).
    ``artifact_path`` is the file the driver wrote: it is read after the loop and diffed against
    ``seed_text``, so the row says what the run changed (plan D5).

    ``assisted_before`` is human work the run carries *before* any tactic, which the artifact diff
    cannot see because it is in the seed as the loop received it: the committed seed differing from its
    recorded baseline, or the prompt withholding a declaration that was not established (plan D15).
    Each string is a reason; any reason makes the run ``assisted``, and the reasons are recorded
    beside the diff's own lists, so a reader sees which made it assisted. ``seed_diff_before`` is that
    same human work in ``detect_assisted``'s shape — the committed seed diffed against its record, so
    an added or changed declaration of *any* kind is named — and its three lists are merged into the
    row's, which is why an invariant a human added to the committed seed appears in
    ``auxiliary_invariants`` rather than only in a reason string (ticket P1-2).

    ``arms`` is the race a run fields (plan D16): ``"proof"`` (the proof arm alone, the pre-D16
    behaviour) or ``"proof+refutation"``, which alternates the two arms under one shared pool —
    the proof arm on odd turns, the refutation arm on even ones, so the race opens with the proof arm.
    Each turn is billed to the arm that took it, and the row's ``arms`` carries both accounting, so a
    reader sees what the winner spent and what the loser was doing. A refutation ends the race as
    ``refuted`` — a machine-checked witness, never a model claim (the prover's ``cmd`` decides) — and a
    witness against a statement the caller does not declare false is a rig defect recorded as
    ``error`` / ``rig_refutation``, the mirror of a mutant that closed. ``setup`` is the configuration
    that produced the row (plan D17; the model, thinking level, prompt and arm configuration), the
    loop adding the arm keys it owns, and ``exploratory`` marks a run whose setup is not the headline
    one, so exploratory rows are never pooled with it.

    Before the race, each configured arm is asked to **plan** (plan D19) — once per arm, recorded
    verbatim in ``plan`` — and before every proof-arm turn the loop tries the cheap automation pass
    (plan D19), recording ``proof.automation_closed`` when it finishes the goal itself, so a close the
    model did not earn is never read as the model's. Both are turns against the same pool: an empty
    plan or tactic is consumed, billed and re-asked (plan D11), never an abort.

    Every way a run can end returns a row: a closed proof (``success``, by the model or by
    ``automation_closed``), a binding budget (``timeout``), a machine-checked refutation (``refuted``,
    the mutant's expected outcome), a provider failure (``error`` / ``provider_failure``, D12), a prover
    that could not load the seed or run a step (``error`` / ``prover_failure``), a seed with no goal
    left to close (``error`` / ``seed_already_closed``, D15), a mutant that closed (``error`` /
    ``mutant_closed``), a witness against a statement that holds (``error`` / ``rig_refutation``, D16),
    and an artifact that cannot be read (``error`` / ``artifact_unreadable``, with the seed-diff
    unknown). Nothing in this function raises on a run that spent budget; an ``arms`` value this loop
    does not implement, or an arm whose ports are missing, is refused before the first turn, because no
    run happened.
    """
    if arms not in ARMS_CONFIGURATIONS:
        raise ValueError(f"arms must be one of {ARMS_CONFIGURATIONS}, not {arms!r}")
    started = clock()
    error: dict | None = None
    try:
        prover.start()
    except ProverError as failure:
        # The seed never loaded, or the repl died loading it: no tactic was taken and the run is over
        # before a turn, but the load's wall-clock was spent and the row says so. The kind is the
        # driver's own (plan D15): a seed with no goal to close is not a prover that died mid-run.
        error = {"kind": failure.kind, "message": failure.message}
    # The port's start() returns once the prover answers, so this is the instant its first goal state
    # is ready: everything before it is environment/olean load, everything after is proof search. A
    # failed start is the wall-clock the load spent before failing — the startup the run really had,
    # never a reported zero.
    startup_ms = _ms(clock() - started)

    history: list[HistoryEntry] = []
    turns = 0
    empty_turns = 0
    budget_exceeded: str | None = None
    outcome = "error"
    fallback = False
    totals = _arm_totals(arms)
    automation_closed: str | None = None
    # The planning turn (plan D19): one per arm, before that arm acts, recorded verbatim. A model port
    # without a `plan` turn is a run without one — the entries stay None rather than the harness
    # inventing a plan it never received — and the phase spends from the run's own pool, so a model that
    # never plans ends the run on the budget instead of looping forever.
    plans: dict[str, str | None] = {arm: None for arm in arm_order(arms)}
    if callable(getattr(model, "plan", None)):
        for plan_arm in arm_order(arms):
            while error is None:
                usage = model.usage()
                fallback = fallback or bool(usage.get("is_fallback", False))
                budget_exceeded = _exhausted(
                    usage, clock() - started, cap_s, cap_usd, cap_tokens
                )
                if budget_exceeded is not None:
                    break
                try:
                    plan = model.plan(plan_arm, prover.goals(), history)
                except ProviderError as failure:
                    _bill(totals[plan_arm], usage, model.usage())
                    error = {
                        "kind": "provider_failure",
                        "status": failure.status,
                        "message": failure.message,
                    }
                    outcome = "error"
                    break
                turns += 1
                totals[plan_arm]["turns"] += 1
                _bill(totals[plan_arm], usage, model.usage())
                if plan:
                    plans[plan_arm] = plan
                    break
                # An empty plan is the empty-reply path (plan D11) on the planning turn: counted,
                # billed and re-asked with the nudge, never an abort.
                empty_turns += 1
                totals[plan_arm]["empty_turns"] += 1
                history.append(("", prover.goals(), EMPTY_PLAN_NUDGE))
            if error is not None or budget_exceeded is not None:
                break
    # A driver failure is what ends the loop when it happens; the row below carries the turns, tokens
    # and dollars spent up to it (ticket P1).
    while error is None and budget_exceeded is None:
        unclosed = prover.unclosed()
        if unclosed == 0:
            outcome = "success"
            break

        usage = model.usage()
        fallback = fallback or bool(usage.get("is_fallback", False))
        budget_exceeded = _exhausted(usage, clock() - started, cap_s, cap_usd, cap_tokens)
        if budget_exceeded is not None:
            break

        # The race alternates (plan D16): the proof arm on odd turns, the refutation arm on even ones,
        # so the arm that acts is a function of the turn number and each is billed for its own.
        arm = arm_of(turns + 1, arms)
        if arm == ARM_PROOF:
            # The cheap automation pass runs before the model is asked (plan D19), and closes the run
            # when it can: the goal is closed, no model turn is spent, and `automation_closed` names the
            # tactic so §5's vacuousness guard can see that no induction was involved. A driver that
            # cannot run a step at all is the same failure here as anywhere else: an outcome, not a lost
            # row (ticket P1).
            try:
                automation_closed = _automation_pass(prover)
            except ProverError as failure:
                error = {"kind": failure.kind, "message": failure.message}
                break
            if automation_closed is not None:
                outcome = "success"
                break
        elif not callable(getattr(model, "refute", None)) or not callable(
            getattr(prover, "cmd", None)
        ):
            # The refutation arm's turn has come and the ports behind it are not there: a run that
            # cannot propose a witness or have one checked is not a race, and saying so is this row's
            # business rather than a traceback's — the arm was configured, so the row records why it
            # could not be fielded and the exit code says the run is not a result.
            missing = "Model.refute()" if not callable(getattr(model, "refute", None)) else "Prover.cmd()"
            outcome = "error"
            error = {
                "kind": "arm_unavailable",
                "message": (
                    f"the {arms} race needs {missing}: the refutation arm has no way to "
                    f"{'propose' if missing.startswith('Model') else 'have a witness machine-checked in'} "
                    "the turn it is due, and no witness can be claimed without it"
                ),
            }
            break
        try:
            proposal = _propose(model, arm, prover.goals(), history)
        except ProviderError as failure:
            # D12: a mid-run provider failure is an outcome carrying what was already spent — the
            # turns, tokens and dollars below — not an exception that loses the run's budget. The
            # attempt's own usage (a retry's tokens, if any) still belongs to the arm that made it.
            _bill(totals[arm], usage, model.usage())
            error = {"kind": "provider_failure", "status": failure.status, "message": failure.message}
            outcome = "error"
            break

        turns += 1
        totals[arm]["turns"] += 1
        spent = model.usage()
        _bill(totals[arm], usage, spent)
        if not proposal:
            # D11: an empty reply is a consumed, billed turn — counted and added to history — that the
            # loop re-asks instead of applying, with a nudge rather than the same prompt again. There
            # is no consecutive-empty abort: only a budget ends a run that never answers, so an
            # always-empty model is a `timeout` and the mutant's `fail_to_close` stays reachable.
            empty_turns += 1
            totals[arm]["empty_turns"] += 1
            history.append(("", prover.goals(), EMPTY_REPLY_NUDGE))
            continue
        before = list(getattr(prover, "failures", ()) or ())
        try:
            if arm == ARM_PROOF:
                prover.apply(proposal)
            else:
                verdict = prover.cmd(proposal)
        except ProverError as failure:
            # A step the driver could not run at all: the repl exceeded STEP_TIMEOUT_S, exited, or
            # answered outside the protocol. The turn above is counted — the model proposed it and the
            # provider billed it — and the run ends as an outcome from the prover's side, carrying what
            # was spent and leaving the partial artifact where it is, rather than a traceback that
            # loses the row (ticket P1; D12's rule, applied to the prover side of the port).
            error = {"kind": failure.kind, "message": failure.message}
            break

        if arm == ARM_REFUTATION:
            totals[arm]["commands"].append(proposal)
            if isinstance(verdict, dict) and verdict.get("refuted"):
                # The witness is the prover's, not the model's: `cmd` only reports a refutation it
                # machine-checked (plan D16), so the row can record it as a result.
                witness = {"command": proposal, "witness": verdict.get("witness")}
                totals[arm]["witness"] = witness
                if mutant:
                    outcome = "refuted"
                else:
                    # The mirror of a mutant that closed (protocol §5): the reference semantics says
                    # this statement holds, so a machine-checked witness against it is a rig defect —
                    # recorded loudly, never pooled as a result.
                    outcome = "error"
                    error = {"kind": "rig_refutation", "message": RIG_REFUTATION_MESSAGE, **witness}
                break
            # A refused command changes nothing, exactly as a refused tactic does: the goal state
            # stays, the next turn sees the same goals, and the reason travels with the history.
            totals[arm]["rejections"].append(proposal)
            refusal = _new_refusals(prover, before) or (
                verdict.get("reason") if isinstance(verdict, dict) else None
            )
            history.append((proposal, prover.goals(), refusal))
            continue
        # A tactic the prover refused changes nothing, and the driver is the only one that knows which
        # of the loop's proposals it refused and why: it records the repl's own reason, which is read
        # here so the next turn can say what was refused (plan D14) instead of leaving the model to
        # infer it from a goal state that did not move.
        history.append((proposal, prover.goals(), _new_refusals(prover, before)))

    wall_ms = _ms(clock() - started)
    usage = model.usage()
    fallback = fallback or bool(usage.get("is_fallback", False))
    if budget_exceeded is not None:
        outcome = "timeout"

    # A mutant run that closed its false statement is a rig defect. The observation is what the
    # negative control exists to produce, so the row records it — the outcome becomes `error` with the
    # defect named, and the observation is kept in `mutant` below — rather than an exception that loses
    # the row, and with it every turn, token and dollar the broken run spent (ticket P2-3, protocol §5).
    mutant_observation = mutant_outcome(outcome) if mutant else None
    if mutant_observation == "closed":
        outcome = "error"
        error = {"kind": "mutant_closed", "message": MUTANT_CLOSED_MESSAGE}

    # proof_s is the wall-clock less startup, so the two intervals reconstruct the total exactly.
    startup_s = startup_ms / 1000.0
    proof_s = (wall_ms - startup_ms) / 1000.0
    wall_clock_s = startup_s + proof_s
    # What the artifact is diffed against is read here, and a read that fails is recorded like any
    # other failure to produce a verdict: the row is written with the seed-diff *unknown*
    # (`assisted: None`, never `False`, which would claim the run supplied nothing on no evidence),
    # and the error names the artifact (planner: kind `artifact_unreadable`). A run that already ended
    # in error keeps that error: it is the cause, and this read is downstream of it.
    if artifact_path is not None:
        try:
            artifact_text = Path(artifact_path).read_text()
        except (OSError, UnicodeDecodeError) as failure:
            seed_diff = {
                "assisted": None,
                "auxiliary_invariants": [],
                "auxiliary_invariant_lines": {},
                "changed_declarations": [],
                "missing_declarations": [],
            }
            if error is None:
                outcome = "error"
                error = {
                    "kind": "artifact_unreadable",
                    "message": f"could not read {artifact_path} to diff it against the seed: {failure}",
                }
        else:
            # The artifact is what the loop produced from this seed: a declaration it added is the
            # model's own helper — a guess it then proved — so `human=False` keeps the run unassisted
            # while still listing what it introduced (plan D19, §4.9).
            seed_diff = detect_assisted(seed_text, artifact_text, human=False)
    else:
        seed_diff = {
            "assisted": False,
            "auxiliary_invariants": [],
            "auxiliary_invariant_lines": {},
            "changed_declarations": [],
            "missing_declarations": [],
        }

    # The steps the prover applied — what the artifact carries — never every proposal: a step the
    # driver refused never entered the proof, and only the prover can tell the two apart (plan D7). A
    # prover that reports neither is answered by the loop's own history, which is what its stubs are.
    applied = getattr(prover, "tactics", None)
    tactics = (
        list(applied)
        if applied is not None
        else [tactic for tactic, _, _ in history if tactic]  # an empty reply was never applied
    )
    failures = list(getattr(prover, "failures", ()) or ())

    # Human work the run carried before the first tactic is assisted even when the artifact diff sees
    # none of it — that diff compares the artifact against the seed the loop received, so a seed-borne
    # invariant is in both (plan D15, P1-2). Two sources, kept distinguishable: the reasons as strings,
    # and the committed seed's own diff against its record, whose lists merge into the row's so an added
    # or changed declaration is named where a reader looks for it. A run with either is assisted
    # whatever the artifact diff said, including when the artifact could not be read at all (`None`);
    # with neither, the artifact diff's own verdict stands, and `None` stays `None` rather than
    # silently reading as "no human work".
    assisted_before_diff = seed_diff_before or {
        "assisted": False,
        "auxiliary_invariants": [],
        "auxiliary_invariant_lines": {},
        "changed_declarations": [],
        "missing_declarations": [],
    }
    human_work = bool(assisted_before) or bool(assisted_before_diff["assisted"])

    def merged(key: str) -> list:
        """The two diffs' entries for one list, each named once, in the order they were found."""
        labels: list = []
        for label in (*seed_diff[key], *assisted_before_diff[key]):
            if label not in labels:
                labels.append(label)
        return labels

    # What each arm did with what it spent (plan D16): the proof arm's applied steps are the driver's
    # own list — the artifact's script — and the refutation arm's commands, rejections and witness were
    # recorded as it went. Together they are what the row shows of the race: the winner's result and
    # what the other arm was doing when it ended.
    if ARM_PROOF in totals:
        totals[ARM_PROOF]["tactics"] = list(tactics)

    return {
        "task": task,
        "route": "proof",
        "param_N": param_N,
        "tier": tier,
        "repetition": repetition,
        "outcome": outcome,
        "budget_exceeded": budget_exceeded,
        "error": error,
        "wall_clock_s": wall_clock_s,
        "startup_s": startup_s,
        "proof_s": proof_s,
        "compute_usd": compute_cost_usd(wall_clock_s),
        "mutant": mutant_observation,
        "arms": {"order": arm_order(arms), **totals},
        # The plans the arms stated before they acted (plan D19), verbatim: evidence of how the model
        # reasoned, one entry per configured arm, `None` for an arm whose plan the port could not be
        # asked for.
        "plan": plans,
        # The setup that produced the row (plan D17): the caller's configuration — model, thinking
        # level, prompt, refutation templates — with the arm configuration the loop owns overriding it,
        # so an iterated run is distinguishable from the one before it. `exploratory` marks a run whose
        # setup is not the headline one, which is what keeps such rows out of the headline numbers.
        "setup": {**(setup or {}), "arms": arms, "order": arm_order(arms)},
        "exploratory": bool(exploratory),
        "assisted": True if human_work else seed_diff["assisted"],
        "assisted_before": list(assisted_before),
        "auxiliary_invariants": merged("auxiliary_invariants"),
        "auxiliary_invariant_lines": {
            **seed_diff["auxiliary_invariant_lines"],
            **assisted_before_diff["auxiliary_invariant_lines"],
        },
        "changed_declarations": merged("changed_declarations"),
        "missing_declarations": merged("missing_declarations"),
        # What the prompt was assembled from, as the client that assembled it reports (plan D14): the
        # sections — the specification, the goals, the tactic history and the refusals. What those
        # sections *showed* is evidence ``harness.route_b`` adds from the excerpt's own inventory
        # (``prompt.shown``, plan D15): the row no longer asserts what it withheld (P1-2). A model port
        # that reports no composition leaves it empty rather than the loop inventing one.
        "prompt": usage.get("prompt") or {},
        "resolvedModelIsFallback": fallback,
        "cost_usd": usage.get("cost_usd", 0.0),
        # §6: both components the row reports, each with its own basis — the token card the dollars
        # were summed from, and the host rate the compute seconds were priced at.
        "cost_basis": f"{usage.get('cost_basis') or COST_BASIS}; {compute_basis(wall_clock_s)}",
        "proof": {
            "turns": turns,
            "unclosed_goals": prover.unclosed(),
            "empty_turns": empty_turns,
            # The tactic the cheap automation pass closed the goal with, or `None` when the model did
            # the work (plan D19). §5's vacuousness guard reads this: a goal automation closed needed
            # no induction, and the row says so rather than leaving a reader to infer it from a proof
            # script that happens to be one line.
            "automation_closed": automation_closed,
            "input_tokens": usage.get("input", 0),
            "output_tokens": usage.get("output", 0),
            "cached_input_tokens": usage.get("cached_input", 0),
            # Re-attempts after a transient provider failure (D12): they spend wall-clock inside the
            # measured run, so the count is part of the row even though the retries are not billed.
            "provider_retries": usage.get("provider_retries", 0),
            "model": usage.get("model"),
            "thinking": usage.get("thinking"),
            "temperature": usage.get("temperature"),
            "max_tokens": usage.get("max_tokens"),
            "resolved_model": usage.get("resolved_model"),
            "tactics": tactics,
            "failures": failures,
        },
        "artifacts": {},
    }
