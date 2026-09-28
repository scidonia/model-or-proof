"""Lean 4 lexical scanning: which characters are code and which are text (plan D6/D13/D15).

Two consumers read Lean source without a Lean process: the artifact's unclosed-goal count
(``harness.lean_repl.count_unclosed``, protocol §8) and the declaration parser and prompt excerpt
(``harness.closure``). Both must read the text the way Lean's lexer does, or they read the seed's own
prose as syntax — the committed seeds explain their placeholder in a comment, and a ``sorry`` or a
``:=`` inside a comment, a string, a character literal or a ``« … »`` quoted identifier is text, not
code. So the delimiters live here, once, and each consumer expresses its own policy over them.

The regions are the reference manual's for this toolchain (``4.35.0-rc3``, §5.2.2 comments, §5.2.3
identifiers). Delimiters take precedence wherever they meet: ``--`` inside a string is string content
and ``"`` inside a comment is comment text.
"""

from __future__ import annotations

from typing import Iterable


def is_identifier_char(char: str) -> bool:
    """Whether ``char`` can appear in a Lean identifier after its first character.

    The continuation set is the reference manual's (§5.2.3): letters, letter-like characters,
    ``_``, ``!``, ``?``, subscripts, and ``'``.
    """
    return char.isalnum() or char in ("_", "'", "!", "?")


def identifier_at(text: str, index: int) -> str | None:
    """The identifier token beginning at ``index``, or ``None`` when no token begins there.

    A token only begins where Lean's lexer would start one, so an identifier spelled inside a longer
    one is never read as a token of its own (``xsorry`` is one name, not a hole).
    """
    if not (text[index].isalpha() or text[index] == "_"):
        return None
    if index and is_identifier_char(text[index - 1]):
        return None
    end = index + 1
    while end < len(text) and is_identifier_char(text[end]):
        end += 1
    return text[index:end]


def skip_comment(text: str, start: int) -> int:
    """One past the comment opening at ``start`` — ``-- …`` to end of line, or ``/- … -/``.

    Lean's block comments nest, so the depth is counted rather than the first ``-/`` closing the
    comment. A comment cannot open inside another comment or a string, so the caller only reaches
    this at a real ``--`` or ``/-``; ``--`` inside a block comment is comment text, not a nested
    line comment, and the depth loop never looks for it.
    """
    if text.startswith("--", start):
        newline = text.find("\n", start)
        return len(text) if newline < 0 else newline + 1
    depth = 1
    index = start + 2
    while index < len(text) and depth:
        if text.startswith("/-", index):
            depth += 1
            index += 2
        elif text.startswith("-/", index):
            depth -= 1
            index += 2
        else:
            index += 1
    return index


def skip_string(text: str, start: int) -> int:
    """One past the string literal opening at ``start`` (or past the text, if it never closes).

    Lean string literals run to the next unescaped ``"`` and may span lines, so ``--`` and ``/-``
    inside one are string content and a ``\\"`` does not end it.
    """
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
        elif char == '"':
            return index + 1
        else:
            index += 1
    return len(text)


def char_literal_end(text: str, start: int) -> int | None:
    """One past the character literal opening at ``start``, or ``None`` when it is not one.

    ``'`` also continues an identifier (``foo'``), so a literal is recognised only where one can
    begin — after a character that cannot be inside an identifier — and only when it closes within
    the literal's own length. The quote in ``'"'`` is why this exists: read as code it would open a
    string that swallows the rest of the file, and a real ``sorry`` in it with it.
    """
    previous = text[start - 1] if start else ""
    if is_identifier_char(previous) or previous == "«":
        return None
    cursor = start + 1
    if cursor >= len(text) or text[cursor] == "'":
        return None
    if text[cursor] == "\\":
        cursor += 2  # the escape's own character (``\n``, ``\"``, ``\\``)
        if text[cursor - 1] == "u" and text[cursor : cursor + 1] == "{":  # ``'\u{1F600}'``
            close = text.find("}", cursor)
            if close < 0:
                return None
            cursor = close + 1
    else:
        cursor += 1
    return cursor + 1 if text[cursor : cursor + 1] == "'" else None


def skip_quoted_identifier(text: str, start: int) -> int:
    """One past the ``« … »`` quoted identifier opening at ``start``.

    A quoted identifier may contain any character but ``»`` — including ``"``, ``--``, ``/-`` and
    ``-/`` (reference manual §5.2.3) — so its contents are a name, never code or a delimiter, and are
    skipped as a unit. An opening ``«`` never closed by ``»`` does not lex as one, so it stays an
    ordinary character and the text after it is still scanned.
    """
    close = text.find("»", start + 1)
    return close + 1 if close >= 0 else start + 1


def synthetic_hole_end(text: str, start: int) -> int | None:
    """One past a synthetic hole opening at ``start`` (``?h``, ``?«x»``), or ``None``.

    Lean's ``?name`` is a synthetic sorry: the goal is left to a metavariable. Whether it *survives*
    is not a lexical fact — ``refine … ?init ?step`` followed by the bullets that discharge both is a
    complete proof, while the same text without them is not — so this scan serves the policy that asks
    only whether a body rests on a metavariable at all, never the artifact-level closure count, which
    leaves a placeholder to elaboration and the axiom report (plan D6, revised). Its remaining caller
    is ``harness.closure.incomplete_body`` (plan D15); ``harness.lean_repl.count_unclosed`` reads an
    artifact with ``count_tokens`` and does not reach this. The syntax is ``?`` followed by an
    identifier, so the name is read to its own end (``?m.123`` is the hole ``?m`` and a projection) and
    may be a ``« … »`` quoted identifier, which is one token like any other. ``?`` must be followed by
    a *letter* to be a hole: a bare ``?``, a digit-named ``?1`` and the anonymous ``?_`` are other
    spellings, and ``?_`` is the ordinary anonymous-constructor idiom (``refine ⟨?_, ?_⟩``), each hole
    becoming a goal the following focusing discharges.

    ``admit?``, ``simp?`` and ``exact?`` end in ``?`` and are ordinary identifiers, which the scan
    consumes before reaching this.
    """
    if text[start] != "?" or start + 1 >= len(text):
        return None
    if text[start + 1] == "«":
        end = skip_quoted_identifier(text, start + 1)
        return end if end > start + 2 else None  # an unclosed « is not a name
    if not text[start + 1].isalpha():
        return None
    end = start + 2
    while end < len(text) and is_identifier_char(text[end]):
        end += 1
    return end


def skip_noncode(text: str, index: int) -> int | None:
    """One past the comment, string, character literal or quoted identifier opening at ``index``.

    ``None`` when the character at ``index`` opens none of them, so the caller reads it as code: this
    is the one place the delimiters are recognised, and both the hole counter below and
    ``harness.closure``'s declaration scan are loops over it.
    """
    if text.startswith("--", index) or text.startswith("/-", index):
        return skip_comment(text, index)
    char = text[index]
    if char == '"':
        return skip_string(text, index)
    if char == "'":
        return char_literal_end(text, index)
    if char == "«":
        return skip_quoted_identifier(text, index)
    return None


def _scan(text: str, tokens: Iterable[str], *, placeholders: bool) -> int:
    """One code-only pass counting whole-identifier occurrences of ``tokens``.

    ``placeholders`` adds every synthetic ``?name`` (``synthetic_hole_end``). Only a caller whose
    policy is about a declaration's own body asks for them: a placeholder's survival is elaboration's
    answer, so an artifact-level caller must not have this pass guess at it.
    """
    counted = frozenset(tokens)
    count = 0
    index = 0
    while index < len(text):
        skipped = skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        if placeholders and text[index] == "?":
            hole_end = synthetic_hole_end(text, index)
            if hole_end is None:
                index += 1
            else:
                count += 1
                index = hole_end
            continue
        token = identifier_at(text, index)
        if token is None:
            index += 1
        else:
            if token in counted:
                count += 1
            index += len(token)
    return count


def count_tokens(text: str, tokens: Iterable[str]) -> int:
    """How many of ``tokens`` a Lean text carries as whole identifiers in code, and nothing else.

    The pass ``count_holes`` makes without its synthetic-``?name`` clause, for a caller that has an
    authority for whether a placeholder survived and must not have one guessed at lexically
    (``harness.lean_repl.count_unclosed``, protocol §8). Only code counts: Lean's comments (``--`` to
    end of line, ``/- … -/`` with nesting), string literals, character literals and ``« … »`` quoted
    identifiers are skipped, so a spelling mentioned in prose is prose, and one inside a longer
    identifier (``sorryful``) is one name, not a spelling of its own.
    """
    return _scan(text, tokens, placeholders=False)


def count_holes(text: str, tokens: Iterable[str]) -> int:
    """How many holes a Lean text carries: ``tokens`` plus every synthetic ``?name``.

    Only code counts: a single pass skips Lean's comments (``--`` to end of line, ``/- … -/`` with
    nesting), string literals, character literals and ``« … »`` quoted identifiers, so a ``sorry`` in
    the seed's own prose or in a prover error message does not refuse a genuinely closed proof and
    lose its row. ``tokens`` is the caller's policy — the declaration spelling set is
    ``harness.closure._HOLE_TOKENS`` — while ``?name`` is counted for every caller, because a
    declaration whose body rests on a metavariable is not a body that establishes anything (plan D15).
    That is a declaration-level question; an artifact-level caller has elaboration in its place
    (``count_tokens``, plan D6, revised).

    A ``sorry`` inside a string *interpolation* (``s!"{sorry}"``) reads as string text and is missed
    here; the driver's close-guard covers that spelling, because the repl reports a proof containing
    ``sorry`` as ``Incomplete`` however the term is written (D6).
    """
    return _scan(text, tokens, placeholders=True)
