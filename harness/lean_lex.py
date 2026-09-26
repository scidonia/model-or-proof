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

    Lean's ``?name`` is a synthetic sorry: the goal is left to a metavariable, which the repl reports
    as ``contains metavariable(s)`` rather than as ``contains sorry``. It is a hole all the same, and
    the import-clean guard reads a module's source with no repl verdict to fall back on (plan D13), so
    it is counted here. The syntax is ``?`` followed by an identifier, so the name is read to its own
    end (``?m.123`` is the hole ``?m`` and a projection) and may be a ``« … »`` quoted identifier,
    which is one token like any other. ``?`` must be followed by a *letter* to be a hole: a bare ``?``,
    a digit-named ``?1`` and the anonymous ``?_`` are other spellings and stay with the repl's verdict
    — ``?_`` is the ordinary anonymous-constructor idiom (``refine ⟨?_, ?_⟩``), each hole becoming a
    goal the following focusing discharges, and a surviving one shows up as ``sorryAx`` in the axiom
    set, which is the authority this scan is a pre-filter for (plan D6, revised).

    ``admit?``, ``simp?`` and ``exact?`` end in ``?`` and are ordinary identifiers, which the scan
    consumes before reaching this.

    **This scan is a pre-filter and a diagnostic; the axiom check is the authority for closure.** A
    hole that survives elaboration is `sorry`-backed, so it shows up as ``sorryAx`` in the axiom set
    regardless of how the term was written — which is why the proxy can afford to leave ``?_`` to the
    repl's verdict rather than guess at Lean's syntax. Read the two as layers, not as competing rules:
    this one is cheap, needs no toolchain, and runs on a module source; the axiom set is what says the
    proof is real.
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


def count_holes(text: str, tokens: Iterable[str]) -> int:
    """How many holes a Lean text carries, counting ``tokens`` and every synthetic ``?name``.

    Only code counts: a single pass skips Lean's comments (``--`` to end of line, ``/- … -/`` with
    nesting), string literals, character literals and ``« … »`` quoted identifiers, so a ``sorry`` in
    the seed's own prose or in a prover error message does not refuse a genuinely closed proof and
    lose its row. ``tokens`` is the caller's policy — the artifact spelling set is
    ``harness.lean_repl.UNCLOSED_TOKENS`` — while ``?name`` is always a hole, whatever the caller
    counts (plan D13).

    A ``sorry`` inside a string *interpolation* (``s!"{sorry}"``) reads as string text and is missed
    here; the driver's close-guard covers that spelling, because the repl reports a proof containing
    ``sorry`` as ``Incomplete`` however the term is written (D6).
    """
    counted = frozenset(tokens)
    count = 0
    index = 0
    while index < len(text):
        skipped = skip_noncode(text, index)
        if skipped is not None:
            index = skipped
            continue
        if text[index] == "?":
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
