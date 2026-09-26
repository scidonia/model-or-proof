"""Closure oracle for a candidate proof file (plan D26).

The unit of proof in file mode is the file. This is how the harness decides, mechanically, that a
candidate *is* a closure of the statement it was asked for — three checks, in order:

1. **Integrity** — the candidate is byte-identical to the seed up to and including the theorem's
   assignment token. That pins every definition (`Phase`, `State`, `ringSucc`, the actions,
   `Reachable`, `Mutex`), the statement, and the model; only the proof body is free. A violation is
   **reported** in the row and never silently prevented, so a run that weakened the model is visible
   rather than merely rejected.
2. **Elaborates** — ``lake env lean <candidate>`` exits 0 with no ``error``. Necessary, and worth
   nothing on its own: the untouched seed compiles.
3. **Closed** — ``#print axioms <theorem>`` reports an axiom set within :data:`ALLOWED_AXIOMS`. This is
   the load-bearing check: a ``sorry`` shows as ``sorryAx`` and a hand-rolled ``axiom`` under its own
   name, so only this distinguishes "compiles" from "closed".

Fixtures (``proofs/lean/token-ring/reference/``, deliberately outside the loop's path):

* positive — ``SeedWithReferenceProof.lean``: the host reference reshaped onto the seed's exact
  statement, so it passes all three and is the one the oracle is demonstrated against;
* negative — the untouched ``TokenRing.lean``: passes integrity and elaboration, fails on ``sorryAx``;
* ``HostReference.lean`` is *not* a fixture: it takes ``N`` as an explicit binder and names the theorem
  ``mutex_mine``, so it fails integrity on purpose — the demonstration that the check bites.

``check`` runs the candidate only: it never writes the candidate, so a caller can point it at a working
copy the model has been editing.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import tempfile

#: The axioms a closure may depend on. ``propext``/``Classical.choice``/``Quot.sound`` are Lean's own;
#: anything else (``sorryAx``, a hand-rolled ``axiom``) means the proof is not a proof.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

#: The elaboration's own bound: a Mathlib-importing candidate takes seconds, not minutes; a hang is a
#: result (``elaborates`` false with the tail saying so), not something to wait out.
ELABORATION_TIMEOUT_S = 600


def _namespace_of(text: str, theorem: str) -> str | None:
    """The namespace the theorem is declared in, if the seed declares one."""
    namespaces: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        match = re.match(r"namespace\s+([A-Za-z_][\w'.]*)", stripped)
        if match:
            namespaces.append(match.group(1))
        if re.match(rf"theorem\s+{re.escape(theorem)}\b", stripped):
            return namespaces[-1] if namespaces else None
        if stripped == "end" and namespaces:
            namespaces.pop()
    return namespaces[-1] if namespaces else None


def theorem_name(seed_text: str, theorem: str = "mutex") -> str:
    """``<namespace>.<theorem>`` for the seed's theorem, as ``#print axioms`` needs it (plan D26).

    Derived from the seed rather than configured, because the seed is the only place the declaration
    lives and the task manifests are not ours to extend: the theorem is the one the seed states, in the
    namespace the seed encloses it in.
    """
    namespace = _namespace_of(seed_text, theorem)
    return f"{namespace}.{theorem}" if namespace else theorem


def pinned_prefix(text: str, theorem: str = "mutex") -> str | None:
    """Everything up to and including the theorem's assignment token, or ``None`` if there is none.

    ``None`` is itself an integrity failure: a candidate whose statement cannot be located has not been
    shown to keep the seed's.
    """
    match = re.search(rf"^theorem\s+{re.escape(theorem)}\b.*?:=", text, re.M | re.S)
    return text[: match.end()] if match else None


def error_lines(output: str, *, max_lines: int = 60, max_chars: int = 6000) -> list[str]:
    """Lean's own errors out of the elaboration output, capped for a prompt.

    The oracle *appends* ``#print axioms`` to the candidate, so the end of the output is the axiom
    report and, before it, the linter's notes — neither of which says why a file failed. Feeding those
    to the model is the failure this field exists to prevent (measured: a candidate with one real error
    produced a tail of a linter note and the axiom line, and not one error). So the appended axiom
    result, ``warning:`` lines and the linter's ``Note:`` lines come out, and the rest is kept as
    **lines rather than single messages**, because Lean's error text is multi-line.

    The cap is the prompt's, not the record's: a failing Mathlib-touching file can emit hundreds of
    lines, and the model needs the list, not the dump. The row keeps the uncapped output in
    ``raw_tail``'s counterpart (``output`` is not stored whole; ``check`` stores the errors capped and
    the last three raw lines).
    """
    kept: list[str] = []
    for line in output.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if re.search(r"depends on axioms:\s*\[", stripped) or "does not depend on any axioms" in stripped:
            continue
        if re.search(r":\s*warning:", stripped) or stripped.startswith("warning:"):
            continue
        if stripped.startswith("Note:") or re.search(r":\s*Note:", stripped):
            continue
        kept.append(line)
    trimmed = max(0, len(kept) - max_lines)
    kept = kept[:max_lines]
    text = "\n".join(kept)
    if len(text) > max_chars:
        text = text[:max_chars]
        trimmed = trimmed or 1
    if trimmed:
        kept = text.splitlines() + [f"… ({trimmed} more line(s) of Lean output, trimmed for the prompt)"]
    return kept


def extract_axioms(output: str) -> set[str] | None:
    """The axiom set ``#print axioms`` reported, or ``None`` when it said nothing about one."""
    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", output)
    if match:
        return {axiom.strip() for axiom in match.group(1).split(",") if axiom.strip()}
    if "does not depend on any axioms" in output:
        return set()
    return None


def sha256_text(text: str) -> str:
    """The digest of a seed's text, for comparing the file's state before and after a run."""
    import hashlib

    return hashlib.sha256(text.encode()).hexdigest()


def check(
    candidate: str,
    *,
    pristine: str,
    package: pathlib.Path | str,
    theorem: str,
    timeout: float = ELABORATION_TIMEOUT_S,
) -> dict:
    """Run the three checks over ``candidate`` and report each one (plan D26).

    ``pristine`` is the seed's text **as recorded before the run**, not read from the working tree: a
    prover with a shell can write anywhere, so a candidate that "matches" an edited seed would pass
    integrity while proving a different theorem. The caller takes it from the run's recorded baseline
    (or a copy kept beyond the prover's reach) and, after the run, compares the seed file's own digest
    against it — a moved seed is reported rather than absorbed into the baseline.

    ``candidate`` is the candidate file's **text**: the check writes its own probe, so it does not need
    a path, and a caller reading a working copy the model may still be editing decides when to read it.
    ``package`` is the lake package directory the elaboration runs in; ``theorem`` is the name
    ``#print axioms`` is asked about (:func:`theorem_name` derives it from a seed).
    """
    text = candidate

    before, seed_before = pinned_prefix(text, theorem.rsplit(".", 1)[-1]), pinned_prefix(
        pristine, theorem.rsplit(".", 1)[-1]
    )
    integrity = before is not None and before == seed_before

    # A unique probe in the system temp directory: `lake env` resolves the package's imports from the
    # environment it builds, not from the probe's location (measured), and a fixed name would let two
    # runs overwrite each other's probe.
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, prefix="_closure_probe_"
    ) as probe:
        probe.write(text + f"\n#print axioms {theorem}\n")
        probe_path = pathlib.Path(probe.name)
    try:
        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(probe_path)],
                cwd=package,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            output = completed.stdout + completed.stderr
            elaborates = completed.returncode == 0 and re.search(r"\berror\b", output) is None
        except subprocess.TimeoutExpired as expired:
            partial = (expired.stdout or "") + (expired.stderr or "")
            partial = partial if isinstance(partial, str) else partial.decode(errors="replace")
            output = partial + f"\nlake env lean did not finish within {timeout:g}s\n"
            elaborates = False
    finally:
        probe_path.unlink(missing_ok=True)

    axioms = extract_axioms(output)
    return {
        "integrity": integrity,
        "elaborates": elaborates,
        # A set, as the contract states: `verdict` compares it with the allowed set. A caller that
        # needs JSON sorts it where it builds the row (harness.file_mode does).
        "axioms": axioms,
        # A file that fails to *elaborate* still reports `sorryAx`: Lean's error recovery leaves the
        # declaration sorry-ed, so the axiom check catches an elaboration failure independently of
        # `elaborates`. That is a property worth relying on, and worth this comment — a reader seeing
        # `sorryAx` in a row whose file had a parse error would otherwise call it a bug.
        "closed": axioms is not None and axioms <= ALLOWED_AXIOMS,
        "pristine_sha256": sha256_text(pristine),
        # Who the failing round is told: Lean's own errors, capped. `raw_tail` is for the CLI and the
        # row, where three lines of context is right — it is *not* what a retry prompt gets.
        "errors": error_lines(output),
        "raw_tail": output.strip().splitlines()[-3:],
    }


def verdict(result: dict, *, seed_intact: bool = True) -> bool:
    """Whether the oracle calls the candidate a closure: all three checks, not the convenient one.

    ``seed_intact`` is the caller's post-run answer to "is the seed still what the run started from?".
    A moved seed fails the verdict whatever the candidate looks like: a proof of a statement the prover
    was free to rewrite is not a proof of ours (plan D26).
    """
    if not seed_intact:
        return False
    return bool(result["integrity"] and result["elaborates"] and result["closed"])


def main(argv: list[str] | None = None) -> int:
    """Check candidates from the command line, one verdict each (the fixtures' entry point)."""
    import argparse

    parser = argparse.ArgumentParser(prog="python -m harness.closure_oracle")
    parser.add_argument("candidates", nargs="+")
    parser.add_argument("--seed", required=True, help="the seed the candidate must keep faith with")
    parser.add_argument("--package", required=True, help="the lake package directory")
    parser.add_argument("--theorem", help="the name #print axioms is asked about (default: from the seed)")
    args = parser.parse_args(argv)

    seed_path = pathlib.Path(args.seed)
    pristine = seed_path.read_text()
    theorem = args.theorem or theorem_name(pristine)
    for candidate in args.candidates:
        result = check(pathlib.Path(candidate).read_text(), pristine=pristine, package=args.package, theorem=theorem)
        seed_intact = sha256_text(seed_path.read_text()) == result["pristine_sha256"]
        ok = verdict(result, seed_intact=seed_intact)
        if not seed_intact:
            print(f"    seed {seed_path} changed during the check: its digest no longer matches")
        print(f"{'CLOSED' if ok else 'NOT-CLOSED'}  {candidate}")
        print(
            f"    integrity={result['integrity']}  elaborates={result['elaborates']}  "
            f"axioms={result['axioms']}"
        )
        if not ok:
            for line in result["raw_tail"]:
                print(f"    tail: {line}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
