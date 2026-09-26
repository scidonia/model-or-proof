"""Closure oracle for a candidate proof file (plan D26).

The unit of proof in file mode is the file. This is how the harness decides, mechanically, that a
candidate *is* a closure of the statement it was asked for — three checks, in order:

1. **Integrity** — the candidate is byte-identical to the seed up to and including the theorem's
   assignment token. That pins every definition (`Phase`, `State`, `ringSucc`, the actions,
   `Reachable`, `Mutex`), the statement, and the model; only the proof body is free. A violation is
   **reported** in the row and never silently prevented, so a run that weakened the model is visible
   rather than merely rejected.
2. **Elaborates** — the candidate is handed to the toolchain's own ``lean`` **directly**, written as
   ``<tmpdir>/<Module>.lean`` and elaborated there (``lean`` takes the module name from the source
   path, not from ``-o``), with the ``LEAN_PATH`` the harness passes. ``<Module>`` is the seed's own
   module — its file name — so the candidate is the module its own ``import``\\ s expect and the one
   the checker imports; the check is told both names (:func:`check`) rather than deriving them. No
   ``lake`` in that invocation: the candidate's shell can reach the package's lakefile, so a lake-built
   environment is the candidate's, not the harness's. Necessary, and worth nothing on its own: the
   untouched seed compiles.
3. **Closed** — the prebuilt checker ``tools/checker/.lake/build/bin/axiom-checker`` imports that
   olean through ``Lean.importModules`` and reads the declaration's axiom set out of the **API**
   (``Lean.collectAxioms`` over the loaded environment) against :data:`ALLOWED_AXIOMS`. This is the
   load-bearing check: a ``sorry`` shows as ``sorryAx`` and a hand-rolled ``axiom`` under its own
   name, so only this distinguishes "compiles" from "closed". It is not a restatement of check 1, it
   is the layer behind it: ``#print axioms`` is *syntax*, and syntax is an environment extension a
   candidate can install and crosses imports — measured, a candidate rewrote the command into text of
   its own and the real report never ran (``tools/checker/PROVENANCE.md``, the ``import Evil``
   experiment). No candidate source can reach this query, so a forged ``#print`` line cannot touch the
   set the seed's own ``sorryAx`` is caught in.

Fixtures (``proofs/lean/token-ring/reference/``, deliberately outside the loop's path):

* positive — ``SeedWithReferenceProof.lean``: the host reference reshaped onto the seed's exact
  statement, so it passes all three and is the one the oracle is demonstrated against;
* negative — the seed's recorded pristine text, ``proofs/lean/token-ring/baseline/TokenRing.lean``:
  passes integrity and elaboration, fails on ``sorryAx``. Not the seed file beside it, which
  ``scripts/promote.py`` rewrites (and re-pins in ``seeds.json``) once its proof is promoted for tier 1:
  the baseline is left alone precisely so that "the untouched seed" keeps meaning the ``sorry`` text,
  and it is what the callers pass as ``pristine``;
* ``HostReference.lean`` is *not* a fixture: it takes ``N`` as an explicit binder and names the theorem
  ``mutex_mine``, so it fails integrity on purpose — the demonstration that the check bites.

``check`` runs the candidate only: it never writes the candidate, so a caller can point it at a working
copy the model has been editing.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile

#: The repository root, for the checker the sources under ``tools/`` build.
REPO_ROOT = pathlib.Path(__file__).resolve().parents[1]

#: The trusted checker (source and rationale: ``tools/checker/PROVENANCE.md``). A build artifact, so
#: a missing one is a provisioning failure and is raised as one rather than read as a candidate's.
AXIOM_CHECKER = REPO_ROOT / "tools" / "checker" / ".lake" / "build" / "bin" / "axiom-checker"

#: The axioms a closure may depend on. ``propext``/``Classical.choice``/``Quot.sound`` are Lean's own;
#: anything else (``sorryAx``, a hand-rolled ``axiom``) means the proof is not a proof.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

#: The elaboration's own bound (the checker is given the same one): a Mathlib-importing candidate takes
#: seconds, not minutes; a hang is a result (``elaborates`` false with the tail saying so), not
#: something to wait out.
ELABORATION_TIMEOUT_S = 600

#: How much of a diagnostic block a retry prompt can carry.
MAX_ERROR_LINES = 60
MAX_ERROR_CHARS = 6000


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


def seed_theorem(seed_text: str) -> str:
    """The simple name of the theorem the seed declares (plan D5's shape: one theorem, one ``sorry``).

    Read off the seed rather than assumed: a default name is wrong for every seed that is not
    token-ring's tier-2 file (the tier-1 corollary is ``mutex_n0``, Bakery's is ``mutual_exclusion``),
    and a wrong name does not fail loudly — it makes :func:`pinned_prefix` find nothing and reports
    ``integrity`` false for a file that is byte-identical to the seed, which then feeds the model a
    misleading complaint until its budget runs out.
    """
    match = re.search(r"^theorem\s+([A-Za-z_][\w'.]*)", seed_text, re.M)
    if match is None:
        raise ValueError("the seed declares no theorem: plan D5's shape is one theorem with one `sorry`")
    return match.group(1)


def theorem_name(seed_text: str, theorem: str | None = None) -> str:
    """``<namespace>.<theorem>`` for the seed's theorem, the fully qualified name to check (plan D26).

    The name comes from the seed — the only place the declaration lives, and the task manifests are not
    ours to extend — and a caller passes one only when it has it from elsewhere. The checker is asked
    about this name and prints the name it resolved, so the two are compared rather than assumed to
    agree.
    """
    theorem = theorem or seed_theorem(seed_text)
    namespace = _namespace_of(seed_text, theorem)
    return f"{namespace}.{theorem}" if namespace else theorem


def pinned_prefix(text: str, theorem: str) -> str | None:
    """Everything up to and including the theorem's assignment token, or ``None`` if there is none.

    ``None`` is itself an integrity failure: a candidate whose statement cannot be located has not been
    shown to keep the seed's. The name is required for the same reason :func:`theorem_name` reads it
    off the seed: a default would silently make every seed that declares something else fail integrity.
    """
    match = re.search(rf"^theorem\s+{re.escape(theorem)}\b.*?:=", text, re.M | re.S)
    return text[: match.end()] if match else None


def _capped(
    lines: list[str], *, max_lines: int = MAX_ERROR_LINES, max_chars: int = MAX_ERROR_CHARS
) -> list[str]:
    """A diagnostic block cut down to what a retry prompt can carry, saying how much was dropped."""
    trimmed = max(0, len(lines) - max_lines)
    kept = lines[:max_lines]
    text = "\n".join(kept)
    if len(text) > max_chars:
        text = text[:max_chars]
        trimmed = trimmed or 1
    if trimmed:
        return text.splitlines() + [f"… ({trimmed} more line(s) of Lean output, trimmed for the prompt)"]
    return kept


def error_lines(output: str, *, max_lines: int = MAX_ERROR_LINES, max_chars: int = MAX_ERROR_CHARS) -> list[str]:
    """Lean's diagnostics out of the elaboration output, capped only after they are selected.

    Two defects this shape exists to avoid (finding F3). First, the *order*: capping first meant the first
    60 lines were kept whatever they were, so a candidate that printed 61 `#eval` lines before its real
    error handed the model noise and hid the error. Diagnostics are therefore selected first — a line
    carrying Lean's position and severity (`…:12:4: error`, or a bare `error:`) starts a block, and its
    indented continuation lines belong to it — and the cap is applied to the result. Second, the *noise*:
    the oracle writes no probe into the candidate, but the candidate can print lines of its own, and a
    line claiming an axiom report is a claim *about* the file rather than a diagnostic for it; warnings,
    `Note:` lines and claim lines are therefore never selected.

    A candidate with no diagnostics yields an empty list, which is the caller's signal to fall back (see
    `file_mode`), not a licence to forward arbitrary output.
    """
    diagnostics: list[str] = []
    in_block = False
    for line in output.splitlines():
        stripped = line.strip()
        if not stripped:
            in_block = False
            continue
        if re.search(r"depends on axioms:\s*\[", stripped) or "does not depend on any axioms" in stripped:
            in_block = False
            continue
        if re.search(r":\s*warning:", stripped) or stripped.startswith("warning:"):
            in_block = False
            continue
        if stripped.startswith("Note:") or re.search(r":\s*Note:", stripped):
            # A linter note belongs to the message above it, but it is never the actionable text.
            continue
        starts = re.search(r":\d+:\d+:\s*error\b", stripped) or stripped.startswith("error")
        if starts:
            diagnostics.append(line.strip())
            in_block = True
        elif in_block and line[:1] in (" ", "\t"):
            diagnostics.append(line.rstrip())
        else:
            in_block = False
    return _capped(diagnostics, max_lines=max_lines, max_chars=max_chars)


def checker_axioms(stdout: str, theorem: str) -> tuple[set[str] | None, str, str | None]:
    """The axiom set the checker printed, whether it is usable, and why not when it is not.

    The checker's output contract (``tools/checker/PROVENANCE.md``) is one item per line: ``axioms
    <count>`` first, one axiom name per line, then ``resolved <fully qualified name>`` last. It prints
    **no** ``axioms`` line when it cannot answer, and exits non-zero, so "I could not find it" and "it
    has no axioms" are never the same answer. A set is read only when every part is there and agrees:
    the count matches the names it printed, and ``resolved`` is the declaration that was asked about —
    a checker that resolved a same-named neighbour has answered a different question, and that answer
    is not ours to use.

    ``"ambiguous"`` remains part of the vocabulary but no longer has a case: the API checker is
    **asked once** and prints one report, so there is no second report for a caller to choose between
    (the old ``#print`` probe could be intercepted twice, and counting reports was how that was caught).
    A report whose name is not ours, or one that cannot be parsed, is ``"missing"`` — the honest
    reading being that *this* declaration's set was not obtained.
    """
    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    header = re.fullmatch(r"axioms (\d+)", lines[0]) if lines else None
    if header is None:
        return None, "missing", f"the checker printed no `axioms` line (stdout begins {lines[:1]!r})"
    body = lines[1:]
    if not body or not body[-1].startswith("resolved "):
        return None, "missing", f"the checker printed no `resolved` line (output ends {body[-1:]!r})"
    resolved = body[-1].split(None, 1)[1].strip()
    names = body[:-1]
    expected = int(header.group(1))
    if len(names) != expected:
        return None, "missing", f"the checker printed `axioms {expected}` with {len(names)} name line(s)"
    if resolved != theorem:
        return None, "missing", f"the checker resolved {resolved!r}, not the {theorem!r} asked about"
    return set(names), "ok", None


def toolchain_prefix(package: pathlib.Path) -> pathlib.Path:
    """The toolchain the package pins, asked of ``lean`` where the pin lives.

    ``lean`` on PATH is elan's shim: run from the package directory it reads the package's
    ``lean-toolchain`` and resolves to the pinned toolchain — the Lean the checker binary was built with,
    and therefore the only one whose olean it will accept. The prefix it prints is also where the
    toolchain's own ``lib/lean`` sits, the last entry of the search path.
    """
    try:
        completed = subprocess.run(
            ["lean", "--print-prefix"], cwd=package, capture_output=True, text=True, timeout=120
        )
    except OSError as failure:
        raise RuntimeError(f"no `lean` on PATH to ask for the package's toolchain prefix: {failure}") from failure
    prefix = completed.stdout.strip()
    if completed.returncode != 0 or not prefix:
        raise RuntimeError(
            f"`lean --print-prefix` in {package} failed (exit {completed.returncode}): "
            f"{completed.stderr.strip() or 'no output'}"
        )
    return pathlib.Path(prefix)


def dependency_lean_path(package: pathlib.Path) -> str:
    """The package's ``LEAN_PATH``, derived from what the package declares rather than recorded.

    Each dependency's build output, then the package's own, then the toolchain's ``lib/lean``: no
    host-specific string, and the same shape and order ``lake env`` builds — including entries whose
    directory does not exist yet (an unbuilt or unused dependency), which are harmless search-path
    entries rather than errors. A genuinely missing build shows up where it belongs: the elaborator
    fails on the import it cannot resolve, and that diagnostic reaches the caller in ``errors``. The
    entries are absolute: the elaboration runs in its own probe directory, so a relative one would
    resolve against *that* rather than against the caller's working directory.
    """
    package = pathlib.Path(package).resolve()
    manifest = json.loads((package / "lake-manifest.json").read_text())
    packages_dir = package / manifest.get("packagesDir", ".lake/packages")
    roots = [
        packages_dir / dependency["name"] / ".lake" / "build" / "lib" / "lean"
        for dependency in manifest.get("packages", [])
    ]
    roots.append(package / ".lake" / "build" / "lib" / "lean")
    roots.append(toolchain_prefix(package) / "lib" / "lean")
    return os.pathsep.join(str(root) for root in roots)


def capture_lean_path(package: pathlib.Path | str) -> str | None:
    """The ``LEAN_PATH`` ``lake`` builds for the package, or ``None`` when it cannot be had.

    Called **before** a session opens, and passed to every check that session needs (see
    ``file_mode.run_file``): the file-mode shell can reach the package's lakefile, so a search path
    computed after its turn is a path the candidate influenced. No answer from ``lake`` is not an error
    here — :func:`dependency_lean_path` derives an equivalent path — but the caller says which one it
    used, so a run's environment is checkable afterwards.
    """
    package = pathlib.Path(package).resolve()
    try:
        completed = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=package,
            capture_output=True,
            text=True,
            timeout=300,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    return lines[-1] if completed.returncode == 0 and lines else None


def _checker_report(
    workdir: pathlib.Path,
    module: str,
    theorem: str,
    search_path: str,
    timeout: float,
) -> tuple[set[str] | None, str, str | None, str]:
    """Ask the checker about one elaborated module: its set, its report, why not, and its output.

    The search path leads with ``workdir``: the candidate's olean must win over the package's own
    pre-built module of the same name, which is exactly the module whose declarations we mean to read.
    """
    if not AXIOM_CHECKER.is_file():
        raise RuntimeError(
            f"the axiom checker is not built at {AXIOM_CHECKER}: run "
            "`nix develop -c bash -c 'cd tools/checker && lake build'` (tools/checker/PROVENANCE.md)"
        )
    env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(workdir), search_path])}
    try:
        completed = subprocess.run(
            # The checker resolves `<Module> ++ <argument>` first and the argument itself second, so the
            # argument is the *fully qualified* declaration name: the candidate's module is the seed's
            # file stem, which need not be the theorem's namespace (`TokenRingN0.lean` declares
            # `TokenRing.mutex_n0`), and the qualified slot is the one that finds it. It is also the
            # precise request — a decoy sharing the simple name cannot stand in for it — and the
            # `resolved` line is compared with the same string.
            [str(AXIOM_CHECKER), module, theorem],
            cwd=workdir,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, "missing", f"the axiom checker did not finish within {timeout:g}s", ""
    output = completed.stdout + completed.stderr
    if completed.returncode != 0:
        reason = completed.stderr.strip() or completed.stdout.strip() or "no output"
        return (
            None,
            "missing",
            f"the axiom checker could not answer for {theorem!r} (exit {completed.returncode}): {reason}",
            output,
        )
    axioms, report, why = checker_axioms(completed.stdout, theorem)
    return axioms, report, why, output


def sha256_text(text: str) -> str:
    """The digest of a seed's text, for comparing the file's state before and after a run."""
    import hashlib

    return hashlib.sha256(text.encode()).hexdigest()


def check(
    candidate: str,
    *,
    pristine: str,
    package: pathlib.Path | str,
    module: str,
    theorem: str,
    timeout: float = ELABORATION_TIMEOUT_S,
    lean_path: str | None = None,
) -> dict:
    """Run the three checks over ``candidate`` and report each one (plan D26).

    ``pristine`` is the seed's text **as recorded before the run**, not read from the working tree: a
    prover with a shell can write anywhere, so a candidate that "matches" an edited seed would pass
    integrity while proving a different theorem. The caller takes it from the run's recorded baseline
    (or a copy kept beyond the prover's reach) and, after the run, compares the seed file's own digest
    against it — a moved seed is reported rather than absorbed into the baseline.

    ``candidate`` is the candidate file's **text**: the check writes its own probe directory, so it does
    not need a path, and a caller reading a working copy the model may still be editing decides when to
    read it. ``package`` is the lake package directory the toolchain is pinned by and the candidate's
    imports are resolved from.

    ``module`` and ``theorem`` are the two names, and both are given rather than derived here, because
    they are different kinds of name:

    * ``module`` is the **candidate's own** module — the seed's file name, which is what ``lean`` makes
      of it and what the candidate's own ``import``\\ s resolve against. It is what the probe is
      elaborated as and what the checker imports.
    * ``theorem`` is the **fully qualified declaration** name (:func:`theorem_name` derives it from the
      seed), and the name the checker's ``resolved`` line is compared with.

    A value assumed rather than read is how a caller gets a wrong answer that looks like a verdict, so
    nothing here guesses either one.

    ``lean_path`` is the search path the elaboration and the checker both run with. A caller that has a
    session in flight passes the path it captured *before* the session opened (the shell can reach the
    package's lakefile, so the path is captured, never computed afterwards); ``None`` derives it with
    :func:`dependency_lean_path`, which is what the fixtures do.

    The axiom check is an independent layer rather than a restatement of integrity: the untouched
    seed's extra axiom is caught by the *environment* the checker loads, and a forged ``#print`` line
    cannot reach that set at all.
    """
    package = pathlib.Path(package).resolve()
    text = candidate
    # Whether the elaboration was cut off rather than answered (finding F3): the caller's licence to
    # fall back to raw output, because a timeout has no diagnostic to select.
    timed_out = False
    elaborates = False
    output = ""
    checker_output = ""

    before, seed_before = pinned_prefix(text, theorem.rsplit(".", 1)[-1]), pinned_prefix(
        pristine, theorem.rsplit(".", 1)[-1]
    )
    integrity = before is not None and before == seed_before

    search_path = lean_path if lean_path is not None else dependency_lean_path(package)
    # The toolchain's own `lean`, not elan's shim: run from the probe directory the shim would resolve
    # against no `lean-toolchain` at all and pick a default toolchain, whose olean the checker might
    # refuse. `-o` is where the olean goes; the module name comes from the source path under `workdir`.
    lean = toolchain_prefix(package) / "bin" / "lean"

    # A unique probe directory in the system temp: the candidate is elaborated *there* so its module
    # name matches the module the checker imports (the trap in `tools/checker/PROVENANCE.md`), and a
    # fixed path would let two runs overwrite each other's olean.
    workdir = pathlib.Path(tempfile.mkdtemp(prefix="_closure_probe_"))
    source = workdir.joinpath(*module.split(".")).with_suffix(".lean")
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(text)
    olean = source.with_suffix(".olean")
    env = {**os.environ, "LEAN_PATH": search_path}
    axioms: set[str] | None = None
    axiom_report = "missing"
    why: str | None = None
    try:
        try:
            completed = subprocess.run(
                [str(lean), "-o", str(olean), str(source.relative_to(workdir))],
                cwd=workdir,
                env=env,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            output = completed.stdout + completed.stderr
            elaborates = completed.returncode == 0 and re.search(r"\berror\b", output) is None
        except subprocess.TimeoutExpired as expired:
            partial = (expired.stdout or "") + (expired.stderr or "")
            partial = partial if isinstance(partial, str) else partial.decode(errors="replace")
            output = partial + f"\nlean did not finish within {timeout:g}s\n"
            timed_out = True

        if elaborates:
            axioms, axiom_report, why, checker_output = _checker_report(
                workdir, module, theorem, search_path, timeout
            )
        # A candidate that does not elaborate is not asked about: there is no olean to import, or one
        # that a half-written elaboration left behind, and "what does this file depend on" is already
        # answered no. Its report is `missing`, and the elaborator's diagnostics are the model-facing
        # ones — the checker's "no such declaration" would only be noise on top of them.
    finally:
        shutil.rmtree(workdir, ignore_errors=True)

    # The checker's own reason for not answering is a diagnostic the retry prompt can act on, appended
    # after the elaborator's selected block: one line, so it is not worth putting through the cap.
    errors = error_lines(output) + ([why] if why else [])
    detail = "\n".join(part for part in (output, checker_output) if part.strip())
    return {
        "integrity": integrity,
        "elaborates": elaborates,
        # A set, as the contract states: `verdict` compares it with the allowed set. A caller that
        # needs JSON sorts it where it builds the row (harness.file_mode does).
        "axioms": axioms,
        # Whether that set is usable at all (finding F1): "ok", or "missing" when the checker did not
        # answer for this declaration — no checker answer, a `resolved` name that is not ours, or an
        # elaboration that failed. "ambiguous" stays in the vocabulary with no case (see
        # `checker_axioms`), and is never returned. `closed` is gated on this, not merely on the set.
        "axiom_report": axiom_report,
        # A file that fails to *elaborate* still reports `sorryAx`: Lean's error recovery leaves the
        # declaration sorry-ed, so the axiom check catches an elaboration failure independently of
        # `elaborates`. That is a property worth relying on, and worth this comment — a reader seeing
        # `sorryAx` in a row whose file had a parse error would otherwise call it a bug.
        "closed": axiom_report == "ok" and axioms is not None and axioms <= ALLOWED_AXIOMS,
        "pristine_sha256": sha256_text(pristine),
        # Who the failing round is told: Lean's diagnostics, selected before capping. `raw_tail` is for
        # the CLI and the row, where three lines of context is right — it is *not* what a retry prompt
        # gets; the retry falls back to it only on `timed_out`.
        "errors": errors,
        "timed_out": timed_out,
        "raw_tail": detail.strip().splitlines()[-3:],
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
    parser.add_argument("--theorem", help="the name the axiom checker is asked about (default: from the seed)")
    args = parser.parse_args(argv)

    seed_path = pathlib.Path(args.seed)
    pristine = seed_path.read_text()
    theorem = args.theorem or theorem_name(pristine)
    for candidate in args.candidates:
        result = check(
            pathlib.Path(candidate).read_text(),
            pristine=pristine,
            package=args.package,
            theorem=theorem,
            # The seed's module as `lean` names a package-root source: its file name. The CLI has the
            # path, so it passes the real thing rather than the namespace fallback.
            module=seed_path.stem,
        )
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
