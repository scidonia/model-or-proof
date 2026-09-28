"""Prepare one clean, independent Paxos proof attempt from a source template.

Contract: ``tests/paxos-attempt-isolation-contract.md``. The researcher runs this **before**
``harness.route_b --mode file --reps 1``, because ``--reps 1`` alone still leaves the template's
``.runs/`` scratch, its promoted ``PaxosProved.lean`` and its closure copies in the working directory
the next sample starts from (``harness/route_b.py:308-323,378-390``). Preparing an attempt makes a
*separate* Lean package that holds only the registered seed, its recorded baseline, the package
configuration, and a link to the pinned dependency cache — so an attempt's own tree contains none of
the earlier attempts' proofs::

    python -m harness.attempt_workspace prepare \\
      --template proofs/lean/paxos --seed Paxos.lean \\
      --attempt 1 --workspace-root <workspace root> --results-root <results root>

It prints one JSON receipt with ``attempt``, the absolute ``package``, ``seed`` and ``results`` paths
and the copied seed's ``seed_sha256``, and exits 0. A destination that already exists — the same
attempt prepared twice — is refused (exit 2) rather than overwritten, so an existing attempt's
evidence is never silently replaced.

What the *preparation* asserts, and what the *receipt* carries. The preparation enforces a
*filesystem* statement about the fresh tree, refusing rather than proceeding when it cannot: the named
seed and ``baseline/<seed>`` are byte-identical to the registered digest in ``seeds.json``, ``seed``
is inside ``package``, ``results`` is outside it (and its own per-attempt directory), the pinned cache
is a symlink reused rather than a ≈7 GB copy, and the package's top level holds none of the
template's ``.runs/``, promoted target, closure copies, other modules or results. The receipt printed
to stdout carries five fields — ``attempt``, ``package``, ``results``, ``seed`` and ``seed_sha256`` —
and the seed digest is the one asserted property it also names; a reader who wants the rest of the
statement above inspects the prepared tree, which is what the contract's scenarios do.
It does **not** assert that earlier proofs are unreadable. This host has no enforced read sandbox
(``harness/outside_watch.py:1-11``: ``unshare``/bubblewrap are denied, file-mode bash runs as the same
UID, and ``outside_watch`` tracks writes only), so a same-UID session can still read any path it names.
The accepted guarantee is **operational nonreuse**: the attempt's own tree offers no prior proof, and
complete tool-call transcripts are audited afterwards, with any observed prior same-tier read
invalidating that attempt. No comment, receipt or doc here claims otherwise.

Four more things this boundary leaves alone, named so a reader need not infer them. The linked
``.lake/packages`` is *shared mutable state*, not a per-attempt copy: a dependency rebuild or
``lake update`` through it is visible to the template and to every other attempt. Nothing stops a
session from reading a *sibling* attempt's results directory. Reads are unconstrained and no receipt
records what was read, which is why the offered guarantee is operational nonreuse plus a post-hoc
transcript audit rather than an enforced sandbox. And ``PaxosMutant.lean`` is copied beside
``Paxos.lean``, so "the seed" here means the registered seed *set*, not a single file.

The dependency cache is linked, not copied. ``.lake/packages`` in the template is the pinned Mathlib
(and its own dependency) checkout — ≈7 GB, and a per-attempt copy would cost that per attempt. The new
package gets one symlink to it, and an offline ``lake env lean`` elaboration of ``import Mathlib`` in a
prepared package is what shows the link resolves; this module never fetches anything, and it never runs
Lean itself.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
import tomllib
from pathlib import Path

# The template's registered-seed record and pristine seed texts (harness/route_b.py:70-78).
SEEDS_RECORD = "seeds.json"
BASELINE_DIR = "baseline"
# The package configuration a run needs beside the seeds: the lakefile (targets and the mathlib
# requirement), the elan toolchain pin, and the resolved dependency manifest (route_b.py:70-78).
PACKAGE_CONFIG = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
# The pinned dependency cache, linked rather than copied.
CACHE = Path(".lake") / "packages"
ATTEMPT_DIR = "attempt-{attempt:03d}"


class PrepareError(Exception):
    """The attempt was not prepared. Either the request was refused before anything was written (an
    existing destination, or a template that does not hold the required seeds or package
    configuration), or the template changed under the copy, and the partially created attempt
    directories have been removed.
    """


def sha256_file(path: Path) -> str:
    """The SHA-256 of a file's exact bytes, streamed so a large file costs no extra memory."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def registered_seeds(template: Path) -> dict[str, str]:
    """The template's ``seeds.json``: flat seed module name -> recorded sha256 of its pristine text.

    The record is what the attempt's digests are checked against, so a malformed one is a refusal
    rather than a preparation whose ``seed_sha256`` no reader can compare to anything.
    """
    record_path = template / SEEDS_RECORD
    try:
        record = json.loads(record_path.read_text())
    except FileNotFoundError as error:
        raise PrepareError(f"template has no {SEEDS_RECORD}: {record_path}") from error
    except json.JSONDecodeError as error:
        raise PrepareError(f"{record_path} is not JSON: {error}") from error
    if not isinstance(record, dict) or not record:
        raise PrepareError(f"{record_path} does not record any seed digests")
    for name, digest in record.items():
        if Path(name).name != name or name in (".", ".."):
            raise PrepareError(f"{record_path} records {name!r}, which is not a flat module file name")
        if not isinstance(digest, str) or len(digest) != 64:
            raise PrepareError(f"{record_path} records {name!r} without a sha256 digest: {digest!r}")
    return record


def package_name(template: Path) -> str:
    """The lake package name in the template's ``lakefile.toml``, used as the prepared package's
    directory name. The template directory's own name is not it: the package identity a Lean
    invocation resolves is the lakefile's, and the prepared package is a real lake package.
    """
    lakefile = template / "lakefile.toml"
    try:
        name = tomllib.loads(lakefile.read_text()).get("name")
    except FileNotFoundError as error:
        raise PrepareError(f"template has no lakefile.toml: {lakefile}") from error
    except tomllib.TOMLDecodeError as error:
        raise PrepareError(f"{lakefile} is not TOML: {error}") from error
    if not isinstance(name, str) or Path(name).name != name or name in (".", ".."):
        raise PrepareError(f"{lakefile} has no usable package name: {name!r}")
    return name


def _checked_source(template: Path, relative: Path, digest: str) -> Path:
    """A template file the attempt copies, refused when it is absent or no longer hashes to its
    recorded pristine digest: a preparation that copied bytes the record does not pin would hand the
    run a baseline the seed's own digest rejects.
    """
    source = template / relative
    if not source.is_file():
        raise PrepareError(f"template is missing {relative}: {source}")
    found = sha256_file(source)
    if found != digest:
        raise PrepareError(
            f"{source} hashes to {found}, not the recorded {digest}: the seed is not the registered one"
        )
    return source


def _link_cache(template: Path, package: Path) -> None:
    """Symlink the prepared package's ``.lake/packages`` at the template's pinned cache. One link per
    attempt instead of a ≈7 GB copy, and the target is absolute so the package keeps resolving it
    wherever its workspace root lives.
    """
    cache = template / CACHE
    if not cache.is_dir():
        raise PrepareError(f"template has no pinned dependency cache to link: {cache}")
    (package / ".lake").mkdir()
    os.symlink(cache.resolve(), package / ".lake" / CACHE.name, target_is_directory=True)


def _check_package_contents(package: Path, expected: set[str]) -> None:
    """The package holds *only* the allowlisted entries: the copied modules, their baselines, the
    package configuration, ``seeds.json`` and ``.lake``. Checked rather than assumed, because a
    wholesale copy is exactly how a template's ``.runs/``, promoted target or closure copy would
    reappear in a "clean" attempt.
    """
    found = {entry.name for entry in package.iterdir()}
    extra = sorted(found - expected)
    missing = sorted(expected - found)
    if extra or missing:
        raise PrepareError(
            f"{package} holds {sorted(found)}, not only the allowlisted entries {sorted(expected)}"
            + (f" (unexpected {extra})" if extra else "")
            + (f" (missing {missing})" if missing else "")
        )


def prepare(
    *,
    template: Path,
    seed: str,
    attempt: int,
    workspace_root: Path,
    results_root: Path,
) -> dict:
    """Prepare the attempt and return its receipt. See the module docstring for what it asserts.

    The workspace and results destinations are created exclusively: an existing one is a refusal, so
    re-running the same attempt cannot overwrite the attempt it prepared. Anything this function
    created before it failed is removed, leaving a retry possible rather than a half-built directory
    that later refuses every attempt.
    """
    template = template.resolve()
    if not template.is_dir():
        raise PrepareError(f"template is not a directory: {template}")
    if attempt < 1:
        raise PrepareError(f"--attempt must be at least 1, got {attempt}")

    name = package_name(template)
    seeds = registered_seeds(template)
    if seed not in seeds:
        raise PrepareError(
            f"{template / SEEDS_RECORD} does not record {seed}: recorded seeds are {sorted(seeds)}"
        )
    seed_digest = seeds[seed]
    # Every registered seed and its baseline must still be the recorded pristine text: the attempt's
    # package carries exactly that set, so a stale one would be copied in the same step.
    sources = {}
    for registered, digest in sorted(seeds.items()):
        sources[Path(registered)] = _checked_source(template, Path(registered), digest)
        sources[Path(BASELINE_DIR) / registered] = _checked_source(
            template, Path(BASELINE_DIR) / registered, digest
        )

    # The package configuration is checked before any destination exists, so an incompletely
    # provisioned template is a diagnosed refusal (exit 2) rather than an I/O failure raised from the
    # copy below, which would report a run that never started. The copies stay inside the cleanup
    # ``try`` for the race where a member disappears after this check.
    for config in PACKAGE_CONFIG:
        if not (template / config).is_file():
            raise PrepareError(f"template is missing {config}: {template / config}")

    attempt_dir = Path(ATTEMPT_DIR.format(attempt=attempt))
    workspace = (workspace_root / attempt_dir).resolve()
    results = (results_root / attempt_dir).resolve()
    for destination in (workspace, results):
        if destination.exists():
            raise PrepareError(
                f"refusing to overwrite the existing attempt destination {destination}; "
                "prepare a different --attempt"
            )
    if results.is_relative_to(workspace) or workspace.is_relative_to(results):
        raise PrepareError(
            f"the attempt workspace {workspace} and its results {results} are not disjoint: the "
            f"per-attempt {attempt_dir} directories must not nest, whatever the parent roots"
        )

    package = workspace / name
    created: list[Path] = []
    try:
        # Exclusive creation is the no-overwrite gate: one of these fails rather than replacing an
        # existing attempt, whatever the check just above raced with.
        for destination in (workspace, results):
            destination.mkdir(parents=True, exist_ok=False)
            created.append(destination)

        package.mkdir()
        for relative, source in sorted(sources.items()):
            target = package / relative
            target.parent.mkdir(exist_ok=True)
            shutil.copyfile(source, target)
        for config in PACKAGE_CONFIG:
            shutil.copyfile(template / config, package / config)
        shutil.copyfile(template / SEEDS_RECORD, package / SEEDS_RECORD)
        _link_cache(template, package)

        _check_package_contents(
            package,
            {relative.parts[0] for relative in sources} | set(PACKAGE_CONFIG) | {SEEDS_RECORD, ".lake"},
        )
        # Hash the bytes the attempt will actually work from, and require them to be the registered
        # seed: the receipt's digest is a statement about the copied file, not about the template.
        copied = sha256_file(package / seed)
        if copied != seed_digest:
            raise PrepareError(
                f"the copied seed {package / seed} hashes to {copied}, not the registered {seed_digest}"
            )
    except BaseException:
        # Only the destinations this call created are removed; a pre-existing attempt is untouched.
        for destination in reversed(created):
            shutil.rmtree(destination, ignore_errors=True)
        raise

    return {
        "attempt": attempt,
        "package": str(package),
        "seed": str(package / seed),
        "results": str(results),
        "seed_sha256": copied,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="harness.attempt_workspace",
        description="Prepare one clean, independent proof attempt package per attempt.",
    )
    commands = parser.add_subparsers(dest="command", required=True)
    prepare_parser = commands.add_parser(
        "prepare",
        help="copy the registered seeds and package config into a fresh per-attempt package",
        description=(
            "Create <workspace-root>/attempt-NNN/<package> holding only the registered modules, their "
            "baselines, seeds.json, the lake package config and a symlink to the pinned dependency "
            "cache, with a separate empty <results-root>/attempt-NNN, and print the JSON receipt."
        ),
    )
    prepare_parser.add_argument("--template", required=True, help="the source Lean package to prepare from")
    prepare_parser.add_argument("--seed", required=True, help="the registered seed module to attempt")
    prepare_parser.add_argument("--attempt", required=True, type=int, help="the attempt number (1, 2, …)")
    prepare_parser.add_argument(
        "--workspace-root", required=True, help="the root holding each attempt's clean package"
    )
    prepare_parser.add_argument(
        "--results-root", required=True, help="the root for each attempt's own results, outside its package"
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        receipt = prepare(
            template=Path(args.template),
            seed=args.seed,
            attempt=args.attempt,
            workspace_root=Path(args.workspace_root),
            results_root=Path(args.results_root),
        )
    except PrepareError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(json.dumps(receipt))
    return 0


if __name__ == "__main__":
    sys.exit(main())
