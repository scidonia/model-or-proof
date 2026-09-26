#!/usr/bin/env python3
"""Promote a closed Route B artifact into the committed seed (plan D10/D13/D15).

The tier-1 run instantiates the tier-2 result, and the repl loads the *olean* of the module it imports:
so the proved text has to exist as a module on disk before `mutex_n0` can rest on it, and before `lake
build` can produce an olean that says so (plan D10's tier ordering) — as `<Stem>Proved.lean`, a new
module, never the seed's own path (the planner's ruling, after the incident of 2026-09-26). A run never
writes the committed seed (plan D15) — it works on `.runs/<stem>-r<N>.lean` — so promotion is an explicit,
human-run step between the tiers, and this script is it.

    nix develop -c python3 scripts/promote.py <closed-artifact> <seed>

What it does, in order:

1. **Checks the artifact.** It must be a closed proof (no `sorry`/`Admitted`/`axiom`), an artifact
   whose hash matches the one **the row recorded at run time** — the row is the run's own evidence of
   what it wrote, because a human or another run can write over the file between the run and the
   promotion — and a *faithful* closure of the seed's recorded baseline: the same declarations, the
   same statements, with only the goal's `sorry` replaced by a proof. Declarations the artifact
   *added* are the loop's own work — a helper the model guessed and then proved — so they promote; a
   changed statement, a changed value or a dropped declaration is a rewrite no loop tactic can
   produce, and is refused rather than recorded as the new baseline (plan D5/D19).
2. **Writes the proof to a new module, and the record:** the proved text goes to `<Stem>Proved.lean`, a
   module of its own, and `seeds.json` receives both that module's sha256 and the seed's. The seed's own
   digest is *unchanged* — the seed is never written — so the record is idempotent by construction, and
   nothing proved sits at a seed's path for a mistaken `--record-baseline` to accept (the planner's
   ruling, after the incident of 2026-09-26). The pristine text in `baseline/<file>` is left alone too:
   it keeps the `sorry` text forever, so every run re-seeds from it and a promoted baseline cannot
   masquerade as a zero-turn "closed". It is a copy of a seed that still exists rather than the last
   line of defence.
3. **Runs `lake build`** through the harness's own runner, so the olean the tier-1 run loads reflects
   the promoted proof. A build that fails is loud — the tree keeps the promoted files, and the next run
   refuses on its own failed build rather than measuring a stale olean.

Exit codes: 0 promoted; 1 the artifact is not closed; 8 the build failed; 9 the seed has no recorded
baseline; 11 the artifact is not a faithful closure of it; 13 no row records this artifact's hash, or
the file no longer matches the hash its row recorded.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.closure import detect_assisted  # noqa: E402
from harness.lean_repl import count_unclosed  # noqa: E402
from harness import route_b  # noqa: E402

# The artifact rewrote the statement instead of proving it: not a rig failure and not a prover failure,
# but a promotion this tool refuses. It shares the harness's exit-code namespace with `route_b`'s codes
# (1, 8, 9 are its), so a scripted caller reads one table of meanings.
EXIT_UNFAITHFUL = 11

# The artifact on disk is not the one the run recorded: a human, or another run, has written over it
# since. Its own code, because it is a different thing from an unfaithful proof — the proof may be
# perfectly faithful and still not be the run's.
EXIT_UNVERIFIED = 13

# Where the rows live: promotion's evidence for "this is the artifact that run produced" is the row the
# run appended, never the file on disk, which anyone can rewrite between the run and the promotion.
DEFAULT_RESULTS = REPO / "results" / "proof.jsonl"


def recorded_sha256(artifact: Path, results: Path) -> str | None:
    """The hash the run's own row recorded for this artifact, or ``None`` when no row has it (D19).

    The row is the evidence: a human, or another run, can write over the artifact between the run and
    the promotion, so "this is the file that run produced" has to come from what the run recorded, not
    from the file itself. The *last* row naming this artifact is the run that wrote the file that is
    there now — repetitions reuse a path (`.runs/<stem>-r<N>.lean`) and each invocation sweeps and
    rewrites its copies — so the last entry is the current file's record, and its hash is the one to
    verify.
    """
    if not results.is_file():
        return None
    wanted = route_b.relative(artifact)
    recorded = None
    for line in results.read_text().splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        artifacts = row.get("artifacts") or {}
        if artifacts.get("proof") == wanted:
            recorded = artifacts.get("artifact_sha256")
    if isinstance(recorded, str):
        return recorded
    # A closure copy has no row of its own: rows name the working copy under `.runs/`, and this file is the
    # durable copy `route_b.write_closure_sidecar` wrote from the very snapshot the oracle checked. Its
    # digest and the row identity behind it are in the sidecar beside it (finding F6), so a row written
    # before `artifact_sha256` existed is still promotable — by the sidecar's evidence, not by skipping the
    # check. A sidecar that records a disagreement is refused: the pair is not evidence of anything.
    sidecar = artifact.with_suffix(".json")
    if not sidecar.is_file():
        return None
    try:
        evidence = json.loads(sidecar.read_text())
    except json.JSONDecodeError:
        return None
    if route_b.relative(Path(str(evidence.get("artifact", "")))) != wanted:
        return None
    if evidence.get("digests_agree") is False:
        print(
            f"{wanted}'s sidecar records that its digest disagrees with the row's: nothing is promoted "
            "from evidence that contradicts itself",
            file=sys.stderr,
        )
        return None
    digest = evidence.get("artifact_sha256")
    return digest if isinstance(digest, str) else None


def register_module(lakefile: Path, module: str) -> bool:
    """Add ``module`` to the package's library targets; report whether the file changed.

    A new module with no ``[[lean_lib]]`` entry compiles to nothing, so every ``import`` of it fails with
    "unknown module prefix". That failure is loud — the build refuses, which is the point — but a
    promotion that leaves the tree unbuildable has not finished its job, so this runs before the build.
    Idempotent: a module already named is left alone, and a file with no ``[[require]]`` marker gets the
    entry appended.
    """
    text = lakefile.read_text()
    if f'name = "{module}"' in text:
        return False
    text = text.replace("defaultTargets = [", f'defaultTargets = ["{module}", ', 1)
    # The marker is *line-anchored*: the bare string `[[require]]` also occurs inside prose comments (it
    # did, and an unanchored replace split a comment line in half rather than inserting a table, which the
    # TOML parser then refused). `\n[[require]]` matches the table and nothing else.
    entry = f'\n[[lean_lib]]\nname = "{module}"\n'
    marker = "\n[[require]]"
    text = text.replace(marker, entry + marker, 1) if marker in text else text.rstrip() + "\n" + entry
    lakefile.write_text(text)
    return True


def promote(artifact: Path, seed: Path, results: Path = DEFAULT_RESULTS) -> int:
    """Promote ``artifact`` into ``seed`` and report the exit code (see the module docstring)."""
    try:
        baseline = route_b.load_baseline(seed)
    except route_b.Refusal as refusal:
        print(refusal.message, file=sys.stderr)
        return refusal.code
    if not artifact.is_file():
        print(f"{artifact} is not a file: nothing to promote", file=sys.stderr)
        return route_b.EXIT_UNCLOSED_ARTIFACT
    data = artifact.read_bytes()
    text = data.decode()
    # The run's own record of what it wrote, checked before anything is believed about the proof's
    # content: a faithful-looking artifact that is not the one the row names is not this run's result.
    recorded = recorded_sha256(artifact, results)
    if recorded is None:
        print(
            f"no row in {results} records an artifact hash for {route_b.relative(artifact)}: a "
            "promotion pins the artifact a run produced, and there is no run here to believe (plan D19)",
            file=sys.stderr,
        )
        return EXIT_UNVERIFIED
    actual = hashlib.sha256(data).hexdigest()
    if actual != recorded:
        print(
            f"{route_b.relative(artifact)} hashes to {actual}, not the {recorded} its row recorded: "
            "the artifact has changed since the run, so it is not what the run proved (plan D19)",
            file=sys.stderr,
        )
        return EXIT_UNVERIFIED
    unclosed = count_unclosed(text)
    if unclosed:
        print(
            f"{artifact} still contains {unclosed} sorry/Admitted/axiom: a promotion pins a proof, "
            "not a hole (plan D13)",
            file=sys.stderr,
        )
        return route_b.EXIT_UNCLOSED_ARTIFACT
    # `human=False`: the declarations the artifact added are the loop's own work (plan D19) — a helper
    # the model guessed and then proved — so promotion accepts them, exactly as the run's row marked
    # them unassisted. What promotion still refuses is a *rewrite*: a changed or missing declaration is
    # something no loop tactic can do, so a human did it, and blessing that would pin a different
    # statement into the record.
    difference = detect_assisted(baseline.text, text, human=False)
    if difference["assisted"]:
        changed = difference["changed_declarations"] + difference["missing_declarations"]
        print(
            f"{artifact} is not a faithful closure of {seed}'s recorded baseline: "
            f"{', '.join(changed)} differs. Promotion replaces a `sorry` with a proof, never the "
            "statement, and never drops one (plan D5)",
            file=sys.stderr,
        )
        return EXIT_UNFAITHFUL
    digest = hashlib.sha256(text.encode()).hexdigest()
    # The proof goes to a **new module**, never to the seed's path (D15 as ruled after the incident this
    # afternoon): a promotion must leave nothing proved where a seed belongs, so a mistaken
    # `--record-baseline` has nothing to accept, and `baseline/` becomes a copy of a seed that still
    # exists rather than the last line of defence. The seed's digest is therefore unchanged across a
    # promotion, and the record is re-pinned to that unchanged digest — idempotent by construction.
    proved = seed.with_name(f"{seed.stem}Proved{seed.suffix}")
    seed_text = seed.read_text()
    proved.write_text(text)
    seed_digest = hashlib.sha256(seed_text.encode()).hexdigest()
    if seed_text != baseline.text:
        # The seed no longer matches the text it is pinned as: a caller edited it, so the promotion's
        # premise ("this proof closes *this* seed") is gone. Loud rather than absorbed.
        print(
            f"{seed} no longer matches its recorded baseline ({route_b.relative(seed)} is not the "
            "pinned text); a promotion proves the seed it was run against (plan D15)",
            file=sys.stderr,
        )
        return EXIT_UNVERIFIED
    record_path = seed.parent / route_b.SEEDS_RECORD
    record = json.loads(record_path.read_text())
    record[seed.name] = seed_digest
    record[proved.name] = digest
    record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    # `baseline/<file>` is deliberately **not** re-pinned (the planner's ruling): it keeps the `sorry`
    # text forever, so every run re-seeds from it. Re-pinning it would make the next tier-2 run copy a
    # closed file and "close" in zero turns — a rig artefact wearing the shape of a result. With the seed
    # itself untouched this is now a copy of a live input rather than the only record of one.
    if register_module(seed.parent / "lakefile.toml", proved.stem):
        print(f"registered {proved.stem} as a library target in {seed.parent.name}/lakefile.toml")
    try:
        build = route_b.run_lake_build(route_b.project_root(seed))
    except route_b.Refusal as refusal:
        print(refusal.message, file=sys.stderr)
        return refusal.code
    print(
        f"promoted {route_b.relative(artifact)} into {route_b.relative(proved)} "
        f"(sha256 {digest}), seed {route_b.relative(seed)} left byte-identical (sha256 {seed_digest}), "
        f"record re-pinned, baseline left pristine, lake build {build['seconds']}s"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="scripts/promote.py")
    parser.add_argument("artifact", help="the closed proof, e.g. proofs/lean/token-ring/.runs/TokenRing-r1.lean")
    parser.add_argument("seed", help="the committed seed it proves, e.g. proofs/lean/token-ring/TokenRing.lean")
    parser.add_argument(
        "--results",
        default=str(DEFAULT_RESULTS),
        help=(
            "the rows the run appended; the artifact is promoted only if its hash matches the one the "
            f"last row naming it recorded (default: {relative_to_repo(DEFAULT_RESULTS)})"
        ),
    )
    args = parser.parse_args(argv)
    return promote(Path(args.artifact), Path(args.seed), Path(args.results))


def relative_to_repo(path: Path) -> str:
    """A path as the rows and the CLI name it: relative to the repository when it is inside it."""
    return str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path)


if __name__ == "__main__":
    raise SystemExit(main())
