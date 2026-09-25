#!/usr/bin/env bash
# Self-contained replay of the pre-implementation red runs for the
# published-human-baseline phase.
#
#   bash docs/redrun-replay.sh [output-dir]      # default /tmp/redrun-out
#
# Run from the repository root.  Needs only git, python3 and the dev shell
# (nix develop).  It reconstructs the two tree states the red runs were
# observed in, runs the named pytest commands with COLUMNS pinned (so pytest
# does not truncate its own summary lines to a terminal width), and writes one
# raw stdout+stderr capture per stage into the output directory.
#
# PRE_PHASE is the commit *before* the published-human-baseline phase: the tree
# as it stood when the scenarios were written and the data did not yet exist.
# It is pinned rather than taken from HEAD so this recipe keeps working after
# the phase itself is committed.  a9275fb is that commit.
PRE_PHASE=a9275fb
REPO=$(pwd)
OUT=${1:-/tmp/redrun-out}
A=/tmp/redrun-A
B=/tmp/redrun-B

rm -rf "$A" "$B" "$OUT"
mkdir -p "$A" "$B" "$OUT"

# Stage A: the pre-implementation tree plus the two scenario files.
git archive "$PRE_PHASE" | tar -x -C "$A"
for f in tests/ewd998-cfg-contract.md tests/test_ewd998_cfg.py \
         tests/human-baseline-contract.md tests/test_human_baseline.py; do
  cp "$REPO/$f" "$A/$f"
done

# Stage B: stage A plus the imported spec data, and the human records with the
# top-level "calibration" key removed (the state after implementation step 5,
# before step 6's calibration run).
cp -r "$A/." "$B/"
mkdir -p "$B/specs/tla" "$B/results"
for d in ewd998 ewd998-paper ijcar2010; do
  cp -r "$REPO/specs/tla/$d" "$B/specs/tla/$d"
done
python3 - "$REPO/results/human.jsonl" "$B/results/human.jsonl" <<'PY'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
with open(dst, "w") as out:
    for line in open(src):
        if not line.strip():
            continue
        rec = json.loads(line)
        rec.pop("calibration", None)      # top-level key of the record
        out.write(json.dumps(rec) + "\n")
PY

run() {   # run <capture-name> <tree> <pytest-args...>
  local name=$1 tree=$2; shift 2
  {
    echo "\$ cd $tree"
    echo "\$ nix develop -c pytest $*"
    ( cd "$tree" && COLUMNS=200 nix develop -c pytest "$@" ) 2>&1
    echo "exit=$?"
  } > "$OUT/$name.txt"
}

run stage-a  "$A" tests/test_ewd998_cfg.py tests/test_human_baseline.py -q
run stage-b1 "$B" tests/test_ewd998_cfg.py -q
run stage-b2 "$B" tests/test_human_baseline.py -q

echo "captures written to $OUT:"; wc -l "$OUT"/stage-*.txt
