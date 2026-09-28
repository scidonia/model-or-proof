#!/usr/bin/env bash
# The six re-earned arms, one invocation per attempt, serial. Generated from the prepare receipts so
# every --proof path is the package the preparer actually built. Headline configuration: default arms,
# file mode, one repetition per invocation, no --exploratory (these replace headline cells).
set -u
cd /home/gavin/dev/model-or-proof || exit 1

echo "=== tok2 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/token-ring.json --proof /home/gavin/dev/model-or-proof/results/remediation/tok2/workspaces/attempt-001/token-ring/TokenRing.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/tok2/results/attempt-001
echo "=== tok2 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/token-ring.json --proof /home/gavin/dev/model-or-proof/results/remediation/tok2/workspaces/attempt-002/token-ring/TokenRing.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/tok2/results/attempt-002
echo "=== tok2 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/token-ring.json --proof /home/gavin/dev/model-or-proof/results/remediation/tok2/workspaces/attempt-003/token-ring/TokenRing.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/tok2/results/attempt-003
echo "=== tok2 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/token-ring.json --proof /home/gavin/dev/model-or-proof/results/remediation/tok2/workspaces/attempt-004/token-ring/TokenRing.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/tok2/results/attempt-004
echo "=== tok2 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/token-ring.json --proof /home/gavin/dev/model-or-proof/results/remediation/tok2/workspaces/attempt-005/token-ring/TokenRing.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/tok2/results/attempt-005
echo "=== bak2 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak2/workspaces/attempt-001/bakery/Bakery.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak2/results/attempt-001
echo "=== bak2 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak2/workspaces/attempt-002/bakery/Bakery.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak2/results/attempt-002
echo "=== bak2 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak2/workspaces/attempt-003/bakery/Bakery.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak2/results/attempt-003
echo "=== bak2 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak2/workspaces/attempt-004/bakery/Bakery.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak2/results/attempt-004
echo "=== bak2 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak2/workspaces/attempt-005/bakery/Bakery.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak2/results/attempt-005
echo "=== lcr2 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr2/workspaces/attempt-001/lcr/LCR.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr2/results/attempt-001
echo "=== lcr2 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr2/workspaces/attempt-002/lcr/LCR.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr2/results/attempt-002
echo "=== lcr2 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr2/workspaces/attempt-003/lcr/LCR.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr2/results/attempt-003
echo "=== lcr2 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr2/workspaces/attempt-004/lcr/LCR.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr2/results/attempt-004
echo "=== lcr2 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr2/workspaces/attempt-005/lcr/LCR.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr2/results/attempt-005
echo "=== ewd2 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/ewd998.json --proof /home/gavin/dev/model-or-proof/results/remediation/ewd2/workspaces/attempt-001/ewd998/EWD998.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/ewd2/results/attempt-001
echo "=== ewd2 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/ewd998.json --proof /home/gavin/dev/model-or-proof/results/remediation/ewd2/workspaces/attempt-002/ewd998/EWD998.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/ewd2/results/attempt-002
echo "=== ewd2 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/ewd998.json --proof /home/gavin/dev/model-or-proof/results/remediation/ewd2/workspaces/attempt-003/ewd998/EWD998.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/ewd2/results/attempt-003
echo "=== ewd2 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/ewd998.json --proof /home/gavin/dev/model-or-proof/results/remediation/ewd2/workspaces/attempt-004/ewd998/EWD998.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/ewd2/results/attempt-004
echo "=== ewd2 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/ewd998.json --proof /home/gavin/dev/model-or-proof/results/remediation/ewd2/workspaces/attempt-005/ewd998/EWD998.lean --mode file --tier 2 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/ewd2/results/attempt-005
echo "=== bak1 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak1/workspaces/attempt-001/bakery/BakeryN0.lean --mode file --tier 1 --param-N 9 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak1/results/attempt-001
echo "=== bak1 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak1/workspaces/attempt-002/bakery/BakeryN0.lean --mode file --tier 1 --param-N 9 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak1/results/attempt-002
echo "=== bak1 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak1/workspaces/attempt-003/bakery/BakeryN0.lean --mode file --tier 1 --param-N 9 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak1/results/attempt-003
echo "=== bak1 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak1/workspaces/attempt-004/bakery/BakeryN0.lean --mode file --tier 1 --param-N 9 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak1/results/attempt-004
echo "=== bak1 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/bakery.json --proof /home/gavin/dev/model-or-proof/results/remediation/bak1/workspaces/attempt-005/bakery/BakeryN0.lean --mode file --tier 1 --param-N 9 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/bak1/results/attempt-005
echo "=== lcr1 attempt-001 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr1/workspaces/attempt-001/lcr/LCRN0.lean --mode file --tier 1 --param-N 10 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr1/results/attempt-001
echo "=== lcr1 attempt-002 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr1/workspaces/attempt-002/lcr/LCRN0.lean --mode file --tier 1 --param-N 10 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr1/results/attempt-002
echo "=== lcr1 attempt-003 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr1/workspaces/attempt-003/lcr/LCRN0.lean --mode file --tier 1 --param-N 10 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr1/results/attempt-003
echo "=== lcr1 attempt-004 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr1/workspaces/attempt-004/lcr/LCRN0.lean --mode file --tier 1 --param-N 10 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr1/results/attempt-004
echo "=== lcr1 attempt-005 ==="
nix develop -c python -m harness.route_b --task tasks/lcr.json --proof /home/gavin/dev/model-or-proof/results/remediation/lcr1/workspaces/attempt-005/lcr/LCRN0.lean --mode file --tier 1 --param-N 10 --reps 1 --results /home/gavin/dev/model-or-proof/results/remediation/lcr1/results/attempt-005
echo "REMEDIATION-DONE"
