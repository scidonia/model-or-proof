#!/usr/bin/env bash
# Chain: wait for the remediation run to exit, then audit each arm in sequence, committing every arm's
# audit and rows together.
#
# Why a chain rather than a reminder: `paxos-remediation` is detached, so its completion reaches nobody.
# This process is the trigger, its own completion is a visible service exit, and every commit it makes is
# checkable afterwards.
#
# It touches neither `harness/*.py` (a harness edit would invalidate the revision record the arms are
# checked against) nor `remediation-run.sh` (in flight). It only runs the audit and commits.
set -u
cd /home/gavin/dev/model-or-proof || exit 1

RUN_PID=4014186
echo "waiting for the remediation run (pid ${RUN_PID}) to exit"
while kill -0 "${RUN_PID}" 2>/dev/null; do sleep 20; done
echo "remediation exited; auditing every arm"

for arm in tok2 bak2 lcr2 ewd2 bak1 lcr1; do
  echo "=== ${arm} ==="
  PYTHONDONTWRITEBYTECODE=1 nix develop -c python -m scripts.audit_attempts \
    --sessions results/remediation/"${arm}"/results \
    --expect-revision results/remediation/revision.json > results/remediation/"${arm}"/audit.txt 2>&1
  text_status=$?
  PYTHONDONTWRITEBYTECODE=1 nix develop -c python -m scripts.audit_attempts \
    --sessions results/remediation/"${arm}"/results \
    --expect-revision results/remediation/revision.json --json > results/remediation/"${arm}"/audit.json 2>&1
  json_status=$?
  echo "audit exit: text=${text_status} json=${json_status}"
  cat results/remediation/"${arm}"/audit.txt

  git add results/remediation/"${arm}"
  if git diff --cached --quiet; then
    echo "nothing staged for ${arm}"
  else
    git commit -q -m "Audit the ${arm} arm before reading its rows

The per-arm transcript audit ran with the revision record and is committed with
the arm's rows, so the arm's verdict is fixed before anything is read from the
rows. Exit status text=${text_status} json=${json_status}: 0 all attempts clean,
1 at least one contaminated, 2 unaudited or the revision split. The three
withholding classes and the all-attempt distributions are reported separately
when these rows are interpreted."
    echo "committed ${arm}"
  fi
done

echo "AUDIT-DONE"
