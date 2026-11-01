#!/bin/sh
# Runs the fast checks (about 1 minute in total).
# The long point-count check (about 3 minutes) is run separately:  python3 -I verify_yn_pure_python.py
cd "$(dirname "$0")" || exit 1
status=0
for s in verify_hand_proofs.py verify_kernel_theorem.py verify_recurrence_twins.py "verify_exact_forms_laws.py 7 8"; do
  echo "=== $s"
  python3 $s > /tmp/_chk.out 2>&1; rc=$?
  tail -2 /tmp/_chk.out
  [ $rc -eq 0 ] || { echo "FAILED: $s"; status=1; }
done
echo "=== census_exact_zero.py (expects: distinct cases: 27)"
python3 census_exact_zero.py | tail -1
echo "=== tvariant.py (expects 32 and 27 cases; 14 lose the deficiency)"
python3 tvariant.py | tail -2
exit $status
