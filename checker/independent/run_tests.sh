#!/bin/bash
# generic tests of the second program (test kernel: testdata/v15fix.r1.json); logs in runs/tests/
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
mkdir -p runs/tests
sha256sum hl_core.py hl_check.py quad_A.py e2e_check.py audit_spec.py test_core.py test_check.py test_out.py test_c12.py test_guards.py > runs/tests/sha256.txt
for t in test_core test_check test_out test_c12 test_guards; do nice -n 10 $PY -I $t.py > runs/tests/$t.log 2>&1; echo "$t rc=$?" >> runs/tests/sha256.txt; done
echo TESTSDONE > runs/tests/done.flag
