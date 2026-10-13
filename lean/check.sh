#!/bin/sh
set -e
cd "$(dirname "$0")"
lake build
lake env lean Check.lean | python3 tests/axioms.py --final
python3 tests/enc63hash.py "${1:-40}"
if [ "${1:-40}" = all ]; then python3 tests/audit364.py --all; else python3 tests/audit364.py --sample "${1:-40}"; fi
python3 tests/difftest.py
