#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXE="$ROOT/.lake/build/bin/routea"
CASES="$ROOT/../data/allcheck/cases.jsonl"
cnf="$1"; prf="$2"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/leanchk.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
cat "$prf" > "$tmp/p.lrat"
h=$(shasum -a 256 "$cnf" | cut -d' ' -f1)
ref=$(awk -v h="$h" '$6 == h {print "364 " $1; exit}' "$ROOT/data/records364.tsv")
if [ -z "$ref" ]; then
  ref=$(python3 -c "
import json,sys
for l in open(sys.argv[1]):
    r=json.loads(l)
    if r['cnf_sha256']==sys.argv[2]: print('63', r['idx']); break" "$CASES" "$h")
fi
[ -n "$ref" ] || { echo "s UNKNOWN cnf"; exit 3; }
set -- $ref
"$EXE" "$1" "$2" "$tmp/lean.cnf" >/dev/null
[ "$(shasum -a 256 "$tmp/lean.cnf" | cut -d' ' -f1)" = "$h" ] || { echo "s MISMATCH lean term"; exit 4; }
"$EXE" "$1" "$2" "$tmp/lean.cnf" "$tmp/p.lrat" && echo "s VERIFIED (lean LRAT.check, $1 $2)"
