#!/bin/bash
# Axiom audit: every audited theorem must depend on exactly the three standard
# axioms, and the source tree must be free of sorry / admit / native_decide.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== source hygiene =="
if grep -rnE '\b(sorry|admit|native_decide)\b' P287/ Check.lean --include='*.lean' \
    | grep -vE '^\S+:[0-9]+:.*--' \
    | grep -vE '(does not admit|bare `sorry`|admit no|tagged .research solved.)' ; then
  echo "FAIL: forbidden token found above"; exit 1
fi
echo "clean"

echo "== axiom audit =="
OUT=$(lake env lean Check.lean --tstack=200000 2>&1)
echo "$OUT"
LINES=$(echo "$OUT" | grep -c "depends on axioms" || true)
BAD=$(echo "$OUT" | grep "depends on axioms" \
  | grep -vcF "[propext, Classical.choice, Quot.sound]" || true)
if [ "$LINES" -ne 23 ] || [ "$BAD" -ne 0 ]; then
  echo "FAIL: expected 23 clean axiom lines, got $LINES lines with $BAD bad"; exit 1
fi
echo "OK: 23/23 theorems depend on exactly [propext, Classical.choice, Quot.sound]"
