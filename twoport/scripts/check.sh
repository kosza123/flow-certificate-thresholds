#!/usr/bin/env bash
# Build, then fail on placeholders, on any axiom outside the three standard ones, and on a
# kernel-replay failure.  Run from this directory after `lake exe cache get`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
if grep -n -E '\bsorry\b|\badmit\b|^axiom\b|native_decide' TwoPort/*.lean TwoPort.lean; then
  echo "FAIL: placeholder or extra axiom keyword found" >&2; exit 1
fi
report="$(lake env lean scripts/PrintAxioms.lean 2>&1 | grep 'depends on axioms' || true)"
n_all="$(printf '%s\n' "$report" | grep -c 'depends on axioms' || true)"
n_ok="$(printf '%s\n' "$report" | grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' || true)"
expected="$(grep -c '^#print axioms' scripts/PrintAxioms.lean)"
if [ "$n_all" -ne "$expected" ] || [ "$n_ok" -ne "$expected" ]; then
  echo "FAIL: axiom report $n_ok/$n_all, expected $expected" >&2; printf '%s\n' "$report" >&2; exit 1
fi
for m in Basic Subst Mobius Compose Growth Main H7; do
  lake env leanchecker "TwoPort.$m"
done
echo "OK: build, $expected axiom reports, kernel replay of 7 modules"
