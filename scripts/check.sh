#!/usr/bin/env bash
# Full check of the formal development: build, forbidden tokens, axioms, kernel replay.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== toolchain";  cat lean-toolchain; lean --version
echo "== Mathlib cache"; lake exe cache get
echo "== build"; lake build
echo "== forbidden tokens (sorry, admit, axiom)"
if grep -rnwE "sorry|admit|axiom" PlanarCore PlanarCore.lean; then
  echo "FAIL: forbidden token found"; exit 1
fi
echo "none"
echo "== axioms"; lake env lean scripts/PrintAxioms.lean | ./scripts/check_axioms.sh
echo "== kernel replay (leanchecker)"
for m in Threshold Projection Assembly Fekete Necessity Graph Theorem1 Network Sanity Kirchhoff Certificate Final; do
  lake env leanchecker "PlanarCore.$m"
  echo "PlanarCore.$m: ok"
done
echo "ALL CHECKS PASSED"
