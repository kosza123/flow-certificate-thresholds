#!/usr/bin/env bash
# One command to check the package.  Run from anywhere after `lake exe cache get` in this
# directory.  Fails on: a build error, a proof placeholder or extra axiom keyword in a source,
# any axiom outside the three standard ones, a kernel-replay failure.
set -euo pipefail
cd "$(dirname "$0")/.."
MODULES="DagCycleAssignment SubdivisionAssignment CorrelationCoverKernel AdapterCost AdapterFeatures AdapterBounds AdapterBirkhoff AdapterPaths AdapterTheorem AdapterPattern AdapterMain AdapterComplements"
SOURCES=""
for m in $MODULES; do SOURCES="$SOURCES $m.lean"; done

lake build

# placeholder scan (whole words; comments are scanned too, which is the stricter choice)
if grep -n -E '\bsorry\b|\badmit\b|^[[:space:]]*axiom\b|native_decide' $SOURCES; then
  echo "FAIL: placeholder or extra axiom keyword found" >&2; exit 1
fi

# axiom report: every reported axiom must be one of the three standard ones (a subset is fine)
report="$(lake env lean scripts/PrintAxioms.lean 2>&1 | tr '\n' ' ' | sed -E "s/'[^']*' (depends on axioms|does not depend on any axioms)/\n&/g")"
expected="$(grep -c '^#print axioms' scripts/PrintAxioms.lean)"
n_all="$(printf '%s\n' "$report" | grep -c -E "depends on axioms|does not depend on any axioms" || true)"
bad="$(printf '%s\n' "$report" | grep 'depends on axioms' | sed -E 's/.*depends on axioms: \[([^]]*)\].*/\1/' \
  | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
if [ "$n_all" -ne "$expected" ] || [ -n "$bad" ]; then
  echo "FAIL: $n_all axiom reports, expected $expected; non-standard axioms: [$bad]" >&2
  printf '%s\n' "$report" >&2; exit 1
fi

# kernel replay of every module (lean4checker is pinned in lake-manifest.json)
n_mod=0
for m in $MODULES; do
  lake exe lean4checker "$m"
  n_mod=$((n_mod + 1))
done
echo "OK: build, $expected axiom reports, kernel replay of $n_mod modules"
