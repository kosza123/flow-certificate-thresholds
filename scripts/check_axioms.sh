#!/usr/bin/env bash
# Reads `#print axioms` output on stdin and fails unless
#  (a) there is exactly one result line per `#print axioms` command in scripts/PrintAxioms.lean, and
#  (b) every declaration depends only on propext, Classical.choice and Quot.sound (or on no axioms).
set -euo pipefail
cd "$(dirname "$0")/.."
allowed=" propext Classical.choice Quot.sound "
expected=$(grep -c '^#print axioms ' scripts/PrintAxioms.lean)
out=$(cat)
printf '%s\n' "$out"
results=$(printf '%s\n' "$out" | grep -E "depends on axioms: \[|does not depend on any axioms" || true)
count=$(printf '%s' "$results" | grep -c . || true)
if [ "$count" -ne "$expected" ]; then
  echo "FAIL: expected $expected axiom reports, got $count"; exit 1
fi
bad=0
while IFS= read -r line; do
  case "$line" in *"does not depend on any axioms"*) continue ;; esac
  list=${line#*depends on axioms: [}; list=${list%]*}
  for ax in ${list//,/ }; do
    case "$allowed" in *" $ax "*) ;; *) echo "FAIL: unexpected axiom '$ax' in: $line"; bad=1 ;; esac
  done
done <<< "$results"
[ "$bad" -eq 0 ] || exit 1
echo "axioms ok: $count declarations, all within {propext, Classical.choice, Quot.sound}"
