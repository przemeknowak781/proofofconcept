#!/usr/bin/env bash
# Build, then fail on placeholders, on any axiom outside the three standard ones, on a control
# that does not behave as stated, and on a kernel-replay failure.
# Run from anywhere after `lake exe cache get` in this directory.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
if grep -n -E '\bsorry\b|\badmit\b|^axiom\b|native_decide' TreeEntropy/*.lean TreeEntropy.lean \
    | grep -v 'no `native_decide`'; then
  echo "FAIL: placeholder or extra axiom keyword found" >&2; exit 1
fi
report="$(lake env lean scripts/PrintAxioms.lean 2>&1)"
expected="$(grep -c '^#print axioms' scripts/PrintAxioms.lean)"
n_all="$(printf '%s\n' "$report" | grep -c -E "depends on axioms|does not depend on any axioms" || true)"
# every reported axiom must be one of the three standard ones (a subset is fine)
bad="$(printf '%s\n' "$report" | grep 'depends on axioms' | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' \
  | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v -x -E 'propext|Classical\.choice|Quot\.sound' || true)"
if [ "$n_all" -ne "$expected" ] || [ -n "$bad" ]; then
  echo "FAIL: $n_all axiom reports, expected $expected; non-standard axioms: [$bad]" >&2
  printf '%s\n' "$report" >&2; exit 1
fi
# positive controls: tightness at d = 4 and two refuted entries
lake env lean scripts/Controls.lean
# negative control: a false table entry must be rejected, and for the right reason
out="$(lake env lean scripts/MustFail.lean 2>&1)" && { echo "FAIL: scripts/MustFail.lean compiled" >&2; exit 1; }
if ! printf '%s\n' "$out" | grep -q 'is false'; then
  echo "FAIL: scripts/MustFail.lean failed for an unexpected reason" >&2; printf '%s\n' "$out" >&2; exit 1
fi
for m in Sum OneVar Table Large Main Darts APriori Sharp; do
  lake env leanchecker "TreeEntropy.$m"
done
echo "OK: build, $expected axiom reports, controls, kernel replay of 8 modules"
