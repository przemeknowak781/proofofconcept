#!/usr/bin/env bash
# Full check of the package: build, source scan, axiom reports, kernel replay.
set -euo pipefail
cd "$(dirname "$0")/.."
LOG="$(mktemp -d)"

MODULES="Kenyon.Levels Kenyon.Green Kenyon.Super Kenyon.BetheFun Kenyon.OneStep Kenyon.LogDet
Kenyon.Lap Kenyon.Bethe Kenyon.Forest Kenyon.MatrixTree Kenyon.Count Kenyon.Amplify
Kenyon.Contract Kenyon.Main Kenyon.ForestCount Kenyon.MatrixTree2 Kenyon.Regular Kenyon.Cayley
Kenyon.Sanov Kenyon.Sharp Kenyon.Examples TreeEntropy.OneVar TreeEntropy.Table TreeEntropy.Large
TreeEntropy.Sharp TreeEntropy.Sum TreeEntropy.Darts TreeEntropy.APriori TreeEntropy.Main"

lake build 2>&1 | grep -v 'module system' | tee $LOG/build.log | tail -3
if grep -qE '^error|: error' $LOG/build.log; then echo "FAIL: build"; exit 1; fi

if grep -rnE '\bsorry\b|\badmit\b|^\s*axiom\b|native_decide' --include='*.lean' Kenyon TreeEntropy \
     | grep -v 'no `native_decide`' ; then
  echo "FAIL: placeholder, axiom or native_decide in the sources"; exit 1
fi

lake env lean scripts/PrintAxioms.lean > $LOG/axioms.log 2>&1 || { cat $LOG/axioms.log; echo "FAIL: PrintAxioms"; exit 1; }
REPORTS=$(grep -c "depends on axioms\|does not depend on any axioms" $LOG/axioms.log || true)
EXPECTED=$(grep -c '^#print axioms' scripts/PrintAxioms.lean)
if [ "$REPORTS" != "$EXPECTED" ]; then cat $LOG/axioms.log; echo "FAIL: $REPORTS reports, expected $EXPECTED"; exit 1; fi
if grep "depends on axioms" $LOG/axioms.log | grep -vE '^\S+ depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'; then
  echo "FAIL: unexpected axiom"; exit 1
fi

N=0
for m in $MODULES; do
  lake env leanchecker "$m" > $LOG/checker.log 2>&1 || { cat $LOG/checker.log; echo "FAIL: leanchecker $m"; exit 1; }
  N=$((N+1))
done

echo "OK: build, $REPORTS axiom reports, kernel replay of $N modules"
