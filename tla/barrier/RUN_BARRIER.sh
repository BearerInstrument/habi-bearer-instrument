#!/bin/bash
set -e
STAMP=$(date +%F_%H%M)
mkdir -p TLC-output
JAR=${JAR:-../tla2tools.jar}
if [ ! -f "$JAR" ]; then JAR=tla2tools.jar; fi

echo "=== 1. PAIRWISE (must PASS) ==="
java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
  -config BARRIER_PAIRWISE.cfg DIL_CRDT_Barrier.tla -workers auto \
  2>&1 | tee TLC-output/barrier-pairwise-${STAMP}.log

echo ""
echo "=== 2. GLOBAL FAIL (expect violation) ==="
java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
  -config BARRIER_GLOBAL_FAIL.cfg DIL_CRDT_Barrier.tla -workers auto \
  2>&1 | tee TLC-output/barrier-global-fail-${STAMP}.log

echo ""
echo "=== 3. FULL (must PASS) ==="
java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
  -config BARRIER_FULL.cfg DIL_CRDT_Barrier.tla -workers auto \
  2>&1 | tee TLC-output/barrier-full-${STAMP}.log

echo ""
echo "=== SUMMARY ==="
grep -E "No error|Invariant.*violated|states generated|distinct states|0 states left" TLC-output/*.log
