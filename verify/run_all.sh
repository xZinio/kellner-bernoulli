#!/usr/bin/env bash
# Reruns every computation of the paper and checks every stated value.  Exits with a non-zero status
# if a program fails or a value is not reproduced.  Needs g++ and python3.  About 37 CPU-minutes, most
# of it for 4*10^6 <= s < 10^9 in Section 4; a few minutes on a machine with many cores (JOBS=... sets
# the number of parallel jobs).
# The proofs need the computation of Section 4 only for s < 678407, as (3.2) covers s >= 678407.  With QUICK=1 the
# script checks (4.1) only in that range (a few CPU-minutes in all), and not the range up to 10^9 stated in (4.1).
set -euo pipefail
cd "$(dirname "$0")"
J=${JOBS:-$(nproc)}
TIMEFORMAT='   (%R s wall, %U s user CPU)'
if [ -n "${QUICK:-}" ]; then SMAX=678407; STEP=100000; S2MAX=678407; else SMAX=1000000000; STEP=20000000; S2MAX=4000001; fi
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
g++ -O2 -o "$W/finite" finite.cpp
g++ -O2 -o "$W/kappa" kappa.cpp
g++ -O2 -o "$W/index" index.cpp

echo "== Lemmas 7 and 8 (numerical test)"
python3 -I lemma_check.py

echo "== n < 1500^2 from the definition: exceptions and b_1, ..., b_24 (Theorem 1)"
"$W/finite" exact 1500 24 > "$W/exact"
cat "$W/exact"
python3 -I check.py exact "$W/exact"

echo "== 1500 <= s < $SMAX: at most 16 of the first 40 primes above s are bad for any n in [s^2, s^2+2s] (4.1)"
if [ -n "${QUICK:-}" ]; then echo "   (QUICK: the range 678407 <= s < 10^9 of (4.1) is not checked; the proofs do not need it)"; fi
python3 -I check.py blocks 1500 "$SMAX" "$STEP" 40 > "$W/blocks"
time xargs -P "$J" -L 1 "$W/finite" range < "$W/blocks" > "$W/out"
python3 -I check.py ranges "$W/blocks" 24 "$W/out" 1726

echo "== the same for 1500 <= s < $S2MAX with the second program"
python3 -I verify2.py exact 80000
python3 -I check.py blocks 1500 "$S2MAX" 200000 > "$W/blocks2"
time xargs -P "$J" -L 1 python3 -I verify2.py range < "$W/blocks2" > "$W/out2"
python3 -I check.py ranges "$W/blocks2" 24 "$W/out2" 1726

echo "== the constants of Section 3, and Theorem 12 (uses (4.1) for 1500 <= s < 678407, checked above)"
time python3 -I omega_bound.py

echo "== the sets in the corollaries"
python3 -I sets.py

echo "== all k <= 24, m < 1500^2 (table in Corollary 4)"
"$W/kappa" 2250000 24 > "$W/kappa.out"
cat "$W/kappa.out"
python3 -I check.py kappa "$W/kappa.out"

echo "== the integral index a(n), n < 2^24: Theorem 10, Corollary 11, table of Corollary 4, data for Conjecture 14"
time "$W/index" 16777215 > "$W/index.out"
cat "$W/index.out"
python3 -I check.py index "$W/index.out"

echo "== exact Bernoulli numbers, n <= 5100"
python3 -I direct_bernoulli.py 5100

echo "== all checks passed"
