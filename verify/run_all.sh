#!/bin/sh
# Runs every check. Needs g++ and python3. About 2-3 minutes on a machine with many cores.
set -e
cd "$(dirname "$0")"; J=${JOBS:-$(nproc)}; W=$(mktemp -d)
g++ -O2 -o "$W/finite" finite.cpp; g++ -O2 -o "$W/kappa" kappa.cpp
echo "== Lemmas 7 and 8 (numerical test)";          python3 -I lemma_check.py
echo "== n < 1500^2, exact";                        "$W/finite" exact 1500 8
echo "== 1500 <= s < 10^9";                         python3 -I -c '
a=1500
while a<10**9:
    b=min((a//(2*10**7)+1)*2*10**7,10**9); print(a,b); a=b' | xargs -P "$J" -L 1 sh -c '"$0" range "$1" "$2" 40' "$W/finite" | sort -t'[' -k2 -n > "$W/out"
python3 -I -c '
import re,sys
r=sorted(tuple(map(int,re.match(r"s in \[(\d+),(\d+)\): omega >= (\d+)",l).groups())) for l in open(sys.argv[1]))
assert r[0][0]==1500 and r[-1][1]==10**9 and all(r[i][1]==r[i+1][0] for i in range(len(r)-1))
print("whole range covered, omega >=",min(t[2] for t in r))' "$W/out"
echo "== second program";                           python3 -I verify2.py exact 30000
python3 -I -c '
for a in range(1500,4000001,200000): print(a,min(a+200000,4000001))' | xargs -P "$J" -L 1 python3 -I verify2.py range | sort -t'[' -k2 -n | awk '{print $6}' | sort -n | uniq -c | sed 's/^/blocks with omega >= /'
echo "== sets in the corollaries";                  python3 -I sets.py
echo "== all k <= 24";                              "$W/kappa" 2250000 24
echo "== exact Bernoulli numbers, n <= 5100";       python3 -I direct_bernoulli.py 5100
rm -rf "$W"
