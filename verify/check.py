# Helpers for run_all.sh: splits ranges into blocks, and checks the output of the programs against the
# values stated in the paper.  Every check prints what it verified; on any mismatch it prints
# "CHECK FAILED: ..." and exits with status 1.
#   python3 check.py blocks LO HI STEP [EXTRA ...]    print "a b EXTRA..." for blocks partitioning [LO, HI)
#   python3 check.py ranges BLOCKS NEED OUT [WITNESS]  output of `finite range` / `verify2.py range`
#   python3 check.py exact OUT                         output of `finite exact 1500 24`
#   python3 check.py kappa OUT                         output of `kappa 2250000 24`
#   python3 check.py index OUT                         output of `index 16777215`
import re, sys

# Theorem 1: the n >= 1 with D_n^+ = 1, and b_1, ..., b_24
EXCEPTIONS = [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
              190, 191, 192]
B = [192, 1080, 2014, 2430, 3360, 5076, 5796, 11824, 13440, 13440, 15438, 17748, 26640, 26640, 32128, 32130,
     37570, 44516, 44520, 53760, 62616, 62618, 63596, 75140]
# Theorem 1: omega(D_{b_k}^+) = k - 1, except for these k, where b_k = b_{k-1} and omega(D_{b_k}^+) = k - 2
B_REPEAT = [10, 14]
# Corollary 4: k -> (|S_k|, max S_k)
TABLE = {1: (10, 60), 2: (29, 190), 3: (59, 392), 4: (88, 393), 5: (125, 904), 6: (164, 905),
         7: (211, 906), 8: (258, 907), 9: (310, 908), 10: (368, 1089), 11: (433, 2080), 12: (502, 2387),
         13: (574, 2952), 14: (646, 2953), 15: (720, 2954), 16: (795, 2955), 17: (874, 2956), 18: (957, 2957),
         19: (1048, 2958), 20: (1133, 3763), 21: (1225, 3764), 22: (1317, 3765), 23: (1408, 3766),
         24: (1503, 4775)}
# Section 7, Conjecture 14: j -> (floor(1000 min a(n)/sqrt(n)), n, a(n)) on the block [2^j, 2^(j+1))
BLOCKS = {12: (347, 4775, 24), 13: (347, 13900, 41), 14: (373, 20116, 53), 15: (441, 38830, 87),
          16: (497, 75898, 137), 17: (536, 156031, 212), 18: (589, 262699, 302), 19: (631, 533686, 461),
          20: (656, 1249093, 734), 21: (710, 3068923, 1244), 22: (743, 4392127, 1558), 23: (761, 8469236, 2217)}
# Section 7: Theorem 10 is checked for all k <= K10, Corollary 11 for n <= N11 (at the primes p with p^2 - 1 <= N11)
K10, N11, P11 = 4092, 16777215, 564


def fail(msg):
    print('CHECK FAILED:', msg, flush=True)
    sys.exit(1)


def blocks(lo, hi, step, extra):
    a = lo
    while a < hi:
        b = min((a // step + 1) * step, hi)
        print(a, b, *extra)
        a = b


def ranges(blockfile, need, outfile, witness=None):
    want = [tuple(map(int, line.split()[:2])) for line in open(blockfile)]
    if not want:
        fail('no blocks in %s' % blockfile)
    if any(want[i][1] != want[i + 1][0] for i in range(len(want) - 1)):
        fail('the blocks do not partition the range')
    got = {}
    for line in open(outfile):
        m = re.fullmatch(r's in \[(\d+),(\d+)\): omega >= (-?\d+) \(worst s=(\d+)\)', line.strip())
        if not m:
            fail('unexpected output line %r' % line)
        a, b, w, ws = map(int, m.groups())
        if (a, b) in got:
            fail('block [%d,%d) reported twice' % (a, b))
        got[(a, b)] = (w, ws)
    if set(got) != set(want):
        fail('missing or unexpected blocks: %s' % sorted(set(want) ^ set(got))[:10])
    worst = min(w for w, _ in got.values())
    if worst < need:
        bad = sorted(k for k, (w, _) in got.items() if w < need)
        fail('omega >= %d only, in blocks %s (need %d)' % (worst, bad[:10], need))
    if witness is not None:
        first = min(want)
        if got[first] != (need, witness):
            fail('first block %s: expected minimum %d first at s = %d, got %s' % (first, need, witness,
                                                                                   got[first]))
    print('%d blocks, %d <= s < %d: omega >= %d everywhere (need %d)%s: OK'
          % (len(want), want[0][0], want[-1][1], worst, need,
             '; minimum first attained at s = %d' % witness if witness is not None else ''))


def exact(outfile):
    text = open(outfile).read()
    m = re.search(r'^omega=0: count (\d+), largest (\d+) :((?: \d+)*)$', text, re.M)
    if not m:
        fail('no list of exceptions in the output')
    ex = list(map(int, m.group(3).split()))
    if ex != EXCEPTIONS or int(m.group(1)) != len(EXCEPTIONS):
        fail('exceptions %s differ from %s' % (ex, EXCEPTIONS))
    b = [int(re.search(r'^b_%d = (\d+)$' % k, text, re.M).group(1)) for k in range(1, len(B) + 1)]
    if b != B:
        fail('b_k = %s, expected %s' % (b, B))
    # omega(D_{b_k}^+): b_k is the largest n with omega(D_n^+) = j for exactly one j < k
    largest = [int(re.search(r'^omega=%d: count \d+, largest (\d+)' % j, text, re.M).group(1)) for j in range(len(B))]
    for k in range(1, len(B) + 1):
        j = largest.index(B[k - 1])
        if j != (k - 2 if k in B_REPEAT else k - 1) or B[k - 1] != max(largest[:k]):
            fail('omega(D_{b_%d}^+) = %d' % (k, j))
    print('the 26 exceptions, b_1, ..., b_24 = %s, and omega(D_{b_k}^+) = k - 1 (k - 2 for k in %s): OK'
          % (B, B_REPEAT))


def kappa(outfile):
    text = open(outfile).read()
    for k, (size, mx) in TABLE.items():
        m = re.search(r'^k=%d: largest m with kappa\(m\)<=k: \d+, max S_k = (\d+), \|S_k\| = (\d+)$' % k,
                      text, re.M)
        if not m:
            fail('no output for k = %d' % k)
        if (int(m.group(2)), int(m.group(1))) != (size, mx):
            fail('k = %d: |S_k| = %s, max = %s; expected %d, %d' % (k, m.group(2), m.group(1), size, mx))
    print('table of Corollary 4 (k <= 24): OK')


def index(outfile):
    text = open(outfile).read()
    if 'CHECK FAILED' in text:
        fail('the program index reported a failure')
    if not re.search(r'^a\(n\) for n <= %d; the first 86 values agree with OEIS A366189; recomputed without '
                     r'shortcuts for n <= 3000$' % N11, text, re.M):
        fail('index: computation of a(n)')
    if not re.search(r'^Corollary 11: a\(n\) <= ceil\(sqrt\(n\+2\)\)-1 for all n <= %d, and a\(p\^2-1\) = p for the '
                     r'%d primes p with p\^2-1 <= %d$' % (N11, P11, N11), text, re.M):
        fail('index: Corollary 11')
    if not re.search(r'^Theorem 10: the least n with a\(n\) > k is \(k\+1\)p_k - 1 for all k <= %d$' % K10, text, re.M):
        fail('index: Theorem 10')
    prev = 0
    for k, (size, mx) in TABLE.items():
        m = re.search(r'^k=%d: \|S_k\| = (\d+), max S_k = (\d+), #\{n : a\(n\) = k\} = (\d+)$' % k, text, re.M)
        if not m or tuple(map(int, m.groups())) != (size, mx, size - prev):
            fail('index: k = %d' % k)
        prev = size
    for j, (r, n, a) in BLOCKS.items():
        m = re.search(r'^block \[%d,%d\]: min a\(n\)/sqrt\(n\) = 0\.(\d{4}) at n = (\d+), a\(n\) = (\d+)$'
                      % (2 ** j, 2 ** (j + 1) - 1), text, re.M)
        if not m or (int(m.group(1)) // 10, int(m.group(2)), int(m.group(3))) != (r, n, a):
            fail('index: block %d' % j)
    print('Theorem 10 (k <= %d), Corollary 11 (n <= %d), the table of Corollary 4 from a(n), the data for Conjecture 14: OK'
          % (K10, N11))


if __name__ == '__main__':
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == 'blocks':
        blocks(int(args[0]), int(args[1]), int(args[2]), args[3:])
    elif cmd == 'ranges':
        ranges(args[0], int(args[1]), args[2], int(args[3]) if len(args) > 3 else None)
    elif cmd == 'exact':
        exact(args[0])
    elif cmd == 'kappa':
        kappa(args[0])
    elif cmd == 'index':
        index(args[0])
    else:
        fail('unknown command %s' % cmd)
