# Helpers for run_all.sh: splits ranges into blocks, and checks the output of the programs against the
# values stated in the paper.  Every check prints what it verified; on any mismatch it prints
# "CHECK FAILED: ..." and exits with status 1.
#   python3 check.py blocks LO HI STEP [EXTRA ...]    print "a b EXTRA..." for blocks partitioning [LO, HI)
#   python3 check.py ranges BLOCKS NEED OUT [WITNESS]  output of `finite range` / `verify2.py range`
#   python3 check.py exact OUT                         output of `finite exact 1500 8`
#   python3 check.py kappa OUT                         output of `kappa 2250000 24`
import re, sys

# Theorem 1: the n >= 1 with D_n^+ = 1, and b_1, ..., b_8
EXCEPTIONS = [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
              190, 191, 192]
B = [192, 1080, 2014, 2430, 3360, 5076, 5796, 11824]
# Corollary 4: k -> (|S_k|, max S_k)
TABLE = {1: (10, 60), 2: (29, 190), 3: (59, 392), 4: (88, 393), 5: (125, 904), 6: (164, 905),
         7: (211, 906), 8: (258, 907), 9: (310, 908), 10: (368, 1089), 11: (433, 2080), 12: (502, 2387)}


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
    b = [int(re.search(r'^b_%d = (\d+)$' % k, text, re.M).group(1)) for k in range(1, 9)]
    if b != B:
        fail('b_k = %s, expected %s' % (b, B))
    print('the 26 exceptions and b_1, ..., b_8 = %s: OK' % B)


def kappa(outfile):
    text = open(outfile).read()
    for k, (size, mx) in TABLE.items():
        m = re.search(r'^k=%d: largest m with kappa\(m\)<=k: \d+, max S_k = (\d+), \|S_k\| = (\d+)$' % k,
                      text, re.M)
        if not m:
            fail('no output for k = %d' % k)
        if (int(m.group(2)), int(m.group(1))) != (size, mx):
            fail('k = %d: |S_k| = %s, max = %s; expected %d, %d' % (k, m.group(2), m.group(1), size, mx))
    print('table of Corollary 4 (k <= 12): OK')


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
    else:
        fail('unknown command %s' % cmd)
