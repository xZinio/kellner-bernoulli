# Second program, written separately from finite.cpp, in pure Python (integer arithmetic only).
#   python3 verify2.py exact N      b_1..b_8 from the definition (digit sums computed digit by digit), n < N;
#                                   exits with status 1 unless they are the values of Theorem 1
#   python3 verify2.py range S0 S1  for S0 <= s < S1: the first 40 primes p>s, bad r in [0,2s] (n=s^2+r) from
#                                   c*p <= u^2+r <= c*p+2u-c-1, u=p-s, c>=0
import sys, bisect, math
def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\0\0'
    for i in range(2, math.isqrt(n) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
def sd(n, p):
    t = 0
    while n: t += n % p; n //= p
    return t
if sys.argv[1] == 'exact':
    N = int(sys.argv[2]); PR = primes(N); last = [0] * 9
    for n in range(1, N):
        w = 0
        for i in range(bisect.bisect_right(PR, math.isqrt(n)), len(PR)):
            p = PR[i]
            if p > n or w >= 8: break
            w += sd(n, p) >= p
        for k in range(w + 1, 9): last[k] = n
    print('largest n < %d with omega(D_n^+) < k, k=1..8:' % N, last[1:])
    if N > 11825 and last[1:] != [192, 1080, 2014, 2430, 3360, 5076, 5796, 11824]:
        print('CHECK FAILED: b_k differ from Theorem 1'); sys.exit(1)
else:
    S0, S1, m = int(sys.argv[2]), int(sys.argv[3]), 40
    PR = primes(S1 + 20000); idx = bisect.bisect_right(PR, S0); worst = (10 ** 9, 0)
    for s in range(S0, S1):
        while PR[idx] <= s: idx += 1
        ev = []
        ps = PR[idx:idx + m]
        if len(ps) != m: print('not enough primes'); sys.exit(1)
        for p in ps:
            u = p - s; c = 0
            while c * p - u * u <= 2 * s:
                lo, hi = c * p - u * u, c * p - u * u + 2 * u - c - 1
                if hi >= max(lo, 0): ev.append((max(lo, 0), 1)); ev.append((min(hi, 2 * s) + 1, -1))
                c += 1
        ev.sort(); cov = mx = 0            # at equal coordinates, removals (-1) come before insertions
        for _, d in ev:
            cov += d
            if cov > mx: mx = cov
        if m - mx < worst[0]: worst = (m - mx, s)
    print('s in [%d,%d): omega >= %d (worst s=%d)' % (S0, S1, worst[0], worst[1]), flush=True)
