# Theorem 12 (explicit lower bound):  omega(D_n^+) > sqrt(n) / (4 log^2 n)  for all n > 192.
# Integer and rational arithmetic only.
#
#   n <= 1080:            the right side is < 1 <= omega(D_n^+) (Theorem 1, b_1 = 192).
#   1080 < n < 1500^2:    the right side is < 2 <= omega(D_n^+) (Theorem 1, b_2 = 1080).
#   1500 <= s < S1:       s = floor(sqrt n); the right side is < (s+1)/(16 log^2 s), and omega(D_n^+) >= M(s) with
#                         M(s) = max(24, L(s)), where 24 is (4.1) and
#                         L(s) = max_U  pi(s+U) - pi(s) - (number of bad m allowed by Lemma 8)    (2.3)
#                         We check 16 M(s) l(s)^2 >= s + 1 with a rational lower bound l(s) <= log s.
#   s >= S1 = 678407:     (3.2), from (3.1) of Rosser and Schoenfeld; its constants are checked at the end.
#
#   python3 omega_bound.py [S1]
import math, sys
from fractions import Fraction as F

S1 = int(sys.argv[1]) if len(sys.argv) > 1 else 678407
UMAX = 40000


def fail(msg):
    print('CHECK FAILED:', msg)
    sys.exit(1)


# --- rigorous lower bounds for log s:  T[j] >= e^(j/R), so  s >= T[j]  implies  log s >= j/R ---------------------
R = 256
x = F(1, R)
c = sum(x ** i / math.factorial(i) for i in range(13)) + 2 * x ** 13 / math.factorial(13)   # c >= e^(1/R)
SH = 1 << 80
E, T = SH, [1]                      # E >= 2^80 e^(j/R), rounded up at every step
while T[-1] <= max(2 * S1, 1500 ** 2):
    E = -((-E * c.numerator) // c.denominator)
    T.append(-((-E) // SH))


def loglow(s):
    """largest j with T[j] <= s; then log s >= j / R"""
    lo, hi = 0, len(T) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if T[mid] <= s: lo = mid
        else: hi = mid - 1
    return lo


# sanity check of the table against floating point (not used in the proof)
for s in (1500, 10 ** 4, 10 ** 5, S1):
    assert 0 <= math.log(s) - loglow(s) / R < 2.0 / R, s

# --- prime counts -------------------------------------------------------------------------------------------------
N = S1 + UMAX + 10
sv = bytearray([1]) * (N + 1); sv[0:2] = b'\0\0'
for i in range(2, math.isqrt(N) + 1):
    if sv[i]: sv[i * i::i] = bytearray(len(sv[i * i::i]))
pi = [0] * (N + 1)
c_ = 0
for i in range(N + 1):
    c_ += sv[i]; pi[i] = c_

# --- 1500 <= s < S1 ------------------------------------------------------------------------------------------------
worst = None
used_L = 0
for s in range(1500, S1):
    j = loglow(s)                                  # log s >= j/R
    base = (s * R) // (4 * j)                      # about s / (4 log s)
    L = -1
    for f in (6, 7, 8, 9, 10, 11, 12, 13, 14):     # U = base * f / 10
        U = max(1, base * f // 10)
        if U > UMAX: fail('UMAX too small')
        E_ = s + U
        bad = (4 * E_ + 2 * U * U - 1) // E_      # largest integer < 4 + 2U^2/(s+U)
        L = max(L, pi[s + U] - pi[s] - bad)
    M = max(24, L)
    if L > 24: used_L += 1
    # need M >= (s+1)/(16 log^2 s); suffices 16 M j^2 >= (s+1) R^2
    lhs, rhs = 16 * M * j * j, (s + 1) * R * R
    if lhs < rhs:
        fail('s = %d: M = %d (L = %d) below (s+1)/(16 log^2 s)' % (s, M, L))
    r = F(lhs, rhs)
    if worst is None or r < worst[0]:
        worst = (r, s, M, L)
print('1500 <= s < %d: omega(D_n^+) >= max(24, L(s)) > (s+1)/(16 log^2 s) > sqrt(n)/(4 log^2 n); '
      'smallest ratio %.4f at s = %d (bound %d); L(s) > 24 for %d values of s: OK'
      % (S1, float(worst[0]), worst[1], worst[2], used_L))

# --- n < 1500^2 -----------------------------------------------------------------------------------------------------
# sqrt(n)/log^2 n is increasing for n > e^4; at n = 1080 the bound is < 1, at n = 1500^2 it is < 2.
def rhs_lt(n, k):
    """sqrt(n)/(4 log^2 n) < k, checked as  sqrt(n) < 4 k (j/R)^2  with log n >= j/R"""
    j = loglow(n)
    return (math.isqrt(n) + 1) * R * R <= 4 * k * j * j
if not (rhs_lt(1080, 1) and rhs_lt(1500 ** 2, 2)):
    fail('small n')
print('192 < n <= 1080: bound < 1;  1080 < n < 1500^2: bound < 2  (Theorem 1 gives omega >= 1, 2): OK')

# --- s >= S1: the analytic argument of Section 3 ------------------------------------------------------------------
# The constants of Section 3, (3.2), checked with exact rational arithmetic.  l = log s >= l0 >= 13.42, U = floor(s/(4l)):
#   U <= s/53.68,  log(s+U) <= l + 1/(4l) <= 1.0014 l,
#   theta(s+U) - theta(s) > U - (2s+U)/(40 l) >= s/(4l) - 1 - 0.05047 s/l = 0.19953 s/l - 1      by (3.1) at s and s+U,
#   pi(s+U) - pi(s) > (0.19953 s/l - 1)/(1.0014 l) >= 0.19925 s/l^2 - 1/l,
#   bad < 4 + 2U^2/(s+U) <= 4 + s/(8 l^2)  (Lemma 8),  so by (2.3)
#   omega(D_n^+) > 0.0742 s/l^2 - 4.08 >= 275,   and  > (s+1)/(16 l^2)  (Theorem 12).
D = lambda x: F(x)                                     # decimal constants as exact fractions
j0 = loglow(S1)
l0 = F(j0, R)                                          # log S1 >= l0
# s / log^2 s is increasing (s > e^2), so for s >= S1 it is >= S1 / lup^2 for any lup > log S1.  A partial sum of the
# series of e^x is a lower bound for e^x, so  lo_e > S1  gives  log S1 < lup.
lup = F(j0 + 2, R)
lo_e = sum(lup ** i / math.factorial(i) for i in range(60))
val = F(S1) / (lup * lup)                              # s / log^2 s >= val  for s >= S1
checks = [
    ('log 678407 >= 13.42', l0 >= D('13.42')),
    ('upper bound for log 678407', lo_e > S1),
    ('4 * 13.42 = 53.68', 4 * D('13.42') == D('53.68')),
    ('1 + 1/(4 * 13.42^2) <= 1.0014', 1 + 1 / (4 * D('13.42') ** 2) <= D('1.0014')),
    ('(2 + 1/53.68)/40 <= 0.05047', (2 + 1 / D('53.68')) / 40 <= D('0.05047')),
    ('1/4 - 0.05047 = 0.19953', F(1, 4) - D('0.05047') == D('0.19953')),
    ('0.19953/1.0014 >= 0.19925', D('0.19953') / D('1.0014') >= D('0.19925')),
    ('0.19925 - 1/8 >= 0.0742', D('0.19925') - F(1, 8) >= D('0.0742')),
    ('4 + 1/13.42 <= 4.08', 4 + 1 / D('13.42') <= D('4.08')),
    ('s/log^2 s >= 3759 for s >= 678407', val >= 3759),
    ('0.0742 * 3759 - 4.08 > 274', D('0.0742') * 3759 - D('4.08') > 274),
    ('(0.0742 - 1/16) * 3759 >= 4.08 + 1/(16 * 13.42^2)',
     (D('0.0742') - F(1, 16)) * 3759 >= D('4.08') + 1 / (16 * D('13.42') ** 2)),
]
for name, okay in checks:
    if not okay:
        fail('Section 3: ' + name)
print('s >= %d: the constants of Section 3 and (3.2) (omega(D_n^+) > 0.0742 s/log^2 s - 4.08 >= 275, s/log^2 s >= %.1f) '
      'and (s+1)/(16 log^2 s) < 0.0742 s/log^2 s - 4.08: OK' % (S1, float(val)))
print('Theorem 12: omega(D_n^+) > sqrt(n)/(4 log^2 n) for all n > 192: OK')
