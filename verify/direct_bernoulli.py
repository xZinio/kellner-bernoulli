# Direct check from exact Bernoulli numbers; does not use the digit-sum criterion.
#   (a) B_n^{(k)}(x) in Z[x]           for k = 1..6 and all n <= N
#   (b) denom(B_n(x) - B_n) = rad(n+1) for all n <= N
# The results are compared with the sets computed from the criterion (sets.py).
import math, sys
from fractions import Fraction
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1100

# Bernoulli numbers from tangent numbers (Brent--Harvey, Algorithm TangentNumbers; integers only)
h = N // 2 + 1
T = [0] * (h + 1)
T[1] = 1
for k in range(2, h + 1): T[k] = (k - 1) * T[k - 1]
for k in range(2, h + 1):
    for j in range(k, h + 1):
        T[j] = (j - k) * T[j - 1] + (j - k + 2) * T[j]
B = [Fraction(0)] * (N + 2)
B[0] = Fraction(1); B[1] = Fraction(-1, 2)
for n in range(1, h + 1):
    if 2 * n <= N:
        B[2 * n] = Fraction((-1) ** (n - 1) * 2 * n * T[n], 4 ** n * (4 ** n - 1))
# independent check of the Bernoulli numbers: recurrence for small n, von Staudt--Clausen for all n
for n in range(1, 60):
    assert sum(Fraction(math.comb(n + 1, j)) * B[j] for j in range(n + 1)) == 0
def is_prime(m): return m > 1 and all(m % q for q in range(2, math.isqrt(m) + 1))
for n in range(2, N + 1, 2):
    d = 1
    for p in range(2, n + 2):
        if n % (p - 1) == 0 and is_prime(p): d *= p
    assert B[n].denominator == d, n
    assert (B[n] + sum(Fraction(1, p) for p in range(2, n + 2) if n % (p - 1) == 0 and is_prime(p))).denominator == 1
den = [b.denominator for b in B]          # Fraction keeps lowest terms
js = [0, 1] + list(range(2, N + 1, 2))    # indices with B_j != 0

def integral(n, k):
    # coefficient of x^{n-k-j} in B_n^{(k)} = (n)_k B_{n-k} is (n)_k C(n-k, j) B_j
    if n < k: return True
    m = n - k
    ff = math.perm(n, k)
    for j in js:
        if j > m: break
        if (ff % den[j]) and (ff * math.comb(m, j)) % den[j]: return False
    return True
def denom_minus_const(n):
    d = 1
    for j in js:
        if j > n - 1: break
        g = den[j] // math.gcd(den[j], math.comb(n, j)); d = d * g // math.gcd(d, g)
    return d
def rad(m):
    r = 1; p = 2
    while p * p <= m:
        if m % p == 0:
            r *= p
            while m % p == 0: m //= p
        p += 1
    return r * (m if m > 1 else 1)

def sd(n, p):
    t = 0
    while n: t += n % p; n //= p
    return t
PR = [p for p in range(2, N + 2) if is_prime(p)]
def crit(n, k):
    if n < k: return True
    m = n - k + 1; ff = math.perm(n, k)
    return all(ff % p == 0 for p in PR if p <= m and sd(m, p) >= p)

for k in range(1, 7):
    d = [n for n in range(1, N + 1) if integral(n, k)]
    c = [n for n in range(1, N + 1) if crit(n, k)]
    print('k=%d: direct set has %d elements, max %d; equals set from criterion: %s' % (k, len(d), max(d), d == c), flush=True)
NR = min(N, 1100)
R = [n for n in range(1, NR + 1) if denom_minus_const(n) == rad(n + 1)]
print('denom(B_n(x)-B_n) = rad(n+1), n <= %d:' % NR, R)
