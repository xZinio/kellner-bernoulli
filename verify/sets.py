# The finite sets in the corollaries, from the criterion (Proposition 9) and the bounds b_k of Theorem 1.
import math
def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\0\0'
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
PR = primes(12000)
def sd(n, p):
    t = 0
    while n: t += n % p; n //= p
    return t
def DP(n): return [p for p in PR if p <= n and sd(n, p) >= p]
B = {1: 192, 2: 1080, 3: 2014, 4: 2430, 5: 3360, 6: 5076}
D = {m: DP(m) for m in range(1, B[6] + 1)}
def S(k):
    return list(range(1, k)) + [m + k - 1 for m in range(1, B[k] + 1) if all(math.perm(m + k - 1, k) % p == 0 for p in D[m])]
def unr(t):
    o = []
    for x in t.replace(' ', '').split(','):
        if '-' in x: a, b = map(int, x.split('-')); o += range(a, b + 1)
        else: o.append(int(x))
    return o
K = {1: [1,2,4,6,10,12,28,30,36,60],
     2: unr('1-7,9-13,15,16,21,25,28-31,36,37,55,57,60,61,70,121,190'),
     3: unr('1-18,20-22,25,26,28-32,35-38,42,50,52,55-58,60-62,66,70-72,78,80,92,110,121,122,156,176,177,190,191,210,392')}
for k in range(1, 7):
    s = S(k); print('k=%d: %d elements, max %d%s' % (k, len(s), max(s), '; equals the conjectured set: %s' % (s == K[k]) if k in K else ''))
print('Corollary 3:', [n for n in range(1, B[2] + 1) if set(D[n]) == {p for p in PR if (n + 1) % p == 0}])
print('Corollary 5, exceptions 193..1080:', [n for n in range(193, 1081) if not (max(D[n]) ** 2 > n and (n + 1) ** 2 < n * max(D[n]) ** 2)])
print('Corollary 6, largest exception <= 192:', max(k for k in range(1, 193) if not any(k % p + (k // p) % p >= p for p in PR if 3 <= p <= k)))
