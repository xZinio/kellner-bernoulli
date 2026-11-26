# New, simpler form of the counting lemma.  n>=1, s=isqrt(n); for m>s put q(m)=n//m.
#  (A) s_m(n) = n-(m-1)q(m);  m good (s_m(n)>=m)  <=>  (n-1)//(m-1) > q(m)
#  (B) for m>=s+2:  q(m-1)-q(m) in {0,1};  m good <=> q(m-1)-q(m)=1 and (m-1) does not divide n
#  (C) #{m in [s+2,s+U]: q(m-1)=q(m)} = (U-1)-(q(s+1)-q(s+U)) <  2 + U^2/(s+U)
#  (D) #{d | n : s+1<=d<=s+U-1} <= 1 + U^2/(s+U)
#  (E) total bad in [s+1,s+U] <  4 + 2U^2/(s+U)
import math, random
def digsum(n,b):
    t=0
    while n: t+=n%b; n//=b
    return t
def check(n,U,full):
    s=math.isqrt(n); bad=0; cC=0; cD=0
    for u in range(1,U+1):
        m=s+u; q=n//m
        good = (digsum(n,m)>=m) if full else (q+n%m>=m)
        assert q<m and (q+n%m)==n-(m-1)*q
        if m>1: assert good==((n-1)//(m-1)>q)
        if u>=2:
            d=n//(m-1)-q
            assert d in (0,1)
            assert good==(d==1 and n%(m-1)!=0)
            cC+= (d==0); cD+= (n%(m-1)==0)
            assert cC==(u-1)-(n//(s+1)-q)
        bad+=not good
        assert cC*(s+u) < 2*(s+u)+u*u
        assert cD*(s+u) <= (s+u)+u*u
        assert bad*(s+u) < 4*(s+u)+2*u*u
    return bad
mx=0
for n in range(1,30000): check(n,4*math.isqrt(n)+6,n<3000)
random.seed(7)
for _ in range(400): check(random.randrange(10**6,10**13),min(30000,math.isqrt(random.randrange(10**6,10**9))),False)
# highly composite n (many divisors near sqrt)
for n in [720720,1441440,4324320,21621600,367567200,6983776800,13967553600,321253732800,2248776129600]: check(n,60000,False)
for k in range(2,3000): check(k*k-1,200,False); check(k*k,200,False); check(k*(k+1),200,False)
print('lemma (A)-(E) verified')
