// The integral index a(n) = min{ k >= 1 : B_n^{(k)}(x) in Z[x] }  (OEIS A366189), from Proposition 9:
//   a(n) <= k  <=>  k > n, or every prime p with s_p(m) >= p, m = n-k+1, divides m(m+1)...(m+k-1).
// A prime p <= k always divides the product, and a prime p > m/k never violates the condition (see the proof of
// Theorem 10), so only the primes in (k, m/k] are tested.  The condition is monotone in k (S_k is contained in
// S_{k+1}), so a(n) is found by bisection.  For n <= 3000 a(n) is recomputed without these two shortcuts.
//   ./index N      checks, for n <= N:
//     Theorem 10    for every k with (k+1)p_k - 1 <= N (p_k the least prime > k): the least n with a(n) > k is
//                   (k+1)p_k - 1;
//     Corollary 11  a(n) <= ceil(sqrt(n+2)) - 1, with equality for n = p^2 - 1;
//     the 86 terms of A366189 listed in the OEIS;
//   and prints, for k <= 24, |S_k|, max S_k and #{n : a(n) = k} (these equal the values for all n once N > max S_24),
//   and min a(n)/sqrt(n) over the dyadic blocks [2^j, 2^(j+1)) contained in [1, N] (Conjecture 14).
// Exits with status 1 if a check fails.  Integer arithmetic only.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using namespace std; typedef long long ll;
static vector<int> pr;
static ll isqrt(ll x){ ll lo=0, hi=3037000499LL; while(lo<hi){ ll mid=lo+(hi-lo+1)/2; if(mid<=x/mid) lo=mid; else hi=mid-1; } return lo; }
static inline ll sd(ll n, ll p){ ll t=0; while(n){ t+=n%p; n/=p; } return t; }
static int fails=0;
static void fail(const char* msg, ll a, ll b){ printf("CHECK FAILED: %s (%lld, %lld)\n", msg, a, b); fails++; if(fails>20) exit(1); }
// a(n) <= k ?
static bool ok(ll n, ll k){
  if(k>n) return true;
  ll m=n-k+1, hi=m/k;
  for(size_t i=upper_bound(pr.begin(),pr.end(),(int)k)-pr.begin(); i<pr.size() && pr[i]<=hi; i++){
    ll p=pr[i]; if((p-m%p)%p>=k && sd(m,p)>=p) return false; }
  return true; }
// the same without shortcuts: all primes p <= m, and the product m(m+1)...(m+k-1) tested directly
static bool okSlow(ll n, ll k){
  if(k>n) return true;
  ll m=n-k+1;
  for(size_t i=0;i<pr.size() && pr[i]<=m;i++){ ll p=pr[i]; if(sd(m,p)<p) continue;
    bool div=false; for(ll j=0;j<k;j++) if((m+j)%p==0){ div=true; break; }
    if(!div) return false; }
  return true; }
static const int OEIS[86]={1,1,2,1,2,1,2,3,2,1,2,1,2,3,2,2,3,3,4,3,2,3,4,5,2,3,4,1,2,1,2,3,4,5,3,1,2,3,4,5,6,3,4,5,4,
  5,6,7,5,3,4,3,4,5,2,3,2,3,4,1,2,3,4,5,6,3,4,4,5,2,3,3,4,5,6,7,6,3,4,3,4,5,6,5,6,7};
int main(int argc,char**argv){
  if(argc!=2){ fprintf(stderr,"usage: index N\n"); return 2; }
  ll N=atoll(argv[1]); ll P=N+2*isqrt(N)+100;
  { vector<char> c(P+1,0); for(ll i=2;i<=P;i++) if(!c[i]){ pr.push_back((int)i); for(ll j=i*i;j<=P;j+=i) c[j]=1; } }
  vector<int> a(N+1,0);
  for(ll n=1;n<=N;n++){
    ll r=isqrt(n+2), ub=(r*r==n+2)? r-1 : r;                  // ceil(sqrt(n+2)) - 1
    if(!ok(n,ub)) fail("Corollary 11: a(n) > ceil(sqrt(n+2))-1", n, ub);
    ll lo=1, hi=ub; while(lo<hi){ ll mid=(lo+hi)/2; if(ok(n,mid)) hi=mid; else lo=mid+1; }
    a[n]=(int)lo;
    if(n<=3000){ ll k=1; while(!okSlow(n,k)) k++; if(k!=lo) fail("slow and fast computation differ", n, k); }
  }
  for(int i=0;i<86 && i<N;i++) if(a[i+1]!=OEIS[i]) fail("differs from the OEIS terms", i+1, a[i+1]);
  printf("a(n) for n <= %lld; the first 86 values agree with OEIS A366189; recomputed without shortcuts for n <= 3000\n", N);
  // Corollary 11, equality
  ll neq=0;
  for(int p: pr){ ll n=(ll)p*p-1; if(n>N) break; if(a[n]!=p) fail("a(p^2-1) != p", p, a[n]); neq++; }
  printf("Corollary 11: a(n) <= ceil(sqrt(n+2))-1 for all n <= %lld, and a(p^2-1) = p for the %lld primes p with p^2-1 <= %lld\n", N, neq, N);
  // Theorem 10: first n with a(n) > k
  vector<ll> first; ll run=0;                                 // first[k] = least n with a(n) > k
  for(ll n=1;n<=N;n++) while(a[n]>run){ first.push_back(n); run++; }   // first[run] for run = 0, 1, ...
  ll K=0;
  for(ll k=1;;k++){
    ll p=*upper_bound(pr.begin(),pr.end(),(int)k); ll want=(k+1)*p-1;
    if(want>N) break;
    if(k>=(ll)first.size()) { fail("no n <= N with a(n) > k", k, want); break; }
    if(first[k]!=want) fail("Theorem 10: least n with a(n) > k", k, first[k]);
    K=k; }
  printf("Theorem 10: the least n with a(n) > k is (k+1)p_k - 1 for all k <= %lld\n", K);
  // tables for k <= 24
  for(int k=1;k<=24;k++){ ll cnt=0, mx=0, eq=0; for(ll n=1;n<=N;n++){ if(a[n]<=k){ cnt++; mx=n; } if(a[n]==k) eq++; }
    printf("k=%d: |S_k| = %lld, max S_k = %lld, #{n : a(n) = k} = %lld\n", k, cnt, mx, eq); }
  // min a(n)/sqrt(n) on dyadic blocks: compare a^2/n exactly; print floor(10^4 a/sqrt(n))
  for(ll lo=1; 2*lo-1<=N; lo*=2){ ll hi=2*lo-1, bn=lo;
    for(ll n=lo;n<=hi;n++) if((ll)a[n]*a[n]*bn < (ll)a[bn]*a[bn]*n) bn=n;
    ll r4=isqrt(100000000LL*a[bn]*a[bn]/bn);  // floor(10^4 a/sqrt(n)), as floor(sqrt(floor(x))) = floor(sqrt(x))
    printf("block [%lld,%lld]: min a(n)/sqrt(n) = %lld.%04lld at n = %lld, a(n) = %d\n", lo, hi, r4/10000, r4%10000, bn, a[bn]); }
  if(fails){ printf("CHECK FAILED: %d failures\n", fails); return 1; }
  return 0; }
