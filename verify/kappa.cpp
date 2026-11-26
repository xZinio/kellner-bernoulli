// For m>=1:  kappa(m) = 1 + max over primes p with s_p(m)>=p of ((-m) mod p)   (kappa=1 if there is no such p with p not dividing m).
// Then  S_k = {1,...,k-1} u { m+k-1 : kappa(m) <= k }.
// Largest m with kappa(m)<=k for k=1..K, and |S_k|, for m < M.  Integer arithmetic only.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using namespace std; typedef long long ll;
static inline ll sd(ll n,ll p){ll t=0;while(n){t+=n%p;n/=p;}return t;}
int main(int argc,char**argv){ ll M=atoll(argv[1]); int K=atoi(argv[2]); vector<char> c(M+1,0); vector<int> pr; for(ll i=2;i<=M;i++) if(!c[i]){pr.push_back(i); for(ll j=i*i;j<=M;j+=i)c[j]=1;}
  vector<ll> last(K+1,0), cnt(K+1,0);
  ll s=0;
  for(ll m=1;m<M;m++){ ll mx=0;
    // go through primes; stop as soon as mx+1>K
    while((s+1)*(s+1)<=m) s++;                                   // s = floor(sqrt m)
    size_t i0=upper_bound(pr.begin(),pr.end(),(int)s)-pr.begin();
    for(size_t i=i0;i<pr.size()&&2*(ll)pr[i]<=m+1&&mx+1<=K;i++){ ll p=pr[i]; if(m/p+m%p>=p){ ll j=(p-m%p)%p; if(j>mx) mx=j; } }
    if(mx+1<=K) for(size_t i=0;i<i0&&mx+1<=K;i++){ ll p=pr[i]; if(sd(m,p)>=p){ ll j=(p-m%p)%p; if(j>mx) mx=j; } }
    ll k=mx+1; if(k<=K) for(int t=k;t<=K;t++){ last[t]=m; cnt[t]++; } }
  for(int k=1;k<=K;k++) printf("k=%d: largest m with kappa(m)<=k: %lld, max S_k = %lld, |S_k| = %lld\n",k,last[k],last[k]+k-1,cnt[k]+k-1);
}
