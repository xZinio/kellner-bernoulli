// Integer arithmetic only (no floating point).   omega(D_n^+) = #{ primes p > sqrt n : s_p(n) >= p }.
//   ./finite exact S0 K        for n < S0^2: all n with omega(D_n^+) < K, from the definition (K <= 8 in the paper)
//   ./finite range S0 S1 m     for S0 <= s < S1: for the first m primes p > s, the n in [s^2, s^2+2s] for which p is bad
//                              (s_p(n) < p) form the intervals [qp, qp+p-1-q]; prints min over n of  m - #bad
//                              and the first s where the minimum is attained.  Sweep: each interval [l, h] gives
//                              the events (l, +1) and (h+1, -1); events are sorted by coordinate, and at equal
//                              coordinates removals (-1) come first, so the running sum is the number of
//                              intervals containing the current coordinate.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <algorithm>
using namespace std; typedef long long ll;
static ll isqrt(ll x){ ll lo=0, hi=3037000499LL; while(lo<hi){ ll mid=lo+(hi-lo+1)/2; if(mid<=x/mid) lo=mid; else hi=mid-1; } return lo; }  // floor(sqrt(x)), x >= 0
static int exact(ll S0, int K){
  ll LIM=S0*S0+10; vector<bool> comp(LIM+1,false); vector<int> pr;
  for(ll i=2;i<=LIM;i++) if(!comp[i]){ pr.push_back((int)i); for(ll j=i*i;j<=LIM;j+=i) comp[j]=true; }
  vector<vector<ll>> few(K); ll s=1; size_t idx=0;
  for(ll n=1;n<S0*S0;n++){
    while((s+1)*(s+1)<=n) s++;
    while(idx<pr.size()&&pr[idx]<=s) idx++;                 // primes > sqrt n are those >= s+1
    int cnt=0; for(size_t i=idx;i<pr.size()&&pr[i]<=n&&cnt<K;i++){ ll p=pr[i]; if(n/p+n%p>=p) cnt++; }
    if(cnt<K) few[cnt].push_back(n); }
  for(int k=0;k<K;k++){ printf("omega=%d: count %zu, largest %lld%s",k,few[k].size(),few[k].empty()?0:few[k].back(),k==0?" :":""); if(k==0) for(ll n:few[k]) printf(" %lld",n); puts(""); }
  ll mx=0; for(int k=0;k<K;k++){ if(!few[k].empty()) mx=max(mx,few[k].back()); printf("b_%d = %lld\n",k+1,mx); }
  return 0; }
static int range(ll S0, ll S1, int m){
  ll HI=S1+200000, sq=isqrt(HI)+1; vector<char> c(sq+1,0); vector<ll> base;
  for(ll i=2;i<=sq;i++) if(!c[i]){ base.push_back(i); for(ll j=i*i;j<=sq;j+=i) c[j]=1; }
  const ll SEG=1<<20; int worst=1<<30; ll ws=0; vector<char> sv; vector<ll> pr; vector<pair<ll,int>> ev;
  for(ll a=S0;a<S1;a+=SEG){ ll b=min(a+SEG,S1), lo=a+1, hi=b+200000;
    sv.assign(hi-lo+1,1); for(ll p:base){ if(p*p>hi) break; for(ll j=max(p*p,(lo+p-1)/p*p);j<=hi;j+=p) sv[j-lo]=0; }
    if(lo<=1) sv[1-lo]=0;
    pr.clear(); for(ll j=lo;j<=hi;j++) if(sv[j-lo]) pr.push_back(j);
    size_t idx=0;
    for(ll s=a;s<b;s++){ while(pr[idx]<=s) idx++; if(idx+m>pr.size()){ puts("not enough primes"); return 1; } ev.clear();
      ll A=s*s, B=s*s+2*s;
      for(int i=0;i<m;i++){ ll p=pr[idx+i]; for(ll q=A/p;q*p<=B;q++){ ll l=max(A,q*p), h=min(B,q*p+p-1-q); if(l<=h){ ev.push_back({l,1}); ev.push_back({h+1,-1}); } } }
      sort(ev.begin(),ev.end()); int cov=0,mx=0; for(auto&e:ev){ cov+=e.second; if(cov>mx) mx=cov; }
      if(m-mx<worst){ worst=m-mx; ws=s; } } }
  printf("s in [%lld,%lld): omega >= %d (worst s=%lld)\n",S0,S1,worst,ws); return 0; }
int main(int argc,char**argv){
  if(argc==4&&!strcmp(argv[1],"exact")) return exact(atoll(argv[2]),atoi(argv[3]));
  if(argc==5&&!strcmp(argv[1],"range")) return range(atoll(argv[2]),atoll(argv[3]),atoi(argv[4]));
  fprintf(stderr,"usage: finite exact S0 K | finite range S0 S1 m\n"); return 2; }
