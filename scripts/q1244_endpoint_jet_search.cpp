#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using i64 = long long;
using Poly = std::array<int, 9>;

static int mod_pow(i64 a, i64 e, int p) {
    i64 r = 1; a %= p;
    while (e) { if (e & 1) r = r*a % p; a = a*a % p; e >>= 1; }
    return (int)r;
}
static std::vector<int> primes_up_to(int N) {
    std::vector<bool> a(N+1,true); a[0]=a[1]=false;
    for(int i=2;1LL*i*i<=N;++i) if(a[i]) for(int j=i*i;j<=N;j+=i) a[j]=false;
    std::vector<int> p; for(int i=2;i<=N;++i) if(a[i]) p.push_back(i); return p;
}
static Poly mul(const Poly&a,const Poly&b,int p){Poly c{};for(int i=0;i<=8;++i)for(int j=0;i+j<=8;++j)c[i+j]=(c[i+j]+1LL*a[i]*b[j])%p;return c;}
static Poly sub(const Poly&a,const Poly&b,int p){Poly c{};for(int i=0;i<=8;++i){int x=a[i]-b[i];x%=p;if(x<0)x+=p;c[i]=x;}return c;}
static Poly linpow(int n,int e,int p){Poly r{};r[0]=1;Poly y{};y[0]=n%p;y[1]=1;for(int k=0;k<e;++k)r=mul(r,y,p);return r;}
static Poly Aser(int n,int p){Poly y=linpow(n,1,p),y2=mul(y,y,p),y3=mul(y2,y,p),a{};for(int k=0;k<=8;++k){i64 v=34LL*y3[k]+51LL*y2[k]+27LL*y[k]+(k==0?5:0);a[k]=v%p;}return a;}
static Poly invcube(int c,int p){Poly r{};int u=mod_pow(c,p-2,p);i64 pw=1LL*u*u%p*u%p;for(int k=0;k<=8;++k){i64 v=(1LL*(k+1)*(k+2)/2)%p*pw%p;if(k&1)v=(p-v)%p;r[k]=v;pw=pw*u%p;}return r;}
int main(){
    const int LIMIT=100000;
    int maxm=0, doubles=0, nondouble=0, triples=0;
    for(int p:primes_up_to(LIMIT)){if(p<5)continue;Poly um1{},u{};u[0]=1;
        for(int n=0;n<=p-3;++n){Poly un=mul(sub(mul(Aser(n,p),u,p),mul(linpow(n,6,p),um1,p),p),invcube(n+1,p),p);int m=n+1,k=0;while(k<=8&&un[k]==0)++k;
            if(k>maxm){maxm=k;std::cout<<"NEW_MAX p="<<p<<" j="<<m+1<<" m="<<m<<" mult="<<k<<" coeffs=";for(int z=0;z<=8;++z)std::cout<<un[z]<<(z==8?'\n':',');}
            if(k>=2){++doubles;bool central=(2*m+1==p);if(!central){++nondouble;if(nondouble<=20)std::cout<<"NONCENTRAL_DOUBLE p="<<p<<" j="<<m+1<<" m="<<m<<" mult="<<k<<"\n";}}
            if(k>=3){++triples;std::cout<<"TRIPLE p="<<p<<" j="<<m+1<<" m="<<m<<" mult="<<k<<" coeffs=";for(int z=0;z<=8;++z)std::cout<<un[z]<<(z==8?'\n':',');if(triples>=20)return 0;}
            um1=u;u=un;
        }
    }
    std::cout<<"SUMMARY limit="<<LIMIT<<" max_mult="<<maxm<<" doubles="<<doubles<<" noncentral_doubles="<<nondouble<<" triples="<<triples<<"\n";
}
