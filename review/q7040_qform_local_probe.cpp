#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <utility>
#include <vector>

struct R { int a,b; };
static inline R mul(R x,R y,int m){
  long long A=(long long)x.a*y.a+(long long)x.b*y.b;
  long long B=(long long)x.a*y.b+(long long)x.b*y.a+(long long)x.b*y.b;
  A%=m; B%=m; if(A<0)A+=m; if(B<0)B+=m; return {(int)A,(int)B};
}
static inline R p5(R x,int m){R x2=mul(x,x,m),x4=mul(x2,x2,m);return mul(x4,x,m);}
static inline int mod(long long x,int m){x%=m;return x<0?x+m:x;}
int main(){
  std::vector<int> mods={25,35,45,55,65,75,85,95,105,125,155,205,305,625};
  std::cout<<"Q7040 Q-FORM LOCAL PROBE\n";
  for(int m:mods){
    std::vector<unsigned char> fifth((size_t)m*m,0);
    for(int x=0;x<m;++x)for(int y=0;y<m;++y){auto z=p5({x,y},m);fifth[(size_t)z.a*m+z.b]=1;}
    long long cnt=0; int wa=-1,wb=-1;
    for(int a=0;a<m;++a)for(int b=0;b<m;b+=5){
      if(std::gcd(std::gcd(a,b),m)!=1)continue;
      int A=mod((long long)a*a+3LL*a*b+5LL*b*b,m);
      int B=mod(-(long long)a*b,m);
      if(fifth[(size_t)A*m+B]){++cnt;if(wa<0){wa=a;wb=b;}}
    }
    std::cout<<"m="<<m<<" primitive_residue_solutions="<<cnt;
    if(cnt)std::cout<<" witness_ab=("<<wa<<","<<wb<<")";
    std::cout<<"\n";
  }
}
