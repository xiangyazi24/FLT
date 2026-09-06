#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <tuple>
#include <vector>

struct R5 { long long a, b; }; // a + b*phi, phi^2=phi+1

static inline R5 mul(R5 x, R5 y) {
  __int128 A=(__int128)x.a*y.a + (__int128)x.b*y.b;
  __int128 B=(__int128)x.a*y.b + (__int128)x.b*y.a + (__int128)x.b*y.b;
  return {(long long)A,(long long)B};
}
static inline R5 pow5(R5 x) {
  R5 x2=mul(x,x), x4=mul(x2,x2); return mul(x4,x);
}
static inline long long qA(long long a,long long b) { return a*a+3*a*b+5*b*b; }
static inline long long qB(long long a,long long b) { return -a*b; }

struct Best {
  long double rel=std::numeric_limits<long double>::infinity();
  long double rootRel=std::numeric_limits<long double>::infinity();
  long long a=0,b=0,x=0,y=0,A=0,B=0,P=0,Q=0;
};

int main(int argc,char**argv) {
  int H=10000; if(argc>1) H=std::atoi(argv[1]);
  const long double sq5=sqrtl(5.0L);
  const long double phi=(1.0L+sq5)/2.0L;
  const long double phip=(1.0L-sq5)/2.0L;
  std::vector<int> cuts={100,250,500,1000,2000,5000,10000};
  cuts.erase(std::remove_if(cuts.begin(),cuts.end(),[&](int x){return x>H;}),cuts.end());
  if(cuts.empty() || cuts.back()!=H) cuts.push_back(H);
  std::vector<Best> best(cuts.size());
  unsigned long long scanned=0, exact=0;
  std::vector<std::tuple<long long,long long,long long,long long>> exacts;

  for(long long b=5;b<=H;b+=5) {
    for(long long a=-H;a<=H;++a) {
      if(std::gcd(std::llabs(a),b)!=1) continue;
      ++scanned;
      long long A=qA(a,b), B=qB(a,b);
      long double q1=(long double)A+(long double)B*phi;
      long double q2=(long double)A+(long double)B*phip;
      if(!(q1>0 && q2>0)) { std::cerr<<"positivity failure\n"; return 2; }
      long double r1=powl(q1,0.2L), r2=powl(q2,0.2L);
      long double y0=(r1-r2)/sq5;
      long double x0=(phi*r2-phip*r1)/sq5;
      long long xc=llroundl(x0), yc=llroundl(y0);
      Best here;
      bool isExact=false;
      for(long long dx=-2;dx<=2;++dx) for(long long dy=-2;dy<=2;++dy) {
        long long x=xc+dx,y=yc+dy;
        R5 p=pow5({x,y});
        long double p1=(long double)p.a+(long double)p.b*phi;
        long double p2=(long double)p.a+(long double)p.b*phip;
        long double rel=std::max(fabsl(p1-q1)/q1,fabsl(p2-q2)/q2);
        long double gr1=(long double)x+(long double)y*phi;
        long double gr2=(long double)x+(long double)y*phip;
        long double rootRel=std::max(fabsl(gr1-r1)/r1,fabsl(gr2-r2)/r2);
        if(rel<here.rel) here={rel,rootRel,a,b,x,y,A,B,p.a,p.b};
        if(p.a==A && p.b==B) {
          isExact=true;
          if(exacts.size()<50) exacts.emplace_back(a,b,x,y);
        }
      }
      if(isExact) ++exact;
      int m=(int)std::max(std::llabs(a),b);
      for(size_t j=0;j<cuts.size();++j) if(m<=cuts[j] && here.rel<best[j].rel) best[j]=here;
    }
  }
  std::cout<<std::setprecision(18);
  std::cout<<"Q7040 Q-FORM PROBE\n";
  std::cout<<"ring=Z[phi], phi^2=phi+1\n";
  std::cout<<"q(a,b)=(a^2+3ab+5b^2) + (-ab)*phi\n";
  std::cout<<"domain: 0<b<=H, 5|b, |a|<=H, gcd(a,b)=1 (projective sign normalized by b>0)\n";
  std::cout<<"H="<<H<<" scanned="<<scanned<<" exact_q_fifth_powers="<<exact<<"\n";
  for(auto [a,b,x,y]:exacts) std::cout<<"EXACT a="<<a<<" b="<<b<<" root="<<x<<"+"<<y<<"*phi\n";
  std::cout<<"nearest fifth-power discrepancies by box:\n";
  for(size_t j=0;j<cuts.size();++j) {
    auto const &z=best[j];
    std::cout<<"  H<="<<cuts[j]<<" min_rel="<<(double)z.rel
             <<" root_rel="<<(double)z.rootRel
             <<" at (a,b)=("<<z.a<<","<<z.b<<") root=("<<z.x<<","<<z.y<<")"
             <<" q_coeff=("<<z.A<<","<<z.B<<") fifth_coeff=("<<z.P<<","<<z.Q<<")"
             <<" coeff_resid=("<<(z.A-z.P)<<","<<(z.B-z.Q)<<")\n";
  }
  std::cout<<"Interpretation: rel=max over the two real embeddings of |gamma^5-q|/q; root_rel is the analogous relative gap between gamma and the positive real fifth-root of q.\n";
  return 0;
}
