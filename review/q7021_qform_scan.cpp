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
#include <vector>

using i128 = __int128_t;
using u128 = __uint128_t;

static std::string s128(i128 x) {
  if (x == 0) return "0";
  bool neg = x < 0;
  u128 u = neg ? (u128)(-x) : (u128)x;
  std::string s;
  while (u) { s.push_back(char('0' + u % 10)); u /= 10; }
  if (neg) s.push_back('-');
  std::reverse(s.begin(), s.end());
  return s;
}

struct Qphi { i128 a, b; }; // a + b phi, phi^2=phi+1
static Qphi mul(Qphi x, Qphi y) {
  return {x.a*y.a + x.b*y.b, x.a*y.b + x.b*y.a + x.b*y.b};
}
static Qphi pow5(Qphi x) {
  Qphi x2=mul(x,x), x4=mul(x2,x2); return mul(x4,x);
}
static u128 upow5(uint64_t x) {
  u128 y=x; return y*y*y*y*y;
}
static bool is_u64_fifth(uint64_t n, uint64_t &r) {
  long double z = std::pow((long double)n, 0.2L);
  uint64_t c = (uint64_t)std::llround(z);
  uint64_t lo = c > 8 ? c-8 : 0, hi=c+8;
  for (uint64_t k=lo;k<=hi;k++) if (upow5(k)==(u128)n) {r=k; return true;}
  return false;
}

struct Best {
  long double delta=2.0L;
  long double rel=1e300L;
  long long a=0,b=0,m=0,n=0;
  long double ms=0,ns=0;
};

int main(int argc,char**argv){
  int B = argc>1 ? std::atoi(argv[1]) : 10000;
  std::array<int,4> cuts={100,1000,3000,10000};
  if(B<10000) cuts={B,B,B,B};
  std::array<Best,4> best;
  std::array<unsigned long long,4> count{}, norm5{}, exact5{};
  const long double sq5=std::sqrt((long double)5.0);
  const long double phip=(1+sq5)/2, phim=(1-sq5)/2;
  const long double cplus=(5-sq5)/2, cminus=(5+sq5)/2;

  auto idx_for=[&](long long a,long long b,int j){return std::llabs(a)<=cuts[j] && b<=cuts[j];};
  for(long long b=5;b<=B;b+=5){
    for(long long a=-B;a<=B;a++){
      if(std::gcd(std::llabs(a),b)!=1) continue;
      i128 A=(i128)a*a + (i128)3*a*b + (i128)5*b*b;
      i128 C=-(i128)a*b;
      i128 N=A*A+A*C-C*C;
      if(N<=0 || N>(i128)std::numeric_limits<uint64_t>::max()) { std::cerr<<"norm range failure\n"; return 2; }
      uint64_t nr=0; bool n5=is_u64_fifth((uint64_t)N,nr);
      long double qp=(long double)a*a + (long double)a*b*cplus + (long double)5*b*b;
      long double qm=(long double)a*a + (long double)a*b*cminus + (long double)5*b*b;
      if(!(qp>0 && qm>0)){std::cerr<<"positivity failure\n";return 3;}
      long double rp=std::pow(qp,0.2L), rm=std::pow(qm,0.2L);
      long double ns=(rp-rm)/sq5;
      long double ms=(phip*rm-phim*rp)/sq5;
      long long m0=std::llround(ms), n0=std::llround(ns);
      long double delta=std::max(std::fabsl(ms-m0),std::fabsl(ns-n0));
      bool ex=false; long double bestrel=1e300L; long long bm=m0,bn=n0;
      for(long long dm=-2;dm<=2;dm++) for(long long dn=-2;dn<=2;dn++){
        long long m=m0+dm,n=n0+dn;
        Qphi p=pow5({(i128)m,(i128)n});
        if(p.a==A && p.b==C) ex=true;
        long double xp=(long double)m+(long double)n*phip;
        long double xm=(long double)m+(long double)n*phim;
        long double rel=std::max(std::fabsl(std::pow(xp,5)-qp)/qp,std::fabsl(std::pow(xm,5)-qm)/qm);
        if(rel<bestrel){bestrel=rel;bm=m;bn=n;}
      }
      for(int j=0;j<4;j++) if(idx_for(a,b,j)){
        count[j]++;
        if(n5) norm5[j]++;
        if(ex) exact5[j]++;
        if(delta<best[j].delta){best[j].delta=delta;best[j].a=a;best[j].b=b;best[j].ms=ms;best[j].ns=ns;}
        if(bestrel<best[j].rel){best[j].rel=bestrel;best[j].m=bm;best[j].n=bn;}
      }
    }
  }
  std::cout<<std::setprecision(18);
  std::cout<<"FORMULA q=A+Bphi with A=a^2+3ab+5b^2, B=-ab\n";
  std::cout<<"Norm(q)=a^4+5a^3b+15a^2b^2+25ab^3+25b^4\n";
  std::cout<<"scan conditions: b>0, 5|b, gcd(a,b)=1, |a|<=box, b<=box\n";
  for(int j=0;j<4;j++){
    std::cout<<"BOX="<<cuts[j]<<" primitive_pairs="<<count[j]<<" norm_perfect_fifths="<<norm5[j]<<" q_exact_fifths="<<exact5[j]<<"\n";
    std::cout<<"  min_root_lattice_delta="<<(double)best[j].delta<<" at (a,b)=("<<best[j].a<<","<<best[j].b<<") root_coords=("<<(double)best[j].ms<<","<<(double)best[j].ns<<")\n";
    std::cout<<"  min_relative_embedding_residual="<<(double)best[j].rel<<" nearest_x=("<<best[j].m<<")+("<<best[j].n<<")phi\n";
  }
  std::cout<<"DONE\n";
}
