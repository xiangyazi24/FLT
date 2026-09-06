#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>

using i128 = __int128_t;
using u128 = __uint128_t;

struct Qphi { i128 a, b; }; // a + b phi, phi^2=phi+1
static Qphi mul(Qphi x, Qphi y) {
  return {x.a*y.a + x.b*y.b, x.a*y.b + x.b*y.a + x.b*y.b};
}
static Qphi pow5(Qphi x) { Qphi x2=mul(x,x), x4=mul(x2,x2); return mul(x4,x); }
static u128 upow5(uint64_t x) { u128 y=x; return y*y*y*y*y; }
static bool is_u64_fifth(uint64_t n, uint64_t &r) {
  double z = std::pow((double)n, 0.2);
  uint64_t c = (uint64_t)std::llround(z), lo = c > 8 ? c-8 : 0, hi=c+8;
  for (uint64_t k=lo;k<=hi;k++) if (upow5(k)==(u128)n) {r=k; return true;}
  return false;
}
static double fifth(double x) { return x*x*x*x*x; }

struct Best { double delta=2.0, rel=1e300, ms=0, ns=0; long long a=0,b=0,m=0,n=0; };

int main(int argc,char**argv){
  int B = argc>1 ? std::atoi(argv[1]) : 10000;
  std::array<int,4> cuts={100,1000,3000,10000};
  std::array<Best,4> best;
  std::array<unsigned long long,4> count{}, norm5{}, exact5{};
  const double sq5=std::sqrt(5.0), phip=(1+sq5)/2, phim=(1-sq5)/2;
  const double cplus=(5-sq5)/2, cminus=(5+sq5)/2;
  for(long long b=5;b<=B;b+=5){
    for(long long a=-B;a<=B;a++){
      if(std::gcd(std::llabs(a),b)!=1) continue;
      i128 A=(i128)a*a + (i128)3*a*b + (i128)5*b*b;
      i128 C=-(i128)a*b;
      i128 N=A*A+A*C-C*C;
      if(N<=0 || N>(i128)std::numeric_limits<uint64_t>::max()) { std::cerr<<"norm range failure\n"; return 2; }
      uint64_t nr=0; bool n5=is_u64_fifth((uint64_t)N,nr), ex=false;
      double qp=(double)a*a + (double)a*b*cplus + (double)5*b*b;
      double qm=(double)a*a + (double)a*b*cminus + (double)5*b*b;
      if(!(qp>0 && qm>0)){std::cerr<<"positivity failure\n";return 3;}
      double rp=std::pow(qp,0.2), rm=std::pow(qm,0.2);
      double ns=(rp-rm)/sq5, ms=(phip*rm-phim*rp)/sq5;
      long long m0=std::llround(ms), n0=std::llround(ns);
      double delta=std::max(std::fabs(ms-m0),std::fabs(ns-n0));
      if(n5){
        for(long long dm=-2;dm<=2;dm++) for(long long dn=-2;dn<=2;dn++){
          Qphi p=pow5({(i128)(m0+dm),(i128)(n0+dn)});
          if(p.a==A && p.b==C) ex=true;
        }
      }
      double xp=(double)m0+(double)n0*phip, xm=(double)m0+(double)n0*phim;
      double rel=std::max(std::fabs(fifth(xp)-qp)/qp,std::fabs(fifth(xm)-qm)/qm);
      for(int j=0;j<4;j++) if(std::llabs(a)<=cuts[j] && b<=cuts[j]){
        count[j]++; if(n5) norm5[j]++; if(ex) exact5[j]++;
        if(delta<best[j].delta) best[j]={delta,best[j].rel,ms,ns,a,b,best[j].m,best[j].n};
        if(rel<best[j].rel){best[j].rel=rel; best[j].m=m0; best[j].n=n0;}
      }
    }
  }
  std::cout<<std::setprecision(17);
  std::cout<<"FORMULA q=A+Bphi with A=a^2+3ab+5b^2, B=-ab\n";
  std::cout<<"Norm(q)=a^4+5a^3b+15a^2b^2+25ab^3+25b^4\n";
  std::cout<<"scan conditions: b>0, 5|b, gcd(a,b)=1, |a|<=box, b<=box\n";
  for(int j=0;j<4;j++){
    std::cout<<"BOX="<<cuts[j]<<" primitive_pairs="<<count[j]<<" norm_perfect_fifths="<<norm5[j]<<" q_exact_fifths="<<exact5[j]<<"\n";
    std::cout<<"  min_root_lattice_delta="<<best[j].delta<<" at (a,b)=("<<best[j].a<<","<<best[j].b<<") root_coords=("<<best[j].ms<<","<<best[j].ns<<")\n";
    std::cout<<"  min_relative_embedding_residual="<<best[j].rel<<" nearest_x=("<<best[j].m<<")+("<<best[j].n<<")phi\n";
  }
  std::cout<<"DONE_FAST_EXACT\n";
}
