#include <array>
#include <iostream>
#include <vector>
using V6 = std::array<int,6>;
using V12 = std::array<int,12>;
static int m5(int x){ x%=5; if(x<0)x+=5; return x; }
static V6 add(V6 a,V6 b){for(int i=0;i<6;i++)a[i]=m5(a[i]+b[i]);return a;}
static V6 scale(int s,V6 a){for(int&i:a)i=m5(s*i);return a;}
static V6 sub(V6 a,V6 b){return add(a,scale(4,b));}
static bool eq(V6 a,V6 b){return a==b;}
static void p6(const char* n,V6 a){std::cout<<n<<" = (";for(int i=0;i<6;i++){if(i)std::cout<<",";std::cout<<a[i];}std::cout<<")\n";}
static void p12(const char* n,V12 a){std::cout<<n<<" = (";for(int i=0;i<12;i++){if(i)std::cout<<",";std::cout<<a[i];}std::cout<<")\n";}
static int dot(V12 a,V12 b){int s=0;for(int i=0;i<12;i++)s=m5(s+a[i]*b[i]);return s;}
int main(){
  V6 c0{0,0,1,0,0,3};
  V6 c1{0,0,4,1,0,2};
  V6 c2{0,0,1,2,3,4};
  V6 c3{0,0,4,2,4,0};
  std::array<int,4> w{1,3,4,2};
  std::array<V6,4> c{c0,c1,c2,c3};
  V6 ws{};
  for(int i=0;i<4;i++) ws=add(ws,scale(w[i],c[i]));
  p6("weighted_sum",ws);
  V6 A=sub(c1,c0), B=sub(c2,c0), C=sub(c3,c0), Cfrom=add(A,scale(3,B));
  p6("A=c1-c0",A); p6("B=c2-c0",B); p6("C=c3-c0",C); p6("A+3B",Cfrom);
  V12 gauge{}; for(int i=0;i<6;i++){gauge[i]=A[i];gauge[6+i]=B[i];}
  p12("gauge(branchValueMatrix@t=2)",gauge);
  V12 g{0,0,3,1,0,4,0,0,0,2,3,1};
  V12 k5{0,0,2,2,2,0,0,0,0,0,0,0};
  V12 ell{0,0,1,2,0,0,0,0,0,0,0,0};
  std::cout<<"gauge_equals_compiled_localImageGenerator = "<<(gauge==g?"true":"false")<<"\n";
  std::cout<<"C_equals_A_plus_3B = "<<(eq(C,Cfrom)?"true":"false")<<"\n";
  std::cout<<"ell(g) = "<<dot(ell,g)<<"\n";
  std::cout<<"ell(k5) = "<<dot(ell,k5)<<"\n";
  std::cout<<"\nGauge matrix G (12x24), columns grouped c0|c1|c2|c3:\n";
  for(int r=0;r<12;r++){
    for(int col=0;col<24;col++){
      int block=col/6, j=col%6, val=0;
      if(r<6){ int i=r; if(j==i && block==0) val=4; if(j==i && block==1) val=1; }
      else { int i=r-6; if(j==i && block==0) val=4; if(j==i && block==2) val=1; }
      if(col) std::cout<<" "; std::cout<<val;
    }
    std::cout<<"\n";
  }
  std::cout<<"\nDiagonal-kill check on symbolic basis blocks:\n";
  bool diag=true;
  for(int j=0;j<6;j++){
    V6 d{}; d[j]=1;
    V6 a=sub(d,d),b=sub(d,d);
    if(a!=V6{}||b!=V6{}) diag=false;
  }
  std::cout<<"G(d,d,d,d)=0 for each standard d = "<<(diag?"true":"false")<<"\n";
  std::cout<<"change_of_basis_needed_for_compiled_constants = identity\n";
}
