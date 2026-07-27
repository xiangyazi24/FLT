#include <boost/multiprecision/cpp_int.hpp>
#include <iostream>
#include <vector>

using boost::multiprecision::cpp_int;

static cpp_int absz(cpp_int x){if(x<0)x=-x;return x;}
static cpp_int gcdz(cpp_int a, cpp_int b){a=absz(a);b=absz(b);while(b!=0){cpp_int r=a%b;a=b;b=r;}return a;}
static std::vector<int> primes_up_to(int N){std::vector<bool>a(N+1,true);a[0]=a[1]=false;for(int i=2;1LL*i*i<=N;++i)if(a[i])for(int j=i*i;j<=N;j+=i)a[j]=false;std::vector<int>p;for(int i=2;i<=N;++i)if(a[i])p.push_back(i);return p;}

int main(){
  const int M=300; // Exact integer recurrence; finite scan is diagnostic only.
  std::vector<cpp_int>b(M+1),c(M+1),e(M+1);
  b[0]=1;b[1]=5;c[0]=0;c[1]=12;e[0]=0;e[1]=0;
  auto ps=primes_up_to(2000000);
  for(int n=1;n<M;++n){
    cpp_int n2=cpp_int(n)*n,n3=n2*n,u=n+1,u2=u*u,u3=u2*u;
    cpp_int A=34*n3+51*n2+27*n+5;
    cpp_int A1=102*n2+102*n+27;
    cpp_int A2=204*n+102;
    cpp_int nb=A*b[n]-n3*b[n-1];
    cpp_int nc=A*c[n]-n3*c[n-1]+A1*b[n]-3*u2*(nb/u3)-3*n2*b[n-1];
    cpp_int ne=A*e[n]-n3*e[n-1]+2*A1*c[n]+A2*b[n]-6*u2*(nc/u3)-6*u*(nb/u3)-6*n2*c[n-1]-6*n*b[n-1];
    if(nb%u3!=0||nc%u3!=0||ne%u3!=0){std::cout<<"NONINTEGER at n="<<n<<"\n";return 1;}
    b[n+1]=nb/u3;c[n+1]=nc/u3;e[n+1]=ne/u3;
    cpp_int g=gcdz(gcdz(b[n+1],c[n+1]),e[n+1]);
    cpp_int rem=g;
    std::vector<long long> factors;
    for(int p:ps){if(p>n+1 && rem%p==0){factors.push_back(p);while(rem%p==0)rem/=p;} else if(p<=n+1){while(rem%p==0)rem/=p;}}
    if(!factors.empty() || rem!=1){
      std::cout<<"m="<<n+1<<" gcd="<<g<<" factors_gt_m=";
      for(auto p:factors)std::cout<<p<<',';
      std::cout<<" residual="<<rem<<"\n";
    }
  }
}
