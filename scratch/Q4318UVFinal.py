import sympy as sp
A,H=sp.symbols('a h')
N=130

def mul(X,Y):
 Z=[sp.Integer(0)]*(N+1)
 for i,a0 in enumerate(X):
  if a0:
   for j in range(N+1-i):
    b0=Y[j]
    if b0: Z[i+j]+=a0*b0
 return Z

def add(X,Y): return [X[i]+Y[i] for i in range(N+1)]
def scale(X,c): return [c*z for z in X]
def inv(X):
 assert X[0] != 0
 Z=[sp.Integer(0)]*(N+1); Z[0]=sp.cancel(1/X[0])
 for n in range(1,N+1): Z[n]=sp.cancel(-sum(X[k]*Z[n-k] for k in range(1,n+1))/X[0])
 return Z

def power(X,n):
 if n<0:return power(inv(X),-n)
 Z=[sp.Integer(0)]*(N+1);Z[0]=1
 while n:
  if n&1:Z=mul(Z,X)
  X=mul(X,X);n//=2
 return Z

def shift(X,k):return [0]*k+X[:N+1-k]
def eta(m):
 X=[0]*(N+1);X[0]=1
 for n in range(m,N+1,m):
  B=[0]*(N+1);B[0]=1;B[n]=-1;X=mul(X,B)
 return X

def compose(poly,X,var):
 Z=[0]*(N+1)
 for c in sp.Poly(poly,var).all_coeffs(): Z=add(mul(Z,X),[c]+[0]*N)
 return Z

E1,E5,E7,E35=eta(1),eta(5),eta(7),eta(35)
a=shift(scale(mul(power(E7,4),power(E1,-4)),49),1)
h=shift(scale(mul(power(E5,6),power(E1,-6)),125),1)
x=shift(mul(mul(E1,E35),mul(inv(E5),inv(E7))),1)
xx=sp.symbols('x')
f=xx**8-4*xx**7-6*xx**6-4*xx**5-9*xx**4+4*xx**3-6*xx**2+4*xx+1
fx=compose(f,x,xx)
y=[0]*(N+1);y[0]=1
for n in range(1,N+1): y[n]=sp.cancel((fx[n]-sum(y[k]*y[n-k] for k in range(1,n)))/2)
one=[1]+[0]*N
den=add(add(mul(x,x),x),scale(one,-1))
k=mul(x,inv(den))
m=mul(y,power(den,-2))
print('k_first=',k[:20]);print('m_first=',m[:20])

maxd=8
ap=[None]*(maxd+1);hp=[None]*(maxd+1);ap[0]=one;hp[0]=one
for i in range(maxd):ap[i+1]=mul(ap[i],a);hp[i+1]=mul(hp[i],h)
def mons(d):return [(i,j,mul(ap[i],hp[j])) for i in range(d+1) for j in range(d+1-i)]
def fit(T,name,maxdeg=7):
 for bound in range(maxdeg+1):
  for dr in range(bound+1):
   dp=bound-dr
   MR=mons(dr); MP=mons(dp)
   cols=[mul(T,z) for _,_,z in MR]+[scale(z,-1) for _,_,z in MP]
   rows=min(N+1,len(cols)+40)
   M=sp.Matrix([[cols[j][n] for j in range(len(cols))] for n in range(rows)])
   for vv in M.nullspace():
    if not any(vv[i] for i in range(len(MR))):continue
    test=[0]*(N+1)
    for c,z in zip(vv,cols):test=add(test,scale(z,c))
    if all(z==0 for z in test):
     R=sum(vv[n]*A**i*H**j for n,(i,j,_) in enumerate(MR))
     P=sum(vv[len(MR)+n]*A**i*H**j for n,(i,j,_) in enumerate(MP))
     g=sp.gcd(sp.Poly(R,A,H),sp.Poly(P,A,H)).as_expr()
     R=sp.factor(R/g);P=sp.factor(P/g)
     print(name+'_DEGREES=',dr,dp);print(name+'_R=',R);print(name+'_P=',P)
     return P,R
 raise RuntimeError('no fit '+name)
pk,rk=fit(k,'K',7)
pm,rm=fit(m,'M',7)
print('DONE')
