import sympy as sp
A,H=sp.symbols('a h')
N=140

def mul(X,Y):
 Z=[sp.Integer(0)]*(N+1)
 for i,a in enumerate(X):
  if a:
   for j,b in enumerate(Y[:N+1-i]):
    if b:Z[i+j]+=a*b
 return Z
def inv(X):
 Z=[sp.Integer(0)]*(N+1);Z[0]=1/X[0]
 for n in range(1,N+1):Z[n]=-sum(X[k]*Z[n-k] for k in range(1,n+1))/X[0]
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
def add(X,Y):return [X[i]+Y[i] for i in range(N+1)]
def scale(X,c):return [c*z for z in X]
def compose(poly,X,var):
 Z=[0]*(N+1)
 for c in reversed(sp.Poly(poly,var).all_coeffs()):Z=add(mul(Z,X),[c]+[0]*N)
 return Z
E1,E5,E7,E35=eta(1),eta(5),eta(7),eta(35)
a=shift(scale(mul(power(E7,4),power(E1,-4)),49),1)
h=shift(scale(mul(power(E5,6),power(E1,-6)),125),1)
x=shift(mul(mul(E1,E35),mul(inv(E5),inv(E7))),1)
xx=sp.symbols('x');f=xx**8-4*xx**7-6*xx**6-4*xx**5-9*xx**4+4*xx**3-6*xx**2+4*xx+1
fx=compose(f,x,xx)
y=[0]*(N+1);y[0]=1
for n in range(1,N+1):y[n]=(fx[n]-sum(y[k]*y[n-k] for k in range(1,n)))/2

maxd=14
ap=[None]*(maxd+1);hp=[None]*(maxd+1)
ap[0]=[1]+[0]*N;hp[0]=[1]+[0]*N
for i in range(maxd):ap[i+1]=mul(ap[i],a);hp[i+1]=mul(hp[i],h)

def mons(d):
 out=[]
 for i in range(d+1):
  for j in range(d+1-i):out.append((i,j,mul(ap[i],hp[j])))
 return out

def fit(T,maxdeg=10):
 for dr in range(maxdeg+1):
  MR=mons(dr)
  for dp in range(maxdeg+1):
   MP=mons(dp)
   cols=[mul(T,z) for _,_,z in MR]+[scale(z,-1) for _,_,z in MP]
   rows=min(N+1,len(cols)+25)
   ns=sp.Matrix([[cols[j][k] for j in range(len(cols))] for k in range(rows)]).nullspace()
   for v in ns:
    if not any(v[i] for i in range(len(MR))):continue
    test=[0]*(N+1)
    for c,z in zip(v,cols):test=add(test,scale(z,c))
    if all(z==0 for z in test):
     R=sum(v[k]*A**i*H**j for k,(i,j,_) in enumerate(MR))
     P=sum(v[len(MR)+k]*A**i*H**j for k,(i,j,_) in enumerate(MP))
     print('degrees',dr,dp);print('R=',sp.factor(R));print('P=',sp.factor(P));print('T=P/R')
     return sp.factor(P),sp.factor(R)
 raise RuntimeError('no fit')
print('X_INVERSE');px,rx=fit(x,10)
print('Y_INVERSE');py,ry=fit(y,10)
