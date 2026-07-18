import sympy as sp
A,H=sp.symbols('a h')
N=160

def mul(X,Y):
 Z=[sp.Integer(0)]*(N+1)
 for i,a in enumerate(X):
  if a:
   for j,b in enumerate(Y[:N+1-i]):
    if b:Z[i+j]+=a*b
 return Z
def inv(X):
 assert X[0]!=0
 Z=[sp.Integer(0)]*(N+1);Z[0]=1/X[0]
 for n in range(1,N+1):Z[n]=-sum(X[k]*Z[n-k] for k in range(1,n+1))/X[0]
 return Z
def div(X,Y):return mul(X,inv(Y))
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
def sub(X,Y):return [X[i]-Y[i] for i in range(N+1)]
def scale(X,c):return [c*z for z in X]
def compose(poly,X,var):
 Z=[0]*(N+1)
 for c in sp.Poly(poly,var).all_coeffs():Z=add(mul(Z,X),[c]+[0]*N)
 return Z

E1,E5,E7,E35=eta(1),eta(5),eta(7),eta(35)
a=shift(scale(mul(power(E7,4),power(E1,-4)),49),1)
h=shift(scale(mul(power(E5,6),power(E1,-6)),125),1)
x=scale(shift(mul(mul(E1,E35),mul(inv(E5),inv(E7))),1),-1)
xx=sp.symbols('x');f=xx**8-4*xx**7-6*xx**6-4*xx**5-9*xx**4+4*xx**3-6*xx**2+4*xx+1
fx=compose(f,x,xx)
y=[0]*(N+1);y[0]=1
for n in range(1,N+1):y[n]=(fx[n]-sum(y[k]*y[n-k] for k in range(1,n)))/2
one=[1]+[0]*N
x2=mul(x,x)
den=add(add(x2,x),scale(one,-1)) # x^2+x-1
XE=div(add(add(x2,scale(x,-6)),scale(one,-1)),den)
YE=scale(div(add(mul(den,den),scale(y,7)),scale(mul(den,den),2)),-1)
print('E series X',XE[:12]);print('E series Y',YE[:12])

maxd=15
ap=[None]*(maxd+1);hp=[None]*(maxd+1)
ap[0]=one;hp[0]=one
for i in range(maxd):ap[i+1]=mul(ap[i],a);hp[i+1]=mul(hp[i],h)
def mons(d):return [(i,j,mul(ap[i],hp[j])) for i in range(d+1) for j in range(d+1-i)]

def fit(T,maxdeg=12):
 for dr in range(maxdeg+1):
  MR=mons(dr)
  for dp in range(maxdeg+1):
   MP=mons(dp)
   cols=[mul(T,z) for _,_,z in MR]+[scale(z,-1) for _,_,z in MP]
   rows=min(N+1,len(cols)+35)
   ns=sp.Matrix([[cols[j][k] for j in range(len(cols))] for k in range(rows)]).nullspace()
   for v in ns:
    if not any(v[i] for i in range(len(MR))):continue
    test=[0]*(N+1)
    for c,z in zip(v,cols):test=add(test,scale(z,c))
    if all(z==0 for z in test):
     R=sum(v[k]*A**i*H**j for k,(i,j,_) in enumerate(MR))
     P=sum(v[len(MR)+k]*A**i*H**j for k,(i,j,_) in enumerate(MP))
     # primitive integer normalization
     R=sp.factor(R);P=sp.factor(P)
     print('degrees',dr,dp);print('R=',R);print('P=',P);print('T=P/R')
     return P,R
 raise RuntimeError('no fit')
print('FIT_XE'); PX,RX=fit(XE,12)
print('FIT_YE'); PY,RY=fit(YE,12)
# Certify E equation modulo plane F(a,h).
Fplane=H*(A**2+13*A+49)*(A**2+5*A+1)**3-A*(H**2+10*H+5)**3
expr=sp.together((PY/RY)**2+PY/RY-(PX/RX)**3-(PX/RX)**2-9*PX/RX-1)
num=sp.factor(expr.as_numer_denom()[0])
Q,Rem=sp.div(sp.Poly(num,H,A),sp.Poly(Fplane,H,A))
print('E_CERT_DIVISIBLE',Rem.is_zero)
if Rem.is_zero:
 print('E_CERT_QUOTIENT_FACTOR',sp.factor(Q.as_expr()))
else:
 print('E_CERT_REM_DEGREES',Rem.degree(H),Rem.degree(A),'TERMS',len(Rem.terms()))
