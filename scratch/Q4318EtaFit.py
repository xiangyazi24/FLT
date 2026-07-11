import sympy as sp
x=sp.symbols('x')
f=x**8-4*x**7-6*x**6-4*x**5-9*x**4+4*x**3-6*x**2+4*x+1
N=110

def mul(A,B):
 C=[sp.Integer(0)]*(N+1)
 for i,a in enumerate(A):
  if a:
   for j,b in enumerate(B[:N+1-i]):
    if b: C[i+j]+=a*b
 return C
def inv(A):
 assert A[0]!=0
 B=[sp.Integer(0)]*(N+1); B[0]=1/A[0]
 for n in range(1,N+1): B[n]=-sum(A[k]*B[n-k] for k in range(1,n+1))/A[0]
 return B
def power(A,n):
 if n<0: return power(inv(A),-n)
 B=[sp.Integer(0)]*(N+1);B[0]=1
 while n:
  if n&1:B=mul(B,A)
  A=mul(A,A);n//=2
 return B
def shift(A,k): return [sp.Integer(0)]*k+A[:N+1-k]
def prod_eta(m):
 A=[sp.Integer(0)]*(N+1);A[0]=1
 for n in range(m,N+1,m):
  B=[sp.Integer(0)]*(N+1);B[0]=1;B[n]=-1
  A=mul(A,B)
 return A
def add(A,B):return [A[i]+B[i] for i in range(N+1)]
def scale(A,c):return [c*z for z in A]
def compose_poly(poly,A):
 B=[sp.Integer(0)]*(N+1)
 for coeff in sp.Poly(poly,x).all_coeffs(): B=add(mul(B,A),[coeff]+[0]*N)
 return B
def series_powers(A,maxd):
 out=[[sp.Integer(0)]*(N+1) for _ in range(maxd+1)];out[0][0]=1
 for i in range(maxd):out[i+1]=mul(out[i],A)
 return out

E1=prod_eta(1);E5=prod_eta(5);E7=prod_eta(7);E35=prod_eta(35)
a=shift([49*z for z in mul(power(E7,4),power(E1,-4))],1)
h=shift([125*z for z in mul(power(E5,6),power(E1,-6))],1)
xx=scale(shift(mul(mul(E1,E35),mul(inv(E5),inv(E7))),1),-1)
fx=compose_poly(f,xx)
y=[sp.Integer(0)]*(N+1);y[0]=1
for n in range(1,N+1): y[n]=(fx[n]-sum(y[k]*y[n-k] for k in range(1,n)))/2
xp=series_powers(xx,20)

def fit(T,maxd=12):
 for dR in range(maxd+1):
  for dP in range(maxd+1):
   for dQ in range(maxd+1):
    cols=[];names=[]
    for i in range(dR+1): cols.append(mul(T,xp[i]));names.append(('R',i))
    for i in range(dP+1): cols.append(scale(xp[i],-1));names.append(('P',i))
    for i in range(dQ+1): cols.append(scale(mul(y,xp[i]),-1));names.append(('Q',i))
    rows=min(N+1,len(cols)+25)
    ns=sp.Matrix([[cols[j][i] for j in range(len(cols))] for i in range(rows)]).nullspace()
    for v in ns:
     if not any(v[i]!=0 for i,nm in enumerate(names) if nm[0]=='R'): continue
     S=[sp.Integer(0)]*(N+1)
     for vv,col in zip(v,cols): S=add(S,scale(col,vv))
     if all(z==0 for z in S):
      polys={k:sp.Integer(0) for k in ['R','P','Q']}
      for vv,(k,i) in zip(v,names):polys[k]+=vv*x**i
      g=sp.gcd(sp.gcd(sp.Poly(polys['R'],x),sp.Poly(polys['P'],x)),sp.Poly(polys['Q'],x)).as_expr()
      for k in polys:polys[k]=sp.factor(polys[k]/g)
      return dR,dP,dQ,polys
 raise RuntimeError('no fit')

da,pa1,qa,pa=fit(a)
dh,ph1,qh,ph=fit(h)
print('A_DEGREES',da,pa1,qa)
print('A_R',pa['R']);print('A_P',pa['P']);print('A_Q',pa['Q'])
print('H_DEGREES',dh,ph1,qh)
print('H_R',ph['R']);print('H_P',ph['P']);print('H_Q',ph['Q'])
yv=sp.symbols('y')
AA=(pa['P']+yv*pa['Q'])/pa['R']; HH=(ph['P']+yv*ph['Q'])/ph['R']
F=HH*(AA**2+13*AA+49)*(AA**2+5*AA+1)**3-AA*(HH**2+10*HH+5)**3
num=sp.together(F).as_numer_denom()[0]
red=sp.Poly(num,yv).rem(sp.Poly(yv**2-f,yv)).as_expr()
print('CERT_ZERO',sp.expand(red)==0)
if red!=0:
 p=sp.Poly(red,x,yv)
 print('CERT_DEGREES',p.degree(x),p.degree(yv),'TERMS',len(p.terms()))
 print('CERT_FACTOR_SMALL',sp.factor(red).as_ordered_factors()[:5])
