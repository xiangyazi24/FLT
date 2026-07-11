import sympy as sp
x=sp.symbols('x')
f=x**8-4*x**7-6*x**6-4*x**5-9*x**4+4*x**3-6*x**2+4*x+1
print('factor f-1',sp.factor(f-1))
# polynomial square approximations at infinity
c=sp.symbols('c0:5')
g=x**4+c[3]*x**3+c[2]*x**2+c[1]*x+c[0]
expr=sp.Poly(sp.expand(f-g**2),x)
sol=sp.solve([expr.coeff_monomial(x**k) for k in range(4,8)], [c[3],c[2],c[1],c[0]], dict=True)
print('sqrt poly sols',sol)
for ss in sol:
 gg=sp.expand(g.subs(ss)); print('g=',gg,'f-g2=',sp.factor(f-gg**2))

N=80
# truncated coefficient lists q^0..N
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
E1=prod_eta(1);E5=prod_eta(5);E7=prod_eta(7);E35=prod_eta(35)
# omit q prefactors then shift by q
a=shift([49*z for z in mul(power(E7,4),power(E1,-4))],1)
h=shift([125*z for z in mul(power(E5,6),power(E1,-6))],1)
xx=shift(mul(mul(E1,E35),mul(inv(E5),inv(E7))),1)
print('a first',a[:12]);print('h first',h[:12]);print('x first',xx[:12])
# compose polynomial f(xx)
def add(A,B):return [A[i]+B[i] for i in range(N+1)]
def scale(A,c):return [c*z for z in A]
def compose_poly(poly,A):
 B=[sp.Integer(0)]*(N+1)
 for coeff in reversed(sp.Poly(poly,x).all_coeffs()):
  B=add(mul(B,A),[coeff]+[0]*N)
 return B
fx=compose_poly(f,xx)
# sqrt series y^2=fx, y0=1
y=[sp.Integer(0)]*(N+1);y[0]=1
for n in range(1,N+1):
 y[n]=(fx[n]-sum(y[k]*y[n-k] for k in range(1,n)))/2
print('y first',y[:12])
# Verify possible eta x sign by hyperell curve only formal definition (always okay).
# Fit target T as (P(x)+y Q(x))/R(x), R monic/generic degree dR.
def series_powers(A,maxd):
 out=[[sp.Integer(0)]*(N+1) for _ in range(maxd+1)];out[0][0]=1
 for i in range(maxd):out[i+1]=mul(out[i],A)
 return out
xp=series_powers(xx,16)
# equation T*R(x)-P(x)-yQ(x)=0, linear homogeneous; set degree bounds and find nullspace.
def fit(T,maxd=10):
 for dR in range(0,maxd+1):
  for dP in range(0,maxd+1):
   for dQ in range(0,maxd+1):
    cols=[];names=[]
    for i in range(dR+1): cols.append(mul(T,xp[i]));names.append(('R',i))
    for i in range(dP+1): cols.append(scale(xp[i],-1));names.append(('P',i))
    for i in range(dQ+1): cols.append(scale(mul(y,xp[i]),-1));names.append(('Q',i))
    rows=min(N+1,len(cols)+15)
    M=sp.Matrix([[cols[j][i] for j in range(len(cols))] for i in range(rows)])
    ns=M.nullspace()
    if ns:
     for v in ns:
      if any(v[i]!=0 for i,nm in enumerate(names) if nm[0]=='R'):
       # verify all coeffs
       S=[sp.Integer(0)]*(N+1)
       for vv,col in zip(v,cols): S=add(S,scale(col,vv))
       if all(z==0 for z in S):
        print('FIT',dR,dP,dQ,list(zip(names,list(v))))
        return names,v
 print('no fit')
print('fit a');fit(a,9)
print('fit h');fit(h,9)
