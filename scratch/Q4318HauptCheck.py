import sympy as sp
t,X=sp.symbols('t X')
a1=1+t-t**2; a2=t**2*(1-t); a3=a2
b2=sp.expand(a1**2+4*a2)
b4=sp.expand(a1*a3)
b6=sp.expand(a3**2)
b8=sp.expand(a2*a3**2)
c4=sp.expand(b2**2-24*b4)
Delta=sp.expand(-b2**2*b8-8*b4**3-27*b6**2+9*b2*b4*b6)
D=sp.expand(4*X**3+b2*X**2+2*b4*X+b6)
phi2=sp.expand(X**4-b4*X**2-2*b6*X-b8)
A=sp.expand(phi2-X*D)
psi3=sp.expand(3*X**4+b2*X**3+3*b4*X**2+3*b6*X+b8)
F4=sp.expand(2*X**6+b2*X**5+5*b4*X**4+10*b6*X**3+10*b8*X**2+(b2*b8-b4*b6)*X+(b4*b8-b6**2))
psi5=sp.expand(F4*D**2-psi3**3)
# d=A^3/D^4; h=d-11-1/d = hn/hd.
dn=sp.expand(A**3); dd=sp.expand(D**4)
hn=sp.expand(dn**2-11*dn*dd-dd**2); hd=sp.expand(dn*dd)
B=sp.expand(hn**2+10*hn*hd+5*hd**2)
# j(h)=(h^2+10h+5)^3/h means c4^3/Delta = B^3/(hn*hd^5).
Cert=sp.expand(hn*c4**3*hd**5-Delta*B**3)
Q,R=sp.div(sp.Poly(Cert,X,t),sp.Poly(psi5,X,t))
print('PSI5_DEG_X=',sp.Poly(psi5,X).degree())
print('HAUPT_DIVISIBLE=',R.is_zero)
print('QUOTIENT_DEG_X=',Q.degree(X))
print('QUOTIENT_DEG_T=',Q.degree(t))
print('QUOTIENT_TERMS=',len(Q.terms()))
# Check duplication d -> -1/d modulo psi5.
x2=sp.cancel(phi2/D)
D2=sp.cancel(D.subs(X,x2))
phi22=sp.cancel(phi2.subs(X,x2))
A2=sp.cancel(phi22-x2*D2)
d2=sp.cancel(A2**3/D2**4)
expr=sp.cancel(d2+1/(A**3/D**4))
num=sp.factor(sp.fraction(expr)[0])
Q2,R2=sp.div(sp.Poly(sp.expand(num),X,t),sp.Poly(psi5,X,t))
print('DUPLICATION_D_NEG_INV=',R2.is_zero)
# a7 j identity
a=(t**3-8*t**2+5*t+1)/(t*(t-1))
j7=(a**2+13*a+49)*(a**2+5*a+1)**3/a
jT=c4**3/Delta
print('A7_J_IDENTITY=',sp.cancel(jT-j7)==0)
