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
# d=A^3/D^4; h=d-11-1/d.
dn=sp.expand(A**3); dd=sp.expand(D**4)
hn=sp.expand(dn**2-11*dn*dd-dd**2); hd=sp.expand(dn*dd)
B=sp.expand(hn**2+10*hn*hd+5*hd**2)
Cert=sp.expand(hn*c4**3*hd**5-Delta*B**3)
print('degrees cert',sp.Poly(Cert,X,t).degree(X),sp.Poly(Cert,X,t).degree(t),'terms',len(sp.Poly(Cert,X,t).terms()))
Q,R=sp.div(sp.Poly(Cert,X,t),sp.Poly(psi5,X,t))
print('divisible',R.is_zero,'QdegX',Q.degree(X),'Qdegt',Q.degree(t),'Qterms',len(Q.terms()))
if R.is_zero:
    print('Qfactor=',sp.factor(Q.as_expr()))
# Direct b-c certificate. lambda numerator/denominator.
lam_num=sp.expand(3*X**2+2*a2*X-a1*sp.symbols('Y'))
# use V=2Y+a1X+a3 to eliminate Y = (V-a1X-a3)/2; c should only use V^2=D eventually.
V=sp.symbols('V')
Y=(V-a1*X-a3)/2
lam=sp.cancel((3*X**2+2*a2*X-a1*Y)/V)
A2=sp.cancel(a2-a1*lam+3*X-lam**2)
A3=V
# c = 1-(a1+2lam)*A2/A3, d=-A2^3/A3^2
bminus=sp.cancel(-A2**3/A3**2 - (1-(a1+2*lam)*A2/A3))
bmn,bmd=map(sp.expand,sp.fraction(bminus))
# reduce V^2=D
P=sp.Poly(bmn,V,domain=sp.QQ.frac_field(t,X))
rem=P.rem(sp.Poly(V**2-D,V,domain=sp.QQ.frac_field(t,X))).as_expr()
print('bminus remainder=',sp.factor(rem))
