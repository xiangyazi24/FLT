import sympy as sp

t, X, s, r, z = sp.symbols('t X s r z')
q = t**2-t+1
a1=1+t-t**2; a2=t**2*(1-t); a3=a2
b2=sp.expand(a1**2+4*a2)
b4=sp.expand(a1*a3)
b6=sp.expand(a3**2)
b8=sp.expand(a2*a3**2)
psi3=sp.expand(3*X**4+b2*X**3+3*b4*X**2+3*b6*X+b8)
psi2sq=sp.expand(4*X**3+b2*X**2+2*b4*X+b6)
F4=sp.expand(2*X**6+b2*X**5+5*b4*X**4+10*b6*X**3+10*b8*X**2+(b2*b8-b4*b6)*X+(b4*b8-b6**2))
psi5=sp.expand(F4*psi2sq**2-psi3**3)
Xsol=t**2*(t-1)*(r*(t-1)+1)/q
I=sp.cancel(q**12*psi5.subs(X,Xsol)/(t**24*(t-1)**24))
In,Id=map(sp.expand,sp.fraction(I))
K=sp.QQ.frac_field(s,r)
cubic=sp.Poly(t**3-s*t**2+(s-3)*t+1,t,domain=K)
R=(sp.Poly(In,t,domain=K).rem(cubic)*sp.invert(sp.Poly(Id,t,domain=K).rem(cubic),cubic)).rem(cubic)
assert R.degree()==0
R35=sp.Poly(sp.together(R.coeff_monomial(1)),r,domain=sp.QQ[s]).as_expr()
R35=sp.Poly(sp.expand(R35),r,s).as_expr()
N=r**4-2*r**2*s+6*r**2-8*r+s
D=4*r**3+r**2*s**2-7*r**2*s+9*r**2+4*r*s-12*r+4
trace_eq=sp.expand(z*D-r*D-N)
print('starting resultant')
Res=sp.resultant(R35,trace_eq,r)
print('resultant degrees',sp.Poly(Res,s,z).degree(s),sp.Poly(Res,s,z).degree(z),'terms',len(sp.Poly(Res,s,z).terms()))
fl=sp.factor_list(Res)
print('content',fl[0])
for i,(f,e) in enumerate(fl[1]):
    p=sp.Poly(f,s,z)
    print('factor',i,'exp',e,'deg_s',p.degree(s),'deg_z',p.degree(z),'terms',len(p.terms()))
    print('F',i,'=',f)
