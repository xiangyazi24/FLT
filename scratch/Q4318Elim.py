import sympy as sp
x,y,a,h=sp.symbols('x y a h')
f=x**8-4*x**7-6*x**6-4*x**5-9*x**4+4*x**3-6*x**2+4*x+1
Pa=-x**6-5*x**5+5*x**3-5*x+1
Qa=x**2+3*x-1
Ph=(x**2+1)*(x**6+7*x**5+6*x**4-21*x**3-6*x**2+7*x-1)
Qh=(x**2+x-1)*(x**2+4*x-1)
# Candidate exact formulas a=(Pa+yQa)/(2x^5), h=(Ph+yQh)/(-2x^7)
R1=sp.expand(2*a*x**5-Pa-y*Qa)
R2=sp.expand(-2*h*x**7-Ph-y*Qh)
El=sp.expand(sp.resultant(R1,R2,y))
print('EL_DEG_X=',sp.degree(El,x),'TERMS=',len(sp.Poly(El,x,a,h).terms()))
print('EL_FACTOR=',sp.factor(El))
K=sp.QQ.frac_field(a,h)
print('EL_FACTOR_K=',sp.factor(sp.Poly(El,x,domain=K).as_expr(),extension=True))
# Groebner with F(a,h) to see rational linear factor / reduction.
F=sp.expand(h*(a**2+13*a+49)*(a**2+5*a+1)**3-a*(h**2+10*h+5)**3)
print('F_DEG=',sp.degree(F,a),sp.degree(F,h))
# Verify forward certificate modulo y^2=f.
AA=(Pa+y*Qa)/(2*x**5); HH=(Ph+y*Qh)/(-2*x**7)
num=sp.together(HH*(AA**2+13*AA+49)*(AA**2+5*AA+1)**3-AA*(HH**2+10*HH+5)**3).as_numer_denom()[0]
red=sp.Poly(sp.expand(num),y).rem(sp.Poly(y**2-f,y)).as_expr()
print('FORWARD_CERT_ZERO=',sp.expand(red)==0)
if red!=0: print('FORWARD_CERT_FACTOR=',sp.factor(red))
