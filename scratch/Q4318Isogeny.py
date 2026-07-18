import sympy as sp
x,y=sp.symbols('x y')
a1=4;a3=7
lam=y/x; mu=(y+7)/x
xp=sp.cancel(lam**2+a1*lam-x)
xm=sp.cancel(mu**2+a1*mu-x)
yp=sp.cancel(-(lam*(xp-x)+y)-a1*xp-a3)
ym=sp.cancel(-(mu*(xm-x)+y)-a1*xm-a3)
X=sp.cancel(x+xp+xm)
Y=sp.cancel(y+yp+(ym+7))
rel=y**2+4*x*y+7*y-x**3
K=sp.QQ.frac_field(x)
def red(expr):
 n,d=sp.fraction(sp.cancel(expr))
 nr=sp.Poly(sp.expand(n),y,domain=K).rem(sp.Poly(y**2+4*x*y+7*y-x**3,y,domain=K)).as_expr()
 return sp.factor(sp.cancel(nr/d))
print('X=',red(X))
print('Y=',red(Y))
Xr=red(X); Yr=red(Y)
target=Yr**2+4*Xr*Yr+7*Yr-(Xr**3-140*Xr-791)
print('target remainder=',red(target))
# Compute a rational formula for dual isogeny by running same Velu on target kernel if rational points exist.
# Also print E' rational 3-torsion roots by solving 3-division polynomial with generalized coefficients.
Xv=sp.symbols('X')
b2=16;b4=-280+28 # 2 a4 + a1*a3, a4=-140
b6=49+4*(-791)
b8=a1*a1*(-791) - a1*a3*(-140) - (-140)**2 # a2=0
psi3=sp.factor(3*Xv**4+b2*Xv**3+3*b4*Xv**2+3*b6*Xv+b8)
print('Eprime psi3=',psi3)
