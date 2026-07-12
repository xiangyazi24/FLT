print('BEGIN_Q4570_VERIFY')
R.<s,t,x,y,z,X> = PolynomialRing(QQ)
F = X^3-432*X+8208
hcurve = y^2-x^3+432*x*z^4-8208*z^6
h1 = s^2-3*x-2*t
h2 = t^2-3*x^2+432*z^4+2*s*y
I=R.ideal([hcurve,h1,h2])
line_num=s*x-y-s*z^2*X
rhs=-(z^2*X-x-t)^2*(z^2*X-x)
identity=line_num^2-z^6*F-rhs
print('TANGENT_REDUCE',I.reduce(identity))
q=(x+t)/z^2
r=(-y-s*t)/z^3
# Clear denominators for curve equation at q,r.
half_curve=z^6*(r^2-(q^3-432*q+8208))
print('HALF_CURVE_REDUCE',I.reduce(half_curve))
# Minimal-model doubling denominator identity.
S.<A,B,C> = PolynomialRing(QQ)
d=2*B+C^3
lam_num=A*(3*A-2*C^2)
N=A^2*(3*A-2*C^2)^2+(C^2-2*A)*d^2
# x2 by standard formula from x=A/C^2,y=B/C^3
xq=A/C^2; yq=B/C^3
lam=(3*xq^2-2*xq)/(2*yq+1)
x2=lam^2+1-2*xq
print('DOUBLE_X_DIFF', (x2-N/(C*d)^2).factor())
# Translation by A0=(0,0) on y^2+y=x^3-x^2.
xtrans=-yq/xq^2
ytrans=-(xq^2+yq)/xq^3
# Verify transformed point equation using original equation after clearing.
eq_orig=yq^2+yq-xq^3+xq^2
eq_trans=ytrans^2+ytrans-xtrans^3+xtrans^2
print('TRANS_A_FACTOR',eq_trans.factor())
print('END_Q4570_VERIFY')
