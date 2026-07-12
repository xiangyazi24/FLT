from sage.all import *

print('Q4403_TATE_BEGIN')
R.<b,c> = PolynomialRing(QQ)
K = R.fraction_field()
E = EllipticCurve(K,[1-c,-b,-b,0,0])
P = E(K(0),K(0))
print('E_AINVS',E.ainvs())

def ff(q):
    if q == 0:
        return '0'
    return str(q.factor())

Q=9*P
expr=2*Q[1]+(1-c)*Q[0]-b
num=R(expr.numerator())
print('NINE_2TORS_NUM_FACTOR',ff(num))
print('DISC',ff(E.discriminant().numerator()))

# Universal order-9 Tate family.
Rt.<t,X> = PolynomialRing(QQ)
Ft = Rt.fraction_field()
tf=Ft(t); xf=Ft(X)
C9=tf^2*(tf-1)
B9=C9*(tf^2-tf+1)
E9=EllipticCurve(Ft,[1-C9,-B9,-B9,0,0])
Q9=E9(Ft(0),Ft(0))
print('ORDER9_9Q_ZERO',(9*Q9).is_zero())
print('ORDER9_3Q_NONZERO',not (3*Q9).is_zero())
Q5=5*Q9
print('X_5Q',ff(Q5[0].numerator()),'/',ff(Q5[0].denominator()))

# x(2R)=0 numerator, using standard b-invariants.
a1,a2,a3,a4,a6=E9.ainvs()
b2=a1^2+4*a2
b4=a1*a3+2*a4
b6=a3^2+4*a6
b8=a1^2*a6+4*a2*a6-a1*a3*a4+a2*a3^2-a4^2
quart=xf^4-b4*xf^2-2*b6*xf-b8
quart_num=Rt(quart.numerator())
print('HALVING_QUARTIC',ff(quart_num))
lin_num=Rt((xf-Q5[0]).numerator())
lin_den=Rt((xf-Q5[0]).denominator())
# x-Q5x = (lin_num/lin_den); root factor is denominator-cleared linear polynomial.
print('KNOWN_LINEAR',ff(lin_num))
quo,rem=quart_num.quo_rem(lin_num)
print('HALVING_REMAINDER',rem)
print('HALVING_CUBIC',ff(quo))
print('HALVING_CUBIC_TOTAL_DEG',quo.total_degree())

# Solve y from tangent condition 2R=Q: lambda chosen so x(2R)=0.
# On a general Weierstrass curve, lambda=(3x^2+2a2*x+a4-a1*y)/(2y+a1*x+a3)
# and x(2R)=lambda^2+a1*lambda-a2-2x=0.
# We only need a rational expression for y on the cubic; solve the duplication x-coordinate equation together with curve equation.
Y=polygen(Rt.parent()) if False else None
print('Q4403_TATE_END')
