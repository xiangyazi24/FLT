from sage.all import *

print('Q4412_TATE_FACTOR_BEGIN')
R.<b,c> = PolynomialRing(QQ)
K = R.fraction_field()
E = EllipticCurve(K,[1-c,-b,-b,0,0])
P = E(K(0),K(0))
Q = 9*P
expr = 2*Q[1] + (1-c)*Q[0] - b
num = R(expr.numerator())
fac6 = c^2-b+c
G18 = num//fac6
print('DIV_REM',num.quo_rem(fac6)[1])
print('G18',G18)

A.<r,s> = PolynomialRing(QQ)
F18 = (
    r^4*s^3 - 6*r^4*s^2 + 9*r^4*s - r^4
  + r^3*s^5 - 7*r^3*s^4 + 20*r^3*s^3 - 19*r^3*s^2 - 8*r^3*s + r^3
  + r^2*s^4 - 11*r^2*s^3 + 28*r^2*s^2
  + r*s^4 - 5*r*s^3 - 8*r*s^2
  + s^4 + s^3 + s^2)
subs = F18(R(b)/R(c),R(c)^2/(R(b)-R(c)))
T18 = R((c^4*(b-c)^5*subs).numerator()/(c^4*(b-c)^5*subs).denominator())
print('T18',T18)
print('G_EQ_T',G18==T18)
print('G_EQ_NEG_T',G18==-T18)
print('DISC',factor(E.discriminant().numerator()))
print('Q4412_TATE_FACTOR_END')
