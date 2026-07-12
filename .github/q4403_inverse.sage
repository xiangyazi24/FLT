from sage.all import *

print('Q4412_LINEAR_INVERSE_BEGIN')

A.<r,s> = PolynomialRing(QQ)
Krs = A.fraction_field()
R.<w> = PolynomialRing(Krs)

N = (1-r)*w^2 - w - 1
D = 1 + r*w^2
B = w^4 + 2*w^3 + 3*w^2 + 5*w + 3
E = N^2 + B*N*D + 2*(w+1)^3*D^2
Q = (s-r)*w^2 + r*(s-1)*w + (r-1)

quo, rem = E.quo_rem(Q)
c0 = rem[0]
c1 = rem[1]
wcand = -c0/c1
Wnum = A(wcand.numerator())
Wden = A(wcand.denominator())
print('RAW_W_NUM', factor(Wnum))
print('RAW_W_DEN', factor(Wden))
print('Q_CERT', factor(Q(wcand).numerator()))

# Reduce the same ratio in the function field QQ(r)[s]/(F18).
Fr.<rr> = FunctionField(QQ)
Ps.<S> = PolynomialRing(Fr)
F18 = (
    rr^4*S^3 - 6*rr^4*S^2 + 9*rr^4*S - rr^4
  + rr^3*S^5 - 7*rr^3*S^4 + 20*rr^3*S^3 - 19*rr^3*S^2 - 8*rr^3*S + rr^3
  + rr^2*S^4 - 11*rr^2*S^3 + 28*rr^2*S^2
  + rr*S^4 - 5*rr*S^3 - 8*rr*S^2
  + S^4 + S^3 + S^2)
KF.<ss> = Fr.extension(F18)

def toKF(poly):
    out = KF(0)
    for (i,j), coeff in poly.dict().items():
        out += KF(coeff) * KF(rr)^i * ss^j
    return out

wred = toKF(Wnum) / toKF(Wden)
print('REDUCED_W', wred)
print('REDUCED_W_VECTOR', list(wred))

print('Q4412_LINEAR_INVERSE_END')
