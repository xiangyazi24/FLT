from sage.all import *

print('Q4412_REDUCED_INVERSE_BEGIN')
A.<r,s> = PolynomialRing(QQ)
K = A.fraction_field()

F18 = (
    r^4*s^3 - 6*r^4*s^2 + 9*r^4*s - r^4
  + r^3*s^5 - 7*r^3*s^4 + 20*r^3*s^3 - 19*r^3*s^2 - 8*r^3*s + r^3
  + r^2*s^4 - 11*r^2*s^3 + 28*r^2*s^2
  + r*s^4 - 5*r*s^3 - 8*r*s^2
  + s^4 + s^3 + s^2)

D0 = r^2*(r-1)^7
W = (
    (-r^8 - 3*r^6 + 5*r^5 - 3*r^4 + r^3)*s^4
  + (5*r^8 - 2*r^7 + 22*r^6 - 39*r^5 + 23*r^4 - 8*r^3 + 3*r^2 - 2*r + 1)*s^3
  + (-r^9 - 11*r^8 + 16*r^7 - 65*r^6 + 127*r^5 - 98*r^4 + 27*r^3 + 9*r^2 - 8*r + 1)*s^2
  + (4*r^9 + r^8 - 14*r^7 + 72*r^6 - 173*r^5 + 208*r^4 - 143*r^3 + 56*r^2 - 11*r + 1)*s
  + r^2*(r-1)*(-2*r^6 + 9*r^5 - 24*r^4 + 29*r^3 - 18*r^2 + 5*r))

w = K(W)/K(D0)
N = (1-r)*w^2 - w - 1
D = 1 + r*w^2
B = w^4 + 2*w^3 + 3*w^2 + 5*w + 3
Q = (s-r)*w^2 + r*(s-1)*w + (r-1)
E = N^2 + B*N*D + 2*(w+1)^3*D^2

Qnum=A(Q.numerator())
Enum=A(E.numerator())
qquo,qrem=Qnum.quo_rem(F18)
equo,erem=Enum.quo_rem(F18)
print('Q_REM',qrem)
print('Q_QUO_FACTOR',factor(qquo))
print('E_REM',erem)
print('E_QUO_FACTOR',factor(equo))
print('Q_NUM_TOTAL_DEG',Qnum.total_degree())
print('E_NUM_TOTAL_DEG',Enum.total_degree())
print('E_QUO_TOTAL_DEG',equo.total_degree())
print('Q4412_REDUCED_INVERSE_END')
