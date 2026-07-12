from sage.all import *

print('Q4412_LINEAR_INVERSE_BEGIN')

A.<r,s> = PolynomialRing(QQ)
K = A.fraction_field()
R.<w> = PolynomialRing(K)

# u=w+1, q=u*v.  The r-coordinate gives q=N/D.
N = (1-r)*w^2 - w - 1
D = 1 + r*w^2
B = w^4 + 2*w^3 + 3*w^2 + 5*w + 3   # u*(u^3-2u^2+3u+1)
E = N^2 + B*N*D + 2*(w+1)^3*D^2      # D^2*u^2*(optimized equation)
Q = (s-r)*w^2 + r*(s-1)*w + (r-1)    # consequence of the s-coordinate

quo, rem = E.quo_rem(Q)
print('REM_DEG', rem.degree())
for i in range(rem.degree()+1):
    ci = rem[i]
    print('REM_COEFF', i)
    print(' NUM ', factor(ci.numerator()))
    print(' DEN ', factor(ci.denominator()))

c0 = rem[0]
c1 = rem[1]
print('W_NUM', factor((-c0).numerator()*c1.denominator()))
print('W_DEN', factor(c0.denominator()*c1.numerator()))

# Verify the candidate w=-c0/c1 kills both equations modulo F18.
wcand = -c0/c1
print('WCAND', wcand)
print('Q_AT_W_NUM', factor(Q(wcand).numerator()))
print('E_AT_W_NUM', factor(E(wcand).numerator()))

print('Q4412_LINEAR_INVERSE_END')
