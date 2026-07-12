from sage.all import *

print('Q4403_TATE_BEGIN')
R.<b,c> = PolynomialRing(QQ)
K = R.fraction_field()
E = EllipticCurve(K,[1-c,-b,-b,0,0])
P = E(K(0),K(0))
print('E_AINVS',E.ainvs())
for n in range(1,10):
    Q=n*P
    if Q.is_zero():
        print('MULT',n,'O')
    else:
        print('MULT',n,'X',factor(Q[0]),'Y',factor(Q[1]))
Q=9*P
expr=2*Q[1]+(1-c)*Q[0]-b
num=R(expr.numerator())
den=R(expr.denominator())
print('NINE_2TORS_NUM_FACTOR',factor(num))
print('NINE_2TORS_DEN_FACTOR',factor(den))
# Also equality 8P=-10P equivalent 18P=O, and 9P nonzero cases.
# Extract the largest nontrivial factor by inspection/factor list.
print('FACTOR_LIST',num.factor())
print('DISC',factor(E.discriminant()))
print('Q4403_TATE_END')
