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

for n in range(1,10):
    Q=n*P
    if Q.is_zero():
        print('MULT',n,'O')
    else:
        print('MULT',n,'XNUM',ff(Q[0].numerator()),'XDEN',ff(Q[0].denominator()))
        print('MULT',n,'YNUM',ff(Q[1].numerator()),'YDEN',ff(Q[1].denominator()))
Q=9*P
expr=2*Q[1]+(1-c)*Q[0]-b
num=R(expr.numerator())
den=R(expr.denominator())
print('NINE_2TORS_NUM_FACTOR',ff(num))
print('NINE_2TORS_DEN_FACTOR',ff(den))
print('FACTOR_LIST',num.factor())
print('DISC',ff(E.discriminant().numerator()),'/',ff(E.discriminant().denominator()))
print('Q4403_TATE_END')
