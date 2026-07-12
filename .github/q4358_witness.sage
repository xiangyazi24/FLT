from sage.all import *


def setup(p,prec=100):
    Q=Qp(p,prec=prec,type='capped-rel')
    R.<X>=PolynomialRing(Q)
    if p==2:
        K.<z>=Q.extension(X^2+X+1)
        pi=K(2)
    else:
        K.<pi>=Q.extension(X^2-3*X+3)
        z=1-pi
    s=1+2*z
    g1=(3+2*s)/7; g2=s; g3=(3-2*s)/7; g4=-s
    c=-(1+3*z)*(1+3*z^2)^2
    def rhs(m): return c*(m-g1)*(m-g2)*(m-g3)^2*(m-g4)^2
    m0=K(1)
    h10=(m0-g1)/(m0-g4); h20=(m0-g2)/(m0-g4)
    return K,z,pi,(g1,g2,g3,g4),rhs,h10,h20

def cert(p,ms):
    K,z,pi,gg,rhs,h10,h20=setup(p)
    g1,g2,g3,g4=gg
    print('PLACE',p)
    for j,m in enumerate(ms):
        rr=rhs(m); val=rr.valuation(); unit=rr/pi^val
        root=rr.nth_root(3)
        print('WITNESS',j+1,'M=',m)
        print('  RHS_VAL=',val)
        if p==2:
            print('  UNIT_MINUS_1_VAL=',(unit-1).valuation())
            print('  UNIT_MOD_2=',unit.add_bigoh(1))
            print('  ROOT_MOD_2^8=',root.add_bigoh(8))
        else:
            un=unit if (unit-1).valuation()>0 else -unit
            print('  NORMALIZED_SIGN=',1 if un==unit else -1)
            print('  UNIT_MINUS_1_VAL=',(un-1).valuation())
            print('  UNIT_MOD_PI^6=',un.add_bigoh(6))
            print('  ROOT_MOD_PI^10=',root.add_bigoh(10))
        aa=((m-g1)/(m-g4))/h10
        bb=((m-g2)/(m-g4))/h20
        print('  A_VAL=',aa.valuation(),' B_VAL=',bb.valuation())
        print('  ROOT_RESIDUAL_VAL=',(root^3-rr).valuation())

K2,z2,pi2,*_=setup(2)
cert(2,[K2(7),K2(19)+K2(60)*z2])
K3,z3,pi3,*_=setup(3)
cert(3,[pi3+2*pi3^4,
        2*pi3+pi3^4+2*pi3^5+2*pi3^6,
        2*pi3+2*pi3^2,
        1+pi3^2])
