from sage.all import *
from itertools import product

# Exact global field and the unique prime over 3.
S.<T>=PolynomialRing(QQ)
L.<a0>=NumberField(T^3-3*T-1)
OL=L.ring_of_integers()
pi0=a0-1
e10=-a0^2+a0+2
e20=-a0
P=OL.ideal(pi0)
print('EXACT_P_NORM',P.norm(),'P3_EQUALS_3',P^3==OL.ideal(3))
for N in range(2,11):
    A=OL.quotient(P^N,'q')
    cube_set={x^3 for x in A}
    survivors=[]
    for i,j,k in product(range(3),repeat=3):
        u=A(e10^i*e20^j*L(2)^k)
        if u in cube_set:
            survivors.append((i,j,k))
    print('FINITE_N',N,'CARD',A.cardinality(),'UNIT_CUBE_SURVIVORS',survivors)
    if survivors==[(0,0,0)]:
        print('FINITE_CERTIFICATE_LEVEL',N)
        break

# Independent q-adic cross-check and explicit local class fingerprints.
Q=Qp(3,prec=120,type='capped-rel')
R.<X>=PolynomialRing(Q)
K.<pi>=Q.extension(X^3+3*X^2-3)
a=pi+1
e1=-a^2+a+2
e2=-a
B=[pi,e1,e2,K(2)]
print('REL',pi^3+3*pi^2-3)
print('BASIS',B)

def cube_root(q):
    try:
        r=q.nth_root(3)
        if (r^3-q).valuation() >= 80:
            return r
    except (ValueError,ArithmeticError,NotImplementedError):
        return None
    return None

cubes=[]
for ex in product(range(3),repeat=4):
    q=prod(B[i]^ex[i] for i in range(4))
    r=cube_root(q)
    if r is not None:
        cubes.append((ex,r))
print('CUBE_COMBINATIONS',[(e,str(r.add_bigoh(10))) for e,r in cubes])
print('BASIS_INDEPENDENT',len(cubes)==1 and cubes[0][0]==(0,0,0,0))
for i,b in enumerate(B):
    print('B',i,'VAL',b.valuation(),'APPROX',b.add_bigoh(10))
sp=K(1)/16
print('SPECIAL_CLASS_EXPECT_2SQ',cube_root(sp/(K(2)^2)) is not None)
print('TWO_NONCUBE',cube_root(K(2)) is None)

def cls(q):
    for ex in product(range(3),repeat=4):
        b=prod(B[i]^ex[i] for i in range(4))
        if cube_root(q/b) is not None:
            return ex
    raise RuntimeError('class not found')
print('CLASS_PI',cls(pi))
print('CLASS_E1',cls(e1))
print('CLASS_E2',cls(e2))
print('CLASS_2',cls(K(2)))
print('CLASS_SPECIAL',cls(sp))
print('LOCAL_IMAGE_SPAN2_GLOBAL_SURVIVORS',[(0,0,0,k) for k in range(3)])
