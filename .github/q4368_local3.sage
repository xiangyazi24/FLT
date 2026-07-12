from sage.all import *
from itertools import product
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
# Special Kummer class alpha(T)=1/16.
sp=K(1)/16
print('SPECIAL_CLASS_EXPECT_2SQ',cube_root(sp/(K(2)^2)) is not None)
print('TWO_NONCUBE',cube_root(K(2)) is None)
# Fingerprint all 81 combinations by whether quotient by one of basis products is a cube.
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
# The local alpha-image has order 3 from the local isogeny ratio; T supplies class 2^2.
# Thus it is exactly the span of class(2). Print all global exponent vectors satisfying this.
surv=[]
for ex in product(range(3),repeat=4):
    # order is pi,e1,e2,2
    if ex[0]==0 and ex[1]==0 and ex[2]==0:
        surv.append(ex)
print('LOCAL_IMAGE_SPAN2_GLOBAL_SURVIVORS',surv)
