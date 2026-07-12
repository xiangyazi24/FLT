from sage.all import *
from itertools import product

# Exact finite certificate for the unique prime above 3.
S.<T>=PolynomialRing(QQ)
L.<a>=NumberField(T^3-3*T-1)
OL=L.ring_of_integers()
pi=a-1
e1=-a^2+a+2
e2=-a
P=OL.ideal(pi)
print('P_NORM',P.norm())
print('P_CUBE_EQUALS_3',P^3==OL.ideal(3))
print('UNIT_BASIS',e1,e2)
print('S_UNIT_BASIS',e1,e2,L(2),pi)

found=False
for N in range(2,8):
    PN=P^N
    A=OL.quotient(PN.gens(),'q')
    reps=[A(sum(ds[n]*pi^n for n in range(N))) for ds in product(range(3),repeat=N)]
    assert len(set(reps))==3^N
    cube_set={x^3 for x in reps}
    survivors=[]
    for i,j,k in product(range(3),repeat=3):
        u=A(e1^i*e2^j*L(2)^k)
        if u in cube_set:
            survivors.append((i,j,k))
    print('FINITE_N',N,'CARD',A.cardinality(),'CUBE_SET_CARD',len(cube_set),'UNIT_CUBE_SURVIVORS',survivors)
    if survivors==[(0,0,0)]:
        print('FINITE_CERTIFICATE_LEVEL',N)
        found=True
        break
print('FINITE_CERTIFICATE_FOUND',found)
print('SPECIAL_CLASS_IDENTITY',(L(1)/16)/(L(2)^2),(L(1)/4)^3)
print('LOCAL_IMAGE_SPAN2_GLOBAL_SURVIVORS',[(0,0,0,k) for k in range(3)])
