from sage.all import *

# Exact computation of the diamond-<3> orbit invariants on X_1(19).
# The first power trace is expected to be 3.  The canonical replacement
# coordinates are the second and third elementary symmetric functions of
# the nine orbit values of alpha.

Qct.<c> = FunctionField(QQ)
Rb.<T> = PolynomialRing(Qct)

# Raw order-19 Tate polynomial, monic of degree 15 in b.
F19 = (
 T^15 - 10*T^14*c - 20*T^13*c^3 + 45*T^13*c^2
 + 69*T^12*c^5 + 195*T^12*c^4 - 120*T^12*c^3
 - 121*T^11*c^7 - 588*T^11*c^6 - 861*T^11*c^5 + 210*T^11*c^4
 + 105*T^10*c^9 + 870*T^10*c^8 + 2235*T^10*c^7 + 2275*T^10*c^6 - 252*T^10*c^5
 - 48*T^9*c^11 - 585*T^9*c^10 - 2720*T^9*c^9 - 4995*T^9*c^8 - 4005*T^9*c^7 + 210*T^9*c^6
 + 11*T^8*c^13 + 183*T^8*c^12 + 1320*T^8*c^11 + 4851*T^8*c^10 + 7290*T^8*c^9 + 4950*T^8*c^8 - 120*T^8*c^7
 - T^7*c^15 - 21*T^7*c^14 - 231*T^7*c^13 - 1531*T^7*c^12 - 5466*T^7*c^11 - 7308*T^7*c^10 - 4410*T^7*c^9 + 45*T^7*c^8
 + 120*T^6*c^14 + 990*T^6*c^13 + 4117*T^6*c^12 + 5166*T^6*c^11 + 2862*T^6*c^10 - 10*T^6*c^9
 - 34*T^5*c^16 - 165*T^5*c^15 - 465*T^5*c^14 - 2190*T^5*c^13 - 2610*T^5*c^12 - 1350*T^5*c^11 + T^5*c^10
 + 25*T^4*c^18 + 150*T^4*c^17 + 363*T^4*c^16 + 320*T^4*c^15 + 885*T^4*c^14 + 945*T^4*c^13 + 455*T^4*c^12
 - 6*T^3*c^20 - 45*T^3*c^19 - 161*T^3*c^18 - 333*T^3*c^17 - 225*T^3*c^16 - 281*T^3*c^15 - 240*T^3*c^14 - 105*T^3*c^13
 + T^2*c^22 + 6*T^2*c^21 + 21*T^2*c^20 + 56*T^2*c^19 + 126*T^2*c^18 + 81*T^2*c^17 + 61*T^2*c^16 + 39*T^2*c^15 + 15*T^2*c^14
 - 15*T*c^19 - 10*T*c^18 - 6*T*c^17 - 3*T*c^16 - T*c^15
 - c^21
)

L.<b> = Qct.extension(F19)
cL = L(c)


def F5(x,y): return x-y
def F6(x,y): return x-y-y^2
def F7(x,y): return x^2-x*y-y^3
def F8(x,y): return 2*x^2-3*x*y-x*y^2+y^2
def F9(x,y): return x^3-3*x^2*y+x*y^3+3*x*y^2-y^5-y^4-y^3
def KK(x,y):
    return (3*x^4-x^3*y^2-9*x^3*y+10*x^2*y^2
            +x*y^4-5*x*y^3+y^6+y^4)

def sigma(x,y):
    den = F6(x,y)
    return F9(x,y)^3/den^8, -y*KK(x,y)/den^4

def alpha(x,y): return F7(x,y)/F8(x,y)
def beta(x,y): return F5(x,y)*F7(x,y)/F9(x,y)

xx, yy = b, cL
alphas = []
betas = []
for i in range(9):
    print('orbit', i, flush=True)
    alphas.append(alpha(xx,yy))
    betas.append(beta(xx,yy))
    xx, yy = sigma(xx,yy)

print('ORBIT_CLOSE_B', xx == b)
print('ORBIT_CLOSE_C', yy == cL)

p1 = sum(alphas)
p2 = sum(a^2 for a in alphas)
p3 = sum(a^3 for a in alphas)
vbeta = sum(betabs for betabs in betas)

e2 = (p1^2-p2)/2
e3 = (p1^3-3*p1*p2+2*p3)/6

print('P1_IS_3', p1 == 3)
print('VBETA_IS_CONSTANT', vbeta in Qct)
print('E2E3_19A1', e3^2+e3 == e2^3+e2^2-9*e2-15)

# Find the exact constant-coefficient Weierstrass relation as a safety check.
mons = [e3^2, e2*e3, e3, e2^3, e2^2, e2, L(1)]
rows = []
for cv in list(range(1,15)) + list(range(20,30)):
    try:
        for j in range(15):
            row=[]
            for z in mons:
                ll=z.list()
                q=ll[j] if j < len(ll) else Qct(0)
                row.append(QQ(q(cv)))
            rows.append(row)
    except (ZeroDivisionError, ValueError):
        pass
M=Matrix(QQ,rows)
ker=M.right_kernel().basis()
print('REL_NULLITY',len(ker))
for r in ker: print('REL_VECTOR',list(r))

# Convert an L-element to a primitive numerator in QQ[B,C] and a monic
# denominator in QQ[C].
Qc.<C> = PolynomialRing(QQ)
QBC.<B,C2> = PolynomialRing(QQ,2)

def to_Qc(poly):
    return Qc(list(poly))

def extract(z, name):
    coeffs=z.list()
    D=Qc.one()
    for q in coeffs:
        D=lcm(D,to_Qc(q.denominator()).monic())
    # D is monic; absorb all coefficient denominators into the numerator.
    P=QBC.zero()
    for i,q in enumerate(coeffs):
        num=to_Qc(q.numerator())
        den=to_Qc(q.denominator())
        fac=D//den.monic()
        # Correct for the leading scalar removed by monic().
        fac *= den.leading_coefficient()
        pc=num*fac
        P += sum(QQ(pc[k])*B^i*C2^k for k in range(pc.degree()+1))
    # Primitive rational normalization.
    denoms=[QQ(t[1]).denominator() for t in P.dict().items()]
    mult=lcm(denoms) if denoms else 1
    P=QBC(mult*P)
    cont=gcd([ZZ(v) for v in P.dict().values()]) if P else 1
    if cont: P=QBC(P/cont)
    D=Qc(mult*D/cont)
    if D.leading_coefficient()!=1:
        lc=D.leading_coefficient(); D/=lc; P/=lc
    print(name+'_DEN_FACTOR',factor(D))
    print(name+'_DEN_DEG',D.degree())
    print(name+'_NUM_DEG_B',P.degree(B))
    print(name+'_NUM_DEG_C',P.degree(C2))
    print(name+'_NUM_TERMS',len(P.dict()))
    open('scratch/x1_19_'+name+'_numerator.txt','w').write(str(P)+'\n')
    open('scratch/x1_19_'+name+'_denominator.txt','w').write(str(D)+'\n')
    return P,D

A19,DA=extract(e2,'A19')
B19,DB=extract(e3,'B19')
VNUM,VDEN=extract(vbeta,'Vbeta19')

# Denominator-cleared certificate for the actual denominator exponents.
# Work directly with DA,DB to avoid assuming the expected 2:3 ratio.
def embed_C(poly):
    return sum(QQ(poly[k])*C2^k for k in range(poly.degree()+1))
da=embed_C(DA); db=embed_C(DB)
C19 = B19^2*da^3 + B19*db*da^3 - A19^3*db^2 - A19^2*da*db^2 + 9*A19*da^2*db^2 + 15*da^3*db^2
F19BC = QBC(F19(T=B,c=C2))
q19,r19 = C19.quo_rem(F19BC)
print('CERT_REM_ZERO',r19==0)
print('CERT_DEG_B',C19.degree(B),'CERT_DEG_C',C19.degree(C2),'CERT_TERMS',len(C19.dict()))
print('QUOT_DEG_B',q19.degree(B),'QUOT_DEG_C',q19.degree(C2),'QUOT_TERMS',len(q19.dict()))
open('scratch/x1_19_C19.txt','w').write(str(C19)+'\n')
open('scratch/x1_19_C19_quotient.txt','w').write(str(q19)+'\n')
print('DONE',flush=True)
