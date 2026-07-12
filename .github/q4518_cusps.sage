from sage.all import *
R.<T>=PolynomialRing(QQ)
L.<a>=NumberField(T^3-3*T-1)

def h(u): return u^3-2*u^2+3*u+1
def opt(X,Y):
    u=-X
    v=(Y-h(u))/2
    return u,v

def classify(X,Y):
    u,v=opt(X,Y)
    Nr=u^2-u*v-3*u+1
    Dr=(u-1)^2*(u*v+1)
    Ns=u^2-2*u-v
    Ds=u^2-u*v-3*u-v^2-2*v
    print('POINT',X,Y,'OPT',u,v,'Dr',Dr,'Ds',Ds)
    if Dr==0: return 'CUSP_Dr0'
    if Ds==0: return 'CUSP_Ds0'
    r=Nr/Dr; s=Ns/Ds; b=r*s*(r-1); c=s*(r-1)
    Delta=b^3*(16*b^2-8*b*c^2-20*b*c+b+c*(c-1)^3)
    print('RAW',r,s,'B',b,'C',c,'DELTA',Delta)
    return 'CUSP_DELTA0' if Delta==0 else 'NONCUSP'

points=[
 (-a-1,3*a^2+3*a),(-a-1,-3*a^2-3*a),
 (a^2-3,-6*a^2+3*a+18),(a^2-3,6*a^2-3*a-18),
 (-a^2+a+1,-3*a^2+6*a),(-a^2+a+1,3*a^2-6*a),
 (0,1),(0,-1),(-1,1),(-1,-1)
]
for P in points: print('CLASS',P,classify(*P))
