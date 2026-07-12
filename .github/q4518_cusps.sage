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
    if Dr==0: return ('CUSP_Dr0',u,v,Dr,Ds,None)
    if Ds==0: return ('CUSP_Ds0',u,v,Dr,Ds,None)
    r=Nr/Dr; s=Ns/Ds; b=r*s*(r-1); c=s*(r-1)
    Delta=b^3*(16*b^2-8*b*c^2-20*b*c+b+c*(c-1)^3)
    return ('CUSP_DELTA0' if Delta==0 else 'NONCUSP',u,v,Dr,Ds,Delta)

points=[
 ('A+',-a-1,3*a^2+3*a),('A-',-a-1,-3*a^2-3*a),
 ('B+',a^2-3,-6*a^2+3*a+18),('B-',a^2-3,6*a^2-3*a-18),
 ('C+',-a^2+a+1,-3*a^2+6*a),('C-',-a^2+a+1,3*a^2-6*a),
 ('Q01',0,1),('Q0m1',0,-1),('Qm11',-1,1),('Qm1m1',-1,-1)
]
for name,X,Y in points: print('CLASS',name,X,Y,classify(X,Y))

rm=-a^2-a
f=lambda x:x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1
vals=[
 ('O_y2',f(rm)),
 ('u1',-8*a^2+8*a+13),
 ('u3',4*a^2-6*a-3),
 ('u4',-12*a^2+20*a+5),
 ('u5',16*a^2-20*a-19),
 ('u6',2*a^2-7),
 ('u7',(-4*a^2+8*a-1)/3),
 ('u9',-10*a^2+14*a+9),
]
for name,w in vals:
    n=L(w).norm()
    print('NONSQUARE',name,'VALUE',w,'NORM',n,'NORM_IS_SQUARE_Q',QQ(n).is_square())
