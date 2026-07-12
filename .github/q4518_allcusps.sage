from sage.all import *
R.<T>=PolynomialRing(QQ)
L.<a>=NumberField(T^3-3*T-1)
E=EllipticCurve(L,[1,-1,1,-5,5])
T3=E(1,0)
G=sorted([P for P in E.torsion_points() if P.order()==21 and 7*P==T3],key=str)[0]
A=-a-1; q=a^2-1; rp=a^2-a-2; rm=-a^2-a
ku=4*a^2+8*a+3; kv=a^2+a-1; lu=8*a^2+16*a+6
f=lambda x:x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1

def h(u): return u^3-2*u^2+3*u+1

def cusp_status(x,y):
    u=-x; v=(y-h(u))/2
    Nr=u^2-u*v-3*u+1
    Dr=(u-1)^2*(u*v+1)
    Ns=u^2-2*u-v
    Ds=u^2-u*v-3*u-v^2-2*v
    if Dr==0: return 'CUSP_Dr0'
    if Ds==0: return 'CUSP_Ds0'
    r=Nr/Dr; s=Ns/Ds; b=r*s*(r-1); c=s*(r-1)
    Delta=b^3*(16*b^2-8*b*c^2-20*b*c+b+c*(c-1)^3)
    return 'CUSP_DELTA0' if Delta==0 else 'NONCUSP'

cusp_count=0; noncusp_count=0
for k in range(21):
    P=k*G
    if P.is_zero():
        w=f(rm)
        S.<Z>=PolynomialRing(L)
        K.<eta>=L.extension(Z^2-w)
        for sg,y in [('+',eta),('-',-eta)]:
            st=cusp_status(K(rm),y)
            print('CLASS42',k,sg,st)
            cusp_count += (st!='NONCUSP'); noncusp_count += (st=='NONCUSP')
        continue
    X0,Y0=P[0],P[1]
    u=(2*X0-3)/ku; v=(8*Y0+lu*u+10)/kv
    if u==1:
        # finite z=-1 and the infinity z=1. Infinity is a cusp.
        x=A; y=-v/8
        st=cusp_status(x,y)
        print('CLASS42',k,'finite',st)
        print('CLASS42',k,'infinity','CUSP_INFINITY')
        cusp_count += 1+(st!='NONCUSP'); noncusp_count += (st=='NONCUSP')
    elif u.is_square():
        z0=L(u.sqrt())
        for sg,z in [('+',z0),('-',-z0)]:
            x=(z*rm-rp)/(z-1); y=v/(z-1)^3
            st=cusp_status(x,y)
            print('CLASS42',k,sg,st)
            cusp_count += (st!='NONCUSP'); noncusp_count += (st=='NONCUSP')
    else:
        S.<Z>=PolynomialRing(L)
        K.<z>=L.extension(Z^2-u)
        for sg,zz in [('+',z),('-',-z)]:
            x=(zz-K(rp))/(zz-1)*K(rm) if False else (zz*K(rm)-K(rp))/(zz-1)
            y=K(v)/(zz-1)^3
            st=cusp_status(x,y)
            print('CLASS42',k,sg,st)
            cusp_count += (st!='NONCUSP'); noncusp_count += (st=='NONCUSP')
print('TOTAL_CUSPS_IN_42',cusp_count)
print('TOTAL_NONCUSPS_IN_42',noncusp_count)
assert cusp_count+noncusp_count==42
