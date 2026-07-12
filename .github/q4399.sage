from sage.all import *

print('Q4399_CONCISE_BEGIN')
R0.<Avar> = PolynomialRing(QQ)
L.<a> = NumberField(Avar^3 - 3*Avar - 1)
Rz.<z> = PolynomialRing(L)
A0 = -a - 1
q0 = a^2 - 1
rp = a^2 - a - 2
rm = -a^2 - a
x_of_z = (z*rm-rp)/(z-1)
def fpoly(x): return x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1
Fz = Rz((z-1)^6*fpoly(x_of_z))
c0,c2,c3 = Fz[0],Fz[4],Fz[6]
Eplus = EllipticCurve(L,[0,c2,0,0,c0*c3^2])
Eminus = EllipticCurve(L,[0,0,0,c2*c0,c3*c0^2])
E0Q = EllipticCurve(QQ,[1,-1,1,-5,5])
EhatQ = E0Q.isogenies_prime_degree(3)[0].codomain()
E0=E0Q.change_ring(L); Ehat=EhatQ.change_ring(L)
isoP=Eplus.isomorphism_to(E0); isoM=Eminus.isomorphism_to(Ehat)
print('BASIC=',A0,q0,rp,rm)
print('C=',c0,c2,c3)
print('EPLUS=',Eplus.a_invariants())
print('EMINUS=',Eminus.a_invariants())
print('E0=',E0.a_invariants(),'LABEL',E0Q.label())
print('EHAT=',Ehat.a_invariants(),'LABEL',EhatQ.label())
print('PLUS_TUPLE=',isoP.tuple())
print('PLUS_MAP=',isoP.rational_maps())
print('PLUS_INV=',(~isoP).rational_maps())
print('MINUS_TUPLE=',isoM.tuple())
print('MINUS_MAP=',isoM.rational_maps())
print('MINUS_INV=',(~isoM).rational_maps())
print('ISOGENY_E0_TO_EHAT=',E0Q.isogenies_prime_degree(3)[0].rational_maps())

# Coefficients in the direct maps from (u,v) raw quotient coordinates.
Pmap=isoP.rational_maps(); Mmap=isoM.rational_maps()
# substitute X=c3*u,Y=c3*v and X=c0/u,Y=c0*w/u^2 respectively
Ruv.<u,v> = PolynomialRing(L,2)
Xp=c3*u; Yp=c3*v
xm = c0/u; ym = c0*v/u^2
print('PLUS_DIRECT_UV_X=',Pmap[0](Xp,Yp))
print('PLUS_DIRECT_UV_Y=',Pmap[1](Xp,Yp))
print('MINUS_DIRECT_UW_X=',Mmap[0](xm,ym))
print('MINUS_DIRECT_UW_Y=',Mmap[1](xm,ym))

# Direct formulas from C coordinates, kept factored through z.
Rxy.<x,y> = PolynomialRing(L,2)
zxy=(x-rp)/(x-rm)
up=zxy^2
vp=(zxy-1)^3*y
wm=zxy*vp
Xplus=c3*up; Yplus=c3*vp
Xminus=c0/up; Yminus=c0*wm/up^2
print('QPLUS_X_E0=',factor(Pmap[0](Xplus,Yplus)))
print('QPLUS_Y_E0=',factor(Pmap[1](Xplus,Yplus)))
print('QMINUS_X_EHAT=',factor(Mmap[0](Xminus,Yminus)))
print('QMINUS_Y_EHAT=',factor(Mmap[1](Xminus,Yminus)))

# Basic identity checks.
sx=(A0*x_of_z-a)/(x_of_z-A0)
print('SIGMA_Z=',Rz((sx-rp)/(sx-rm)))
print('SIGMA_MU=',q0^3/(x_of_z-A0)^3)
print('Q0_CUBE=',q0^3)
print('REL_FIXED=',q0^2-(A0^2-a))
print('Q4399_CONCISE_END')
