from sage.all import *
R.<t> = PolynomialRing(QQ)
L.<a> = NumberField(t^3-3*t-1)
c6=1800*a^2+3384*a+960
c4=420*a^2+780*a+240
c0=84*a^2-132*a-48
Ep=EllipticCurve(L,[0,c4,0,0,c0*c6^2])
Em=EllipticCurve(L,[0,0,0,c4*c0,c6*c0^2])
E0=EllipticCurve(L,[1,-1,1,-5,5])
Eh=EllipticCurve(L,[1,-1,1,25,1])
isoP=Ep.isomorphism_to(E0)
isoM=Em.isomorphism_to(Eh)
print('PLUS_TUPLE',isoP.tuple())
print('PLUS_MAPS',isoP.rational_maps())
print('MINUS_TUPLE',isoM.tuple())
print('MINUS_MAPS',isoM.rational_maps())
phi=E0.isogeny(E0(1,0),codomain=Eh)
print('PHI_MAPS',phi.rational_maps())
print('DUAL_MAPS',phi.dual().rational_maps())
