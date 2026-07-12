from sage.all import *
R.<t> = PolynomialRing(QQ)
L.<a> = NumberField(t^3-3*t-1)
A=-a-1
q=a^2-1
rp=a^2-a-2
rm=-a^2-a
c6=1800*a^2+3384*a+960
c4=420*a^2+780*a+240
c0=84*a^2-132*a-48
print('FIELD_REL',a^3-3*a-1)
print('A_Q_RP_RM',A,q,rp,rm)
print('C6_C4_C0',c6,c4,c0)
Ep=EllipticCurve(L,[0,c4,0,0,c0*c6^2])
Em=EllipticCurve(L,[0,0,0,c4*c0,c6*c0^2])
E0=EllipticCurve(L,[1,-1,1,-5,5])
Eh=EllipticCurve(L,[1,-1,1,25,1])
for name,E in [('EPLUS',Ep),('EMINUS',Em),('E0',E0),('EHAT',Eh)]:
 print(name,'AINVS',E.ainvs(),'DISC',E.discriminant(),'J',E.j_invariant())
for srcname,src in [('EPLUS',Ep),('EMINUS',Em)]:
 for dstname,dst in [('E0',E0),('EHAT',Eh)]:
  print('ISO_TEST',srcname,dstname,src.is_isomorphic(dst))
  if src.is_isomorphic(dst):
   iso=src.isomorphism_to(dst)
   print('ISO',srcname,'TO',dstname,iso)
   try: print('ISO_TUPLE',iso.tuple())
   except Exception as e: print('ISO_TUPLE_ERR',e)
   try: print('ISO_MAPS',iso.rational_maps())
   except Exception as e: print('ISO_MAPS_ERR',e)
# also print a degree-3 isogeny between the pinned models
phi=E0.isogeny(E0(1,0),codomain=Eh)
print('PHI_MAPS',phi.rational_maps())
print('DUAL_MAPS',phi.dual().rational_maps())
