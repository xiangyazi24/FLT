R.<T> = PolynomialRing(QQ)
E = EllipticCurve(QQ,[0,0,0,-432,8208])
print('BEGIN_Q4570')
print('E',E.a_invariants(),E.discriminant(),E.j_invariant(),E.conductor())
try: print('LABEL',E.cremona_label())
except Exception as ex: print('LABEL_ERR',repr(ex))
Emin = E.global_minimal_model()
print('EMIN',Emin.a_invariants(),Emin.discriminant(),Emin.conductor())
iso = E.isomorphism_to(Emin)
print('ISO_URST',iso.tuple())
print('ISO_MAPS',iso.rational_maps())
inv=iso.inverse()
print('INV_URST',inv.tuple())
print('INV_MAPS',inv.rational_maps())
try:
    print('TORSION_GROUP',Emin.torsion_subgroup())
    print('TORSION_MIN',Emin.torsion_points())
    print('TORSION_SHORT',E.torsion_points())
except Exception as ex: print('TORSION_ERR',repr(ex))
for p in [2,3,5,7,13]:
    Ep=Emin.change_ring(GF(p))
    print('RED',p,Ep.cardinality(),Ep.abelian_group(),Ep.points())
Ps=[]
for x0 in [-12,24]:
  for y0 in [-108,108]:
    try:
      P=E(x0,y0); Ps.append(P)
      print('POINT',P,'ORDER',P.order(),'MIN',iso(P))
    except Exception: pass
try:
  tors=E.torsion_points()
  for P in Ps:
    print('HALVES',P,[Q for Q in tors if 2*Q==P])
except Exception as ex: print('HALF_ERR',repr(ex))
S.<aa,b,c,z,x,y> = PolynomialRing(QQ)
D=c-2*b
const=aa^2+4*D*b+8*b^2
lin=2*aa*D-8*D*b-14*b^2
quad=D^2+2*aa*b+8*D*b+12*b^2
tr=3*aa+4*D+8*b
s2=(tr^2-3*x)/2
print('W2',const.factor(),lin.factor(),quad.factor())
print('TRACE',tr.factor())
print('S2_RAW',s2.factor())
rel1=x-(aa^2+4*b*c+24*z^2)
rel2=9*z^2-(aa*c-2*aa*b-4*b*c+b^2)
rel3=c^2+4*b*c+2*aa*b
I=S.ideal([rel1,rel2,rel3])
try:
  print('S2_REDUCED',I.reduce(s2))
  print('XHALF_REDUCED',I.reduce(x+s2))
except Exception as ex: print('GB_ERR',repr(ex))
U.<A,Dd,Bb> = PolynomialRing(QQ)
M=matrix(U,3,3)
M[:,0]=vector([A,Dd,Bb])
M[:,1]=vector([2*Bb,A-4*Bb,Dd+4*Bb])
M[:,2]=vector([2*Dd+8*Bb,-4*Dd-14*Bb,A+4*Dd+12*Bb])
print('NORM_W',M.det().factor())
print('END_Q4570')
