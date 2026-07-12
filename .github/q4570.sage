R.<T> = PolynomialRing(QQ)
print('BEGIN_Q4570')
E = EllipticCurve(QQ,[0,0,0,-432,8208])
print('E_BASIC',E.a_invariants(),E.discriminant(),E.j_invariant())
try:
    Emin=E.global_minimal_model()
    print('EMIN',Emin.a_invariants(),Emin.discriminant())
    iso=E.isomorphism_to(Emin)
    print('ISO_URST',iso.tuple())
    print('ISO_MAPS',iso.rational_maps())
    inv=iso.inverse()
    print('INV_URST',inv.tuple())
    print('INV_MAPS',inv.rational_maps())
except Exception as ex:
    print('MIN_ERR',repr(ex))
    Emin=EllipticCurve(QQ,[0,-1,1,0,0])
    iso=None
for p in [2,3,5,7,13]:
    try:
        Ep=Emin.change_ring(GF(p))
        print('RED',p,'CARD',Ep.cardinality(),'POINTS',Ep.points())
    except Exception as ex: print('RED_ERR',p,repr(ex))
for x0 in [-12,24]:
  for y0 in [-108,108]:
    try:
      P=E(x0,y0)
      print('POINT',P,'MIN',iso(P) if iso is not None else None,'2P',2*P,'5P',5*P)
    except Exception as ex: print('POINT_ERR',x0,y0,repr(ex))
S.<aa,b,c,z,x,y> = PolynomialRing(QQ)
D=c-2*b
const=aa^2+4*D*b+8*b^2
lin=2*aa*D-8*D*b-14*b^2
quad=D^2+2*aa*b+8*D*b+12*b^2
tr=3*aa+4*D+8*b
s2=(tr^2-3*x)/2
print('W2_CONST',const.factor())
print('W2_LIN',lin.factor())
print('W2_QUAD',quad.factor())
print('TRACE',tr.factor())
print('S2_RAW',s2.factor())
# Direct candidate simplification checked by reducing differences against relations.
t_exp=3*aa^2+8*aa*c+4*c^2-6*b*c-4*b^2
rel1=x-(aa^2+4*b*c+24*z^2)
rel2=9*z^2-(aa*c-2*aa*b-4*b*c+b^2)
rel3=c^2+4*b*c+2*aa*b
I=S.ideal([rel1,rel2,rel3])
try:
  print('T_DIFF_REDUCE',I.reduce(s2-t_exp))
  print('XPLUS_T',I.reduce(x+t_exp))
except Exception as ex: print('GB_ERR',repr(ex))
U.<A,Dd,Bb> = PolynomialRing(QQ)
M=matrix(U,3,3)
M[:,0]=vector([A,Dd,Bb])
M[:,1]=vector([2*Bb,A-4*Bb,Dd+4*Bb])
M[:,2]=vector([2*Dd+8*Bb,-4*Dd-14*Bb,A+4*Dd+12*Bb])
print('NORM_W',M.det().factor())
print('END_Q4570')
