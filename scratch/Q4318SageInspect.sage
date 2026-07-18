R.<a,h> = PolynomialRing(QQ)
F = h*(a^2+13*a+49)*(a^2+5*a+1)^3 - a*(h^2+10*h+5)^3
print('factor=',factor(F))
P2.<A,H,Z> = ProjectiveSpace(QQ,2)
Fp = H*(A^2+13*A*Z+49*Z^2)*(A^2+5*A*Z+Z^2)^3 - A*Z^2*(H^2+10*H*Z+5*Z^2)^3
print('homogeneous=',Fp.is_homogeneous(),'degree=',Fp.degree())
C=Curve(P2,Fp)
print('curve=',C)
print('curve type=',type(C))
print('curve methods=',[m for m in dir(C) if any(k in m.lower() for k in ['normal','function','canonical','hyperell','genus','riemann','model','smooth','singular'])])
for name in ['genus','arithmetic_genus','is_singular','singular_points','function_field','normalization','canonical_model','hyperelliptic_model']:
 try:
  obj=getattr(C,name)
  print(name,'=',obj() if callable(obj) else obj)
 except Exception as e: print(name,'ERROR',repr(e))
try:
 K=C.function_field()
 print('K=',K,'type=',type(K))
 print('K methods=',[m for m in dir(K) if any(k in m.lower() for k in ['normal','canonical','hyperell','genus','riemann','model','curve','places'])])
 for name in ['genus','places','maximal_order','constant_field']:
  try:
   obj=getattr(K,name); print('K',name,'=',obj() if callable(obj) else obj)
  except Exception as e: print('K',name,'ERROR',repr(e))
except Exception as e: print('function field outer ERROR',repr(e))
E=EllipticCurve([0,1,1,9,1])
print('E=',E)
print('rank=',E.rank(proof=True),'torsion=',E.torsion_subgroup())
print('E methods=',[m for m in dir(E) if any(k in m.lower() for k in ['modular','param','isogen','descent','selmer'])])
try:
 phi=E.modular_parametrization()
 print('phi=',phi,'type=',type(phi))
 print('phi methods=',[m for m in dir(phi) if any(k in m.lower() for k in ['series','power','map','x','y'])])
 for name in ['x_coordinate','y_coordinate','power_series','q_expansion']:
  try:
   obj=getattr(phi,name); print('phi',name,'=',obj() if callable(obj) else obj)
  except Exception as e: print('phi',name,'ERROR',repr(e))
except Exception as e: print('phi outer ERROR',repr(e))
