SetColumns(0);
k := GF(11);

// Tate primitive order-25 function field after the exact blow-up
// b = c + c^2*v and removal of the exceptional factor c^40.
Kv<v> := FunctionField(k);
Pc<c> := PolynomialRing(Kv);
b := c+c^2*v;
F5 := b-c;
F6 := b-c-c^2;
F7 := c^3-b^2+b*c;
F8 := 2*b^2-3*b*c-b*c^2+c^2;
F9 := F5^3+c^3*F6;
G11 := F7*F5^3-b*c*F6^3;
G12 := c*F6*(F5^2*F8+F7^2);
G13 := F5*F7^3+b*c*F6^3*F8;
G14 := F7*(b*F6^2*F9-c^2*F5*F8^2);
sub25 := ExactQuotient(G11*G13^3-b*G14*G12^3,F5);
E := ExactQuotient(sub25,c^40);
FT<ct> := FunctionField(E/LeadingCoefficient(E));
B := BasisOfHolomorphicDifferentials(FT);
assert #B eq 12;
f := [ B[i]/B[1] : i in [1..12] ];
prods := [ f[i]*f[j] : i in [1..12], j in [i..12] ];
Rels := Relations(prods,k);
print "TATE_QUADRIC_RELATION_DIMENSION", Dimension(Rels);
assert Dimension(Rels) eq 45;

P<[X]> := ProjectiveSpace(k,11);
mons := [ X[i]*X[j] : i in [1..12], j in [i..12] ];
QT := [ &+[ rr[n]*mons[n] : n in [1..#mons] ] : rr in Basis(Rels) ];
CT := Curve(P,QT);
print "TATE_CANONICAL_CURVE_BUILT", #DefiningEquations(CT);

// Official LMFDB canonical model, coordinate order
// x,y,z,w,t,u,v,r,s,a,b,c.
x:=X[1]; y:=X[2]; z:=X[3]; w:=X[4]; t:=X[5]; u:=X[6];
qv:=X[7]; r:=X[8]; s:=X[9]; a:=X[10]; qb:=X[11]; qc:=X[12];
QL := [
x*y-x*r-x*a-s*qb+a*qb,
qv*qb+qv*qc-s*qb+a*qb,
x*z-x*w+x*u+x*r-x*qc+s*qb,
x*s-y*z-y*u-qv*s-a*qc,
x*u-x*qc+y*t-u*qb+qv*qc-a*qc,
y*z+y*s-u*qb+qv*qc-s*qc+a*qc,
x*u-x*s+y*u-w*u+u*qb+a*qb,
x*s+x*qb-y*u-u*qb+qv*qc+r*qc-s*qb+qb*qc,
x*w+x*t+x*qc-qv*r-s*qb,
x*r-y*t-y*u+u*a+s*qb,
x*w-x*s-y*s+u*s+qv*s,
y*z+u*r+u*a+qv*s-a*qb,
x*u-x*s-x*qc+t*qc+u*qc-qv*qb+s*qb,
x*z-x*qb+t*qb+u*qb+qv*qb,
x*s-y*qc-z*r-qv*r+r*qc-s*qb-a*qb,
x^2+x*y-x*w+x*r+x*a+y^2-y*u-qv*s+s*qb,
x*s+y^2+y*t-y*s-y*a+r*s+s*a+s*qb-a*qb,
x*w+x*s-w*s-qv*r+r*s-r*a+s*qc-a*qc,
x^2+x*y-x*qv-y*u+y*a-u*qb-qv*r-qv*a-qv*qb-a*qc,
x*t+y*t+y*qc-t*u+t*qc-a*qc,
x*z-y*s+z*t-t*a+u*qb-qv*qc,
x*w-w*s-t*s+a*qb,
y*s+t*qv+t*a,
w*u-w*qc-u*qb,
x*w-y*u-w*qb-u*qb+qv*qc,
y*s-w*a+a*qb,
x*r+x*s-z*t-t*r-qv*r+s*qc-a*qb-a*qc,
x*w+w*r+s*qc+a*qb,
x*w+y*z-w*qv-u*qb+qv*s-a*qb,
x*z+x*u+w*t-s*qc,
w^2+u*s,
x*w-y*t-y*qc-z*qc-s*qb+a*qb+a*qc,
z*r+z*qb+qv*r+s*qb,
x*w+y*z-z*s-u*qb+qv*qc,
x*z-z*u+u*qb-qv*qc,
x*s+z*w-a*qb-a*qc,
x*t+x*u+x*r+y^2+y*t-y*a-z*a+s*qb,
x^2-x*t-x*u+x*a+y*z-z*qv-u*qb+qv*qc-a*qb,
x*y+x*z-x*a+y*z-y*t+z^2-u*r-qv*r,
x*qb-y*t+y*qb-s*qb+a*qb+a*qc,
x*s+y*t+y*r-a*qb-a*qc,
y*w+a*qc,
x*qv+x*a+y*qv-qv*s,
x^2-x*t-x*u-x*s+x*a+t*u+u^2+u*qv,
x*w+x*s+y*t+t*qb+r^2+r*a+r*qb-s*qb-a*qc
];
CL := Curve(P,QL);
print "LMFDB_CANONICAL_CURVE_BUILT", #DefiningEquations(CL);

print "BEGIN_CANONICAL_ISOMORPHISM";
ok, phi := IsIsomorphic(CT,CL);
print "CANONICAL_ISOMORPHIC", ok;
if ok then
  eqphi := DefiningEquations(phi);
  print "FORWARD_COORDINATE_COUNT", #eqphi;
  for i in [1..#eqphi] do
    print "PHI_COORD", i, eqphi[i];
  end for;
  psi := Inverse(phi);
  eqpsi := DefiningEquations(psi);
  print "INVERSE_COORDINATE_COUNT", #eqpsi;
  for i in [1..#eqpsi] do
    print "PSI_COORD", i, eqpsi[i];
  end for;
end if;
print "Q3976_CANONICAL_F11_COMPLETE";
