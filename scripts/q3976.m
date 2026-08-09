SetColumns(0);
Q := Rationals();

// Tate blow-up b = c + c^2 v, as a degree-10 polynomial in c.
Rv<v> := PolynomialRing(Q);
Kv := FieldOfFractions(Rv);
Pc<c> := PolynomialRing(Kv);
bb := c+c^2*v;
F5 := bb-c;
F6 := bb-c-c^2;
F7 := c^3-bb^2+bb*c;
F8 := 2*bb^2-3*bb*c-bb*c^2+c^2;
F9 := F5^3+c^3*F6;
G11 := F7*F5^3-bb*c*F6^3;
G12 := c*F6*(F5^2*F8+F7^2);
G13 := F5*F7^3+bb*c*F6^3*F8;
G14 := F7*(bb*F6^2*F9-c^2*F5*F8^2);
sub25 := ExactQuotient(G11*G13^3-bb*G14*G12^3,F5);
E := ExactQuotient(sub25,c^40);
print "TATE_E_DEGREE", Degree(E);
print "BEGIN_TATE_DISC";
dE := Discriminant(E);
numE := Numerator(dE);
denE := Denominator(dE);
print "TATE_DISC_NUM_DEGREE_TERMS", Degree(numE), #Terms(numE);
print "TATE_DISC_DEN", denE;
facE := Factorization(numE);
print "TATE_DISC_FACTORS_COUNT", #facE;
for fe in facE do
  print "TATE_FACTOR", Degree(fe[1]), fe[2], fe[1];
end for;

// LMFDB H(C,W,1), degree 10 in W over Q(C).
RC<C> := PolynomialRing(Q);
KC := FieldOfFractions(RC);
PW<W> := PolynomialRing(KC);
H :=
 C^3*W^8+2*C^2*W^9+C*W^10
 +C^4*W^6+3*C^3*W^7+2*C^2*W^8
 -C^4*W^5-2*C^3*W^6+C*W^8
 -C^5*W^3-3*C^4*W^4+C^3*W^5+2*C^2*W^6-2*C*W^7-W^8
 +C^4*W^3-C^3*W^4-4*C^2*W^5-C*W^6
 -2*C^4*W^2-C^3*W^3+2*C^2*W^4-C*W^5
 +C^4*W+2*C^3*W^2-2*C^2*W^3+C*W^4
 -C^3*W+2*C^2*W^2+C^3;
print "LMFDB_H_DEGREE", Degree(H);
print "BEGIN_LMFDB_DISC";
dH := Discriminant(H);
numH := Numerator(dH);
denH := Denominator(dH);
print "LMFDB_DISC_NUM_DEGREE_TERMS", Degree(numH), #Terms(numH);
print "LMFDB_DISC_DEN", denH;
facH := Factorization(numH);
print "LMFDB_DISC_FACTORS_COUNT", #facH;
for fh in facH do
  print "LMFDB_FACTOR", Degree(fh[1]), fh[2], fh[1];
end for;
print "BRANCH_DIVISORS_COMPLETE";
