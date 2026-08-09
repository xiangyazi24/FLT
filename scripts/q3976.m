SetColumns(0);
Q := Rationals();

// Tate primitive order-25 component over Q(c).
Kc<c> := FunctionField(Q);
Pb<b> := PolynomialRing(Kc);
F5 := b-c;
F6 := b-c-c^2;
F7 := c^3-b^2+b*c;
F8 := 2*b^2-3*b*c-b*c^2+c^2;
F9 := F5^3+c^3*F6;
G11 := F7*F5^3-b*c*F6^3;
G12 := c*F6*(F5^2*F8+F7^2);
G13 := F5*F7^3+b*c*F6^3*F8;
G14 := F7*(b*F6^2*F9-c^2*F5*F8^2);
num25 := G11*G13^3-b*G14*G12^3;
assert IsDivisibleBy(num25,F5);
F25 := ExactQuotient(num25,F5);
fT := F25/LeadingCoefficient(F25);
print "TATE_DEGREES", Degree(F25), #Terms(F25);
print "TATE_IRREDUCIBLE", IsIrreducible(fT);
KT<B> := FunctionField(fT);
print "TATE_FIELD", KT;
print "TATE_GENUS", Genus(KT);

// Official LMFDB plane model H(C,W,S)=0, dehomogenized at S=1.
Kw<W> := FunctionField(Q);
PC<C> := PolynomialRing(Kw);
H :=
 C^3*W^8+2*C^2*W^9+C*W^10
 +C^4*W^6+3*C^3*W^7+2*C^2*W^8
 -C^4*W^5-2*C^3*W^6+C*W^8
 -C^5*W^3-3*C^4*W^4+C^3*W^5+2*C^2*W^6-2*C*W^7-W^8
 +C^4*W^3-C^3*W^4-4*C^2*W^5-C*W^6
 -2*C^4*W^2-C^3*W^3+2*C^2*W^4-C*W^5
 +C^4*W+2*C^3*W^2-2*C^2*W^3+C*W^4
 -C^3*W+2*C^2*W^2+C^3;
fL := H/LeadingCoefficient(H);
print "LMFDB_DEGREES", Degree(H), #Terms(H);
print "LMFDB_IRREDUCIBLE", IsIrreducible(fL);
KL<CC> := FunctionField(fL);
print "LMFDB_FIELD", KL;
print "LMFDB_GENUS", Genus(KL);

print "FIELD_SETUP_COMPLETE";
