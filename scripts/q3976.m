SetColumns(0);
k := GF(3);

// Tate field FT = k(v,c), E(c,v)=0.
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
print "TATE_FIELD_READY", Degree(FT), #Places(FT,1);

// LMFDB plane field FL = k(C,W), H(C,W,1)=0.
KC<C> := FunctionField(k);
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
FL<wl> := FunctionField(H/LeadingCoefficient(H));
print "LMFDB_FIELD_READY", Degree(FL), #Places(FL,1);

print "BEGIN_DEGONE_FUNCTION_FIELD_ISOMORPHISM";
ok, phi := IsIsomorphic(FT,FL : Strategy := "DegOne");
print "ISOMORPHIC", ok;
if ok then
  print "IMAGE_TATE_C", phi(ct);
  print "IMAGE_TATE_V", phi(FT!v);
  hinv, psi := HasInverse(phi);
  print "HAS_INVERSE", hinv;
  if hinv cmpeq true then
    print "IMAGE_LMFDB_W", psi(wl);
    print "IMAGE_LMFDB_C", psi(FL!C);
  end if;
end if;
print "Q3976_DEGONE_F3_COMPLETE";
