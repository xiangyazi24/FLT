SetColumns(0);
k := GF(101);

// Tate blow-up model E(c,v)=0 over F_101.
A2<c,v> := AffineSpace(k,2);
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
CTaff := Curve(A2,E);
CT := ProjectiveClosure(CTaff);
print "TATE_PROJECTIVE_DEGREE", Degree(CT);

// Official LMFDB plane curve.
P2<C,W,S> := ProjectiveSpace(k,2);
H :=
 C^3*W^8+2*C^2*W^9+C*W^10
 +C^4*W^6*S+3*C^3*W^7*S+2*C^2*W^8*S
 -C^4*W^5*S^2-2*C^3*W^6*S^2+C*W^8*S^2
 -C^5*W^3*S^3-3*C^4*W^4*S^3+C^3*W^5*S^3+2*C^2*W^6*S^3-2*C*W^7*S^3-W^8*S^3
 +C^4*W^3*S^4-C^3*W^4*S^4-4*C^2*W^5*S^4-C*W^6*S^4
 -2*C^4*W^2*S^5-C^3*W^3*S^5+2*C^2*W^4*S^5-C*W^5*S^5
 +C^4*W*S^6+2*C^3*W^2*S^6-2*C^2*W^3*S^6+C*W^4*S^6
 -C^3*W*S^7+2*C^2*W^2*S^7+C^3*S^8;
CL := Curve(P2,H);
print "LMFDB_PROJECTIVE_DEGREE", Degree(CL);
print "BEGIN_ISOMORPHISM";
ok, phi := IsIsomorphic(CT,CL);
print "ISOMORPHIC", ok;
if ok then
  print "FORWARD_MAP";
  print phi;
  psi := Inverse(phi);
  print "INVERSE_MAP";
  print psi;
end if;
print "FINITE_FIELD_ISOMORPHISM_COMPLETE";
