SetColumns(0);
Q := Rationals();
P11<[X]> := ProjectiveSpace(Q,11);
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
Can := Curve(P11,QL);
P2<C,W,S> := ProjectiveSpace(Q,2);
H :=
 C^3*W^8+2*C^2*W^9+C*W^10
 +C^4*W^6*S+3*C^3*W^7*S+2*C^2*W^8*S
 -C^4*W^5*S^2-2*C^3*W^6*S^2+C*W^8*S^2
 -C^5*W^3*S^3-3*C^4*W^4*S^3+C^3*W^5*S^3+2*C^2*W^6*S^3-2*C*W^7*S^3-W^8*S^3
 +C^4*W^3*S^4-C^3*W^4*S^4-4*C^2*W^5*S^4-C*W^6*S^4
 -2*C^4*W^2*S^5-C^3*W^3*S^5+2*C^2*W^4*S^5-C*W^5*S^5
 +C^4*W*S^6+2*C^3*W^2*S^6-2*C^2*W^3*S^6+C*W^4*S^6
 -C^3*W*S^7+2*C^2*W^2*S^7+C^3*S^8;
Plane := Curve(P2,H);
pi := map< Can -> Plane | [qc,w,s] >;
hasInv, invpi := IsInvertible(pi);
assert hasInv;
ee := DefiningEquations(invpi);

// Work on S=1 and reduce every projective ratio through H(C,W,1).
KC<C0> := FunctionField(Q);
PW<W0> := PolynomialRing(KC);
H0 := Evaluate(H,[C0,W0,1]);
FL<ww> := FunctionField(H0/LeadingCoefficient(H0));
vals := [ Evaluate(ee[i],[FL!C0,ww,FL!1]) : i in [1..12] ];
assert vals[9] ne 0;
for i in [1..12] do
  print "CANONICAL_OVER_S", i, vals[i]/vals[9];
end for;
// Target quotient coordinates divided by Z_tgt.
Xt := -vals[3]+vals[4]-vals[6]-vals[7]-vals[8]-vals[10]-vals[11]+vals[12];
Yt := vals[1]-vals[5]-vals[6]-vals[7]-vals[11];
Zt := -vals[1]-vals[3]+vals[4]+vals[5]+vals[6]-vals[8]-vals[9];
Wt := -vals[3]+vals[4]-vals[6]-vals[7]-vals[8]-vals[11];
print "TARGET_X_OVER_Z", Xt/Zt;
print "TARGET_Y_OVER_Z", Yt/Zt;
print "TARGET_W_OVER_Z", Wt/Zt;
print "Q3976_COMPACT_PLANE_INVERSE_COMPLETE";
