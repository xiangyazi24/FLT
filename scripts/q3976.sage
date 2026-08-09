from sage.all import *

print("Q3976_SAGE_VERSION", version())

# Exact Tate blow-up E(c,v)=c^(-40) F25(c+c^2 v,c).
R = PolynomialRing(QQ, names=('c','v'))
c, v = R.gens()
b = c + c^2*v
F5 = b-c
F6 = b-c-c^2
F7 = c^3-b^2+b*c
F8 = 2*b^2-3*b*c-b*c^2+c^2
F9 = F5^3+c^3*F6
G11 = F7*F5^3-b*c*F6^3
G12 = c*F6*(F5^2*F8+F7^2)
G13 = F5*F7^3+b*c*F6^3*F8
G14 = F7*(b*F6^2*F9-c^2*F5*F8^2)
num25 = G11*G13^3-b*G14*G12^3
assert num25 % F5 == 0
sub25 = num25 // F5
assert sub25 % c^40 == 0
E = sub25 // c^40
print("TATE_E_DEGREES", E.degree(c), E.degree(v), E.total_degree(), len(E.monomials()))

# Official LMFDB H(C,W,1).
S = PolynomialRing(QQ, names=('W','C'))
W, C = S.gens()
H = (C^3*W^8+2*C^2*W^9+C*W^10
 +C^4*W^6+3*C^3*W^7+2*C^2*W^8
 -C^4*W^5-2*C^3*W^6+C*W^8
 -C^5*W^3-3*C^4*W^4+C^3*W^5+2*C^2*W^6-2*C*W^7-W^8
 +C^4*W^3-C^3*W^4-4*C^2*W^5-C*W^6
 -2*C^4*W^2-C^3*W^3+2*C^2*W^4-C*W^5
 +C^4*W+2*C^3*W^2-2*C^2*W^3+C*W^4
 -C^3*W+2*C^2*W^2+C^3)
print("LMFDB_H_DEGREES", H.degree(W), H.degree(C), H.total_degree(), len(H.monomials()))

# Discriminants of the degree-10 projections.
print("BEGIN_TATE_DISCRIMINANT")
dE = E.discriminant(c)
Rv = PolynomialRing(QQ, 'v')
vv = Rv.gen()
dEv = Rv(dE.subs({c:0, v:vv}))
print("TATE_DISC_DEGREE", dEv.degree())
facE = dEv.factor()
print("TATE_DISC_FACTORIZATION", facE)
print("TATE_DISC_FACTOR_DEGREES", [(f.degree(), e) for f,e in facE])

print("BEGIN_LMFDB_DISCRIMINANT")
dH = H.discriminant(W)
RC = PolynomialRing(QQ, 'C')
CC = RC.gen()
dHC = RC(dH.subs({W:0, C:CC}))
print("LMFDB_DISC_DEGREE", dHC.degree())
facH = dHC.factor()
print("LMFDB_DISC_FACTORIZATION", facH)
print("LMFDB_DISC_FACTOR_DEGREES", [(f.degree(), e) for f,e in facH])

# Genus checks through algebraic function fields.
print("BEGIN_TATE_FUNCTION_FIELD")
Kv = FunctionField(QQ, 'v')
v0 = Kv.gen()
Pc = PolynomialRing(Kv, 'c')
c0 = Pc.gen()
# Rebuild directly to avoid multivariate coercion ambiguity.
b0 = c0+c0^2*v0
f5 = b0-c0
f6 = b0-c0-c0^2
f7 = c0^3-b0^2+b0*c0
f8 = 2*b0^2-3*b0*c0-b0*c0^2+c0^2
f9 = f5^3+c0^3*f6
g11 = f7*f5^3-b0*c0*f6^3
g12 = c0*f6*(f5^2*f8+f7^2)
g13 = f5*f7^3+b0*c0*f6^3*f8
g14 = f7*(b0*f6^2*f9-c0^2*f5*f8^2)
f25sub = (g11*g13^3-b0*g14*g12^3)//f5
Ef = (f25sub//c0^40).monic()
KT = Kv.extension(Ef, 'ct')
print("TATE_FUNCTION_FIELD_DEGREE", KT.degree())
print("TATE_GENUS", KT.genus())

print("BEGIN_LMFDB_FUNCTION_FIELD")
KC = FunctionField(QQ, 'C')
C0 = KC.gen()
PW = PolynomialRing(KC, 'W')
W0 = PW.gen()
Hf = (C0^3*W0^8+2*C0^2*W0^9+C0*W0^10
 +C0^4*W0^6+3*C0^3*W0^7+2*C0^2*W0^8
 -C0^4*W0^5-2*C0^3*W0^6+C0*W0^8
 -C0^5*W0^3-3*C0^4*W0^4+C0^3*W0^5+2*C0^2*W0^6-2*C0*W0^7-W0^8
 +C0^4*W0^3-C0^3*W0^4-4*C0^2*W0^5-C0*W0^6
 -2*C0^4*W0^2-C0^3*W0^3+2*C0^2*W0^4-C0*W0^5
 +C0^4*W0+2*C0^3*W0^2-2*C0^2*W0^3+C0*W0^4
 -C0^3*W0+2*C0^2*W0^2+C0^3).monic()
KL = KC.extension(Hf, 'wl')
print("LMFDB_FUNCTION_FIELD_DEGREE", KL.degree())
print("LMFDB_GENUS", KL.genus())
print("Q3976_SAGE_COMPLETE")
