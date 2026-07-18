import sympy as sp

# Exact symbolic computation of the X_1(7) x X_0(5) quotient.
t, X, s, r = sp.symbols('t X s r')
q = t**2 - t + 1

a1 = 1 + t - t**2
a2 = t**2 * (1 - t)
a3 = a2
a4 = sp.Integer(0)
a6 = sp.Integer(0)

b2 = sp.expand(a1**2 + 4*a2)
b4 = sp.expand(a1*a3 + 2*a4)
b6 = sp.expand(a3**2 + 4*a6)
b8 = sp.expand(a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2)

psi3 = sp.expand(3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8)
psi2sq = sp.expand(4*X**3 + b2*X**2 + 2*b4*X + b6)
F4 = sp.expand(
    2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2
    + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
)
psi5 = sp.expand(F4*psi2sq**2 - psi3**3)
print('psi5_degree_X =', sp.Poly(psi5, X).degree())
print('b2 =', b2)
print('b4 =', b4)
print('b6 =', b6)
print('b8 =', b8)

# Check the diamond-action weight.
tp = (t-1)/t
Xp = (X - t**2*(t-1))/t**4
ratio_check = sp.factor(sp.together(t**48 * psi5.subs({t: tp, X: Xp}, simultaneous=True) - psi5))
print('diamond_weight_certificate_zero =', ratio_check == 0)

# Invariant r = (q X - t^2(t-1))/(t^2(t-1)^2).
Xsol = t**2*(t-1)*(r*(t-1)+1)/q
I = sp.cancel(q**12 * psi5.subs(X, Xsol) / (t**24 * (t-1)**24))
Inum, Iden = map(sp.expand, sp.fraction(I))
print('I_num_degree_t =', sp.Poly(Inum, t).degree())
print('I_den_factor =', sp.factor(Iden))

# Reduce the rational function I modulo the cubic relation for t over s.
K = sp.QQ.frac_field(s, r)
cubic = sp.Poly(t**3 - s*t**2 + (s-3)*t + 1, t, domain=K)
numrem = sp.Poly(Inum, t, domain=K).rem(cubic)
denrem = sp.Poly(Iden, t, domain=K).rem(cubic)
deni = sp.invert(denrem, cubic)
Rrem = (numrem * deni).rem(cubic)
print('invariant_remainder_degree_t =', Rrem.degree())
print('invariant_remainder =', sp.factor(Rrem.as_expr()))
if Rrem.degree() == 0:
    R35 = sp.cancel(Rrem.coeff_monomial(1))
    R35num, R35den = sp.fraction(R35)
    R35num = sp.factor(R35num)
    R35den = sp.factor(R35den)
    print('R35_den =', R35den)
    P35 = sp.Poly(sp.expand(R35num), s, r)
    print('R35_degree_s =', P35.degree(s))
    print('R35_degree_r =', P35.degree(r))
    print('R35_terms =', len(P35.terms()))
    print('R35_num =', P35.as_expr())

# Duplication involution on x(Q), then on invariant r.
phi2 = sp.expand(X**4 - b4*X**2 - 2*b6*X - b8)
X2 = sp.cancel(phi2 / psi2sq)
r2 = sp.cancel((q*X2 - t**2*(t-1))/(t**2*(t-1)**2))
r2_sub = sp.cancel(r2.subs(X, Xsol))
print('r2_raw =', sp.factor(r2_sub))
# Reduce r2 rationally modulo the cubic relation.
r2n, r2d = map(sp.expand, sp.fraction(r2_sub))
r2nr = sp.Poly(r2n, t, domain=K).rem(cubic)
r2dr = sp.Poly(r2d, t, domain=K).rem(cubic)
r2red = (r2nr * sp.invert(r2dr, cubic)).rem(cubic)
print('r2_remainder_degree_t =', r2red.degree())
print('r2_reduced =', sp.factor(r2red.as_expr()))
