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
psi5p = sp.Poly(psi5, X)
print('psi5_degree_X =', psi5p.degree())
print('psi5_terms =', len(psi5p.terms()))
print('b2 =', b2)
print('b4 =', b4)
print('b6 =', b6)
print('b8 =', b8)

# Invariant r = (q X - t^2(t-1))/(t^2(t-1)^2).
Xsol = t**2*(t-1)*(r*(t-1)+1)/q
N = sp.cancel(q**12 * psi5.subs(X, Xsol))
Nnum, Nden = sp.fraction(N)
assert sp.expand(Nden) == 1
Nnum = sp.Poly(sp.expand(Nnum), t, r)
fac = t**24 * (t-1)**24
Qpoly, Rem = sp.div(Nnum, sp.Poly(fac, t, r))
print('division_remainder_zero =', Rem.is_zero)
H = sp.expand(Qpoly.as_expr())
print('H_degree_t =', sp.Poly(H, t).degree())
print('H_degree_r =', sp.Poly(H, r).degree())

# Reduce H modulo t^3 - s t^2 + (s-3)t + 1.
K = sp.QQ.frac_field(s, r)
Ht = sp.Poly(H, t, domain=K)
cubic = sp.Poly(t**3 - s*t**2 + (s-3)*t + 1, t, domain=K)
Remainder = Ht.rem(cubic).as_expr()
Remainder = sp.factor(Remainder)
print('remainder =', Remainder)
RP = sp.Poly(sp.expand(Remainder), t, domain=K)
print('remainder_degree_t =', RP.degree())
R35 = sp.cancel(RP.coeff_monomial(1)) if RP.degree() == 0 else None
print('R35 =', sp.factor(R35) if R35 is not None else 'NONCONSTANT')
if R35 is not None:
    R35 = sp.factor(R35)
    num, den = sp.fraction(R35)
    print('R35_den =', sp.factor(den))
    R35num = sp.Poly(sp.expand(num), s, r)
    print('R35_degree_s =', R35num.degree(s))
    print('R35_degree_r =', R35num.degree(r))
    print('R35_terms =', len(R35num.terms()))
    print('R35_expanded =', R35num.as_expr())
    if R35num.degree(s) == 2:
        A = sp.Poly(R35num.as_expr(), s).coeff_monomial(s**2)
        B = sp.Poly(R35num.as_expr(), s).coeff_monomial(s)
        C = sp.Poly(R35num.as_expr(), s).coeff_monomial(1)
        disc = sp.factor(B**2 - 4*A*C)
        print('quad_A =', sp.factor(A))
        print('quad_B =', sp.factor(B))
        print('quad_C =', sp.factor(C))
        print('disc_factor =', disc)
