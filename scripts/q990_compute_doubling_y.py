#!/usr/bin/env python3
"""Q990: direct exact certificate for the Vélu doubling negAddY identity.

The checker keeps B independent, verifies the full original rational identity,
normalizes to the reduced denominator, and proves the compact coefficient

    CY = (DX*delta(CX) - CX*delta(DX))/e - d*t*p^2*V^2.

Here CX and DX are the primitive Q971 doubling-X numerator coefficient and
denominator, and delta is the source-curve derivation delta(x)=1,
delta(z)=3*x^2+A.  The last term is the exact correction caused by the fact
that the off-curve Vélu image has target residual (e/d^2)^2*(z-F0).
"""

from __future__ import annotations

import hashlib

import sympy as sp


x1, y1, A, r, B = sp.symbols("x1 y1 A r B")
Z = sp.symbols("Z")


def require_zero(expr: sp.Expr, label: str) -> None:
    """Require an exact polynomial/rational zero and print a useful failure."""
    reduced = sp.cancel(sp.together(expr))
    if reduced != 0:
        print(f"FAILED: {label}")
        num, den = sp.fraction(reduced)
        print(f"denominator = {sp.factor(den)}")
        print(f"numerator factorization = {sp.factor(num)}")
        raise AssertionError(label)


def term_count(expr: sp.Expr) -> int:
    expanded = sp.expand(expr)
    return 0 if expanded == 0 else len(expanded.as_ordered_terms())


def digest(expr: sp.Expr) -> str:
    payload = sp.sstr(sp.expand(expr), order="lex").encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


# ---------------------------------------------------------------------------
# 1. Full rational identity in the original variables
# ---------------------------------------------------------------------------
t = 3 * r**2 + A
Ap = A - 5 * t
Bp = B - 7 * r * t  # Retained to document the complete quotient curve.

u = 3 * x1**2 + A
ell = u / (2 * y1)
x3 = ell**2 - 2 * x1

y3_std = ell * (x1 - x3) - y1
neg_y3 = -ell * (x1 - x3) + y1

X1p = x1 + t / (x1 - r)
Y1p = y1 * ((x1 - r) ** 2 - t) / (x1 - r) ** 2
ellp = (3 * X1p**2 + Ap) / (2 * Y1p)
X3p = ellp**2 - 2 * X1p

Y3p_std = ellp * (X1p - X3p) - Y1p
neg_Y3p = -ellp * (X1p - X3p) + Y1p


def phiY(xx: sp.Expr, yy: sp.Expr) -> sp.Expr:
    return yy * ((xx - r) ** 2 - t) / (xx - r) ** 2


diff_std = phiY(x3, y3_std) - Y3p_std
diff_neg = phiY(x3, neg_y3) - neg_Y3p
require_zero(diff_neg + diff_std, "Mathlib negAddY sign")


# ---------------------------------------------------------------------------
# 2. Compact Q971 names and the corrected differentiated coefficient
# ---------------------------------------------------------------------------
z = y1**2
d = x1 - r
e = d**2 - t
m = x1 * d + t
p = 3 * m**2 + (A - 5 * t) * d**2
h = 2 * x1 + r
F0 = x1**3 + A * x1 - r**3 - A * r

require_zero(F0 - d * (m + 2 * r * d), "F0 factorization")


def compact_data(zz: sp.Expr) -> dict[str, sp.Expr]:
    """Return the exact compact coefficient and all named subexpressions."""
    k = 2 * t - d * h
    w = zz + F0
    s = u**2 * k - 12 * t * (x1 + r) * w
    v = u**2 - 4 * h * zz

    pdot = 6 * m * (x1 + d) + 2 * (A - 5 * t) * d
    sdot = (
        12 * x1 * u * k
        - u**2 * (h + 2 * d)
        - 12 * t * (w + 2 * (x1 + r) * u)
    )
    vdot = 12 * x1 * u - 8 * zz - 4 * h * u

    cx = d * h * p**2 + e**2 * s
    cxdot = (
        (h + 2 * d) * p**2
        + 2 * d * h * p * pdot
        + 4 * d * e * s
        + e**2 * sdot
    )

    # DX = d*zz*e^2*v, so delta(DX)/e is the following polynomial.
    dbar = e * v * (zz + d * u) + d * zz * (4 * d * v + e * vdot)

    # Wronskian contribution minus the exact off-curve target correction.
    cy = d * zz * e * v * cxdot - cx * dbar - d * t * p**2 * v**2

    return {
        "k": sp.expand(k),
        "w": sp.expand(w),
        "s": sp.expand(s),
        "v": sp.expand(v),
        "pdot": sp.expand(pdot),
        "sdot": sp.expand(sdot),
        "vdot": sp.expand(vdot),
        "cx": sp.expand(cx),
        "cxdot": sp.expand(cxdot),
        "dbar": sp.expand(dbar),
        "cy": sp.expand(cy),
    }


dataZ = compact_data(Z)
data = compact_data(z)
CYZ = dataZ["cy"]
CY = data["cy"]
VZ = dataZ["v"]
V = data["v"]
CXZ = dataZ["cx"]
CX = data["cx"]

require_zero(x3 - r - V / (4 * z), "source doubled X")
require_zero(ellp - p / (2 * y1 * e), "target tangent slope")


# ---------------------------------------------------------------------------
# 3. Reduced numerator and the requested equal coefficients
# ---------------------------------------------------------------------------
denY = 2 * y1**3 * d**2 * e**3 * V**2

rat_std = sp.cancel(sp.together(diff_std))
num_std_cas, den_std_cas = sp.fraction(rat_std)
scale_std = sp.cancel(den_std_cas / denY)
assert not scale_std.free_symbols and scale_std != 0
N_std = sp.cancel(num_std_cas / scale_std)
assert sp.denom(sp.together(N_std)) == 1
N_std = sp.expand(N_std)
require_zero(rat_std - N_std / denY, "standard reduced normalization")
require_zero(N_std - CY * (z - F0), "compact standard-Y certificate")

rat_neg = sp.cancel(sp.together(diff_neg))
num_neg_cas, den_neg_cas = sp.fraction(rat_neg)
scale_neg = sp.cancel(den_neg_cas / denY)
assert not scale_neg.free_symbols and scale_neg != 0
N_neg = sp.cancel(num_neg_cas / scale_neg)
assert sp.denom(sp.together(N_neg)) == 1
N_neg = sp.expand(N_neg)
require_zero(rat_neg - N_neg / denY, "negAddY reduced normalization")
require_zero(N_neg + N_std, "negAddY primitive numerator sign")

hcurve1 = z - x1**3 - A * x1 - B
htors = r**3 + A * r + B
require_zero((z - F0) - (hcurve1 + htors), "combined residual")
assert B not in CY.free_symbols
require_zero(N_neg - (-CY) * hcurve1 - (-CY) * htors, "equal coefficient pair")

raw_std = sp.together(diff_std)
raw_num_std, raw_den_std = sp.fraction(raw_std)
raw_multiplier_std = sp.factor(sp.cancel(raw_num_std / N_std))
assert sp.denom(sp.together(raw_multiplier_std)) == 1
require_zero(raw_num_std - raw_multiplier_std * N_std, "raw numerator multiplier")
require_zero(raw_num_std * denY - N_std * raw_den_std, "raw denominator cross-check")


# ---------------------------------------------------------------------------
# 4. Q971 Wronskian relation and exact correction term
# ---------------------------------------------------------------------------
DXZ = sp.expand(d * Z * e**2 * VZ)


def delta(expr: sp.Expr) -> sp.Expr:
    return sp.expand(sp.diff(expr, x1) + u * sp.diff(expr, Z))


wronskian_num = sp.expand(DXZ * delta(CXZ) - CXZ * delta(DXZ))
wronskian_q, wronskian_rem = sp.div(
    sp.Poly(wronskian_num, Z, x1, A, r, domain=sp.QQ),
    sp.Poly(e, Z, x1, A, r, domain=sp.QQ),
)
assert wronskian_rem.is_zero
CY_wronskian = sp.expand(wronskian_q.as_expr())
correction = sp.expand(d * t * p**2 * VZ**2)
require_zero(CYZ - (CY_wronskian - correction), "Wronskian plus target-residual correction")

# Directly audit each hand-written derivative abbreviation.
require_zero(dataZ["pdot"] - delta(p), "pdot")
require_zero(dataZ["sdot"] - delta(dataZ["s"]), "sdot")
require_zero(dataZ["vdot"] - delta(VZ), "vdot")
require_zero(dataZ["cxdot"] - delta(CXZ), "cxdot")
require_zero(dataZ["dbar"] - delta(DXZ) / e, "delta(DX)/e")


# ---------------------------------------------------------------------------
# 5. Exact factorization audit and reproducible report
# ---------------------------------------------------------------------------
content_CY, factors_CY = sp.factor_list(CYZ)
factored_CY = sp.factor(CYZ)
require_zero(factored_CY - CYZ, "factorization reconstruction")
gcd_CY_CX = sp.factor(
    sp.gcd(
        sp.Poly(CYZ, Z, x1, A, r, domain=sp.QQ),
        sp.Poly(CXZ, Z, x1, A, r, domain=sp.QQ),
    ).as_expr()
)

print("## Q990 exact result")
print()
print(f"- SymPy version: `{sp.__version__}`")
print(f"- reduced denominator scale for standard Y: `{scale_std}`")
print(f"- reduced denominator scale for negAddY: `{scale_neg}`")
print(f"- raw/reduced standard-numerator multiplier: `{sp.sstr(raw_multiplier_std, order='lex')}`")
print(f"- primitive standard numerator terms: `{term_count(N_std)}`")
print(f"- compact coefficient expanded terms: `{term_count(CYZ)}`")
print(f"- compact coefficient degree in Z: `{sp.degree(CYZ, Z)}`")
print(f"- compact coefficient SHA-256: `{digest(CYZ)}`")
print("- `N_std = CY*(z-F0)` verified exactly")
print("- `N_neg = (-CY)*(z-F0)` verified exactly")
print("- `N_neg = (-CY)*hcurve1 + (-CY)*htors` verified exactly")
print()
print("## Q971 differentiated relation")
print()
print("`(DX*delta(CX)-CX*delta(DX))/e` is polynomial.")
print("The exact correction is `d*t*p^2*V^2`, so")
print("`CY = (DX*delta(CX)-CX*delta(DX))/e - d*t*p^2*V^2`.")
print(f"- correction expanded terms: `{term_count(correction)}`")
print(f"- correction SHA-256: `{digest(correction)}`")
print()
print("## Exact factorization over QQ[x1,A,r,Z]")
print()
print(f"- content: `{content_CY}`")
print(f"- nonconstant factor count: `{len(factors_CY)}`")
for index, (factor, exponent) in enumerate(factors_CY, start=1):
    print(
        f"- factor {index}: exponent `{exponent}`, terms `{term_count(factor)}`, "
        f"SHA-256 `{digest(factor)}`"
    )
    if term_count(factor) <= 20:
        print(f"  - `{sp.sstr(factor, order='lex')}`")
print(f"- gcd(CY, Q971_CX): `{sp.sstr(gcd_CY_CX, order='lex')}`")
print()
print("## Compact definitions")
print()
print("```text")
print("z  = y1^2")
print("t  = 3*r^2 + A")
print("d  = x1-r")
print("e  = d^2-t")
print("u  = 3*x1^2+A")
print("m  = x1*d+t")
print("p  = 3*m^2+(A-5*t)*d^2")
print("h  = 2*x1+r")
print("F0 = x1^3+A*x1-r^3-A*r")
print("k  = 2*t-d*h")
print("S  = u^2*k-12*t*(x1+r)*(z+F0)")
print("V  = u^2-4*h*z")
print("pd = 6*m*(x1+d)+2*(A-5*t)*d")
print("Sd = 12*x1*u*k-u^2*(h+2*d)-12*t*((z+F0)+2*(x1+r)*u)")
print("Vd = 12*x1*u-8*z-4*h*u")
print("CX = d*h*p^2+e^2*S")
print("CXd = (h+2*d)*p^2+2*d*h*p*pd+4*d*e*S+e^2*Sd")
print("Dbar = e*V*(z+d*u)+d*z*(4*d*V+e*Vd)")
print("CY = d*z*e*V*CXd-CX*Dbar-d*t*p^2*V^2")
print("```")
print()
print("For the requested `LHS-RHS` using Mathlib `negAddY`:")
print()
print("```text")
print("c1 = c2 = -CY")
print("```")
