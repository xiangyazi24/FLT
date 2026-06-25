# Q238 (dm3): per-`n` certificates vs general-`n` projective formula

## Verdict

For the **Mazur `|T| ≤ 16` bound only**, the per-`n` certificate route is faster to formalize than building the full general-`n` projective formula with `ω_n` and the coordinate-ring X/Y identities.

The tradeoff is exactly as stated:

```text
per-n route:      finite generated certificates, boring Lean, certificate-size risk
projective route: mathematically uniform, but a 600–1200 line infrastructure project
```

For `n = 1..16`, I would choose the per-`n` route unless the generated certs for `n ≥ 9` become too large for Lean to elaborate.  The right implementation is not hand-written `ring`; it is generated sparse certificate checking.

One caveat: the explicit `n=5` certificate below is for a **short Weierstrass curve**

```text
y² = x³ + A x + B.
```

It is directly useful in characteristic not `2,3`, or after reducing the relevant Mazur setup to a short model.  If the final Mathlib theorem must hold for arbitrary long Weierstrass equations in all characteristics allowed by `(n : k) ≠ 0`, then the same certificate method still applies, but the universal cofactors must be generated in the long Weierstrass/invariant variables and will be substantially larger.

---

## 1. Size estimates for `n = 5..16`

Let

```text
d(n) = deg_X(preΨ'_n)
     = (n² - 1)/2   if n is odd,
     = (n² - 4)/2   if n is even.
```

For a Bezout identity

```text
A_n · preΨ'_n + B_n · derivative(preΨ'_n) = R_n,
```

the canonical degree bounds are

```text
deg_X A_n ≤ d(n) - 2,
deg_X B_n ≤ d(n) - 1.
```

For short Weierstrass curves, with weights

```text
wt(X)=2, wt(A)=4, wt(B)=6,
```

the following table gives the expected **monomial slot count** for weighted-homogeneous cofactors.  For `n=5`, every slot is nonzero in the primitive certificate I computed.

| n | d(n) | exponent e(n) in Δ^e | deg_X A | deg_X B | short-curve cofactor slots |
|---:|---:|---:|---:|---:|---:|
| 5 | 12 | 22 | 10 | 11 | 452 |
| 6 | 16 | 40 | 14 | 15 | 1,136 |
| 7 | 24 | 92 | 22 | 23 | 4,072 |
| 8 | 30 | 145 | 28 | 29 | 8,150 |
| 9 | 40 | 260 | 38 | 39 | 19,800 |
| 10 | 48 | 376 | 46 | 47 | 34,640 |
| 11 | 60 | 590 | 58 | 59 | 68,500 |
| 12 | 70 | 805 | 68 | 69 | 109,550 |
| 13 | 84 | 1162 | 82 | 83 | 190,652 |
| 14 | 96 | 1520 | 94 | 95 | 285,856 |
| 15 | 112 | 2072 | 110 | 111 | 455,952 |
| 16 | 126 | 2625 | 124 | 125 | 651,126 |

Interpretation:

* `n=5,6` are very reasonable.
* `n=7,8` are large but still realistic with a generated sparse checker.
* `n=9..16` are too large for hand-maintained Lean and probably too large for naive `ring`/`linear_combination`; they are still plausible if the checker is data-driven and avoids elaborating a huge expanded expression.

For **long Weierstrass** certificates, term counts will be larger because coefficients live in more variables.  I would generate certs in invariant variables (`b₂,b₄,b₆,b₈`, or `c₄,c₆,Δ` where possible) rather than raw `a₁,a₂,a₃,a₄,a₆`.

---

## 2. Is the resultant always a discriminant power?

Yes, up to a nonzero integer supported at primes dividing `n`.

For short Weierstrass curves, the expected shape is

```text
Res_X(preΨ'_n, derivative(preΨ'_n)) = C_n · Δ^e(n),
```

where

```text
e(n) = d(n)(d(n)-1)/6.
```

For odd `n`, in the standard normalization:

```text
Disc_X(ψ_n) = (-1)^((n-1)/2) · n^((n²-3)/2)
              · Δ^((n²-1)(n²-3)/24),
```

and since `Res(f,f') = (-1)^(d(d-1)/2) lc(f) Disc(f)`, the non-Δ scalar is a power of `n`.  For even `n`, the same discriminant-power phenomenon holds for the x-division polynomial `preΨ'_n`; the exact integer scalar depends on normalization, but its prime factors are still among the primes dividing `n`.

For the Mazur application, this is exactly what is needed: `[W.IsElliptic]` gives `Δ ≠ 0`, and `(n : k) ≠ 0` makes the integer scalar a unit/nonzero in `k`.

---

## 3. `n = 5` over `y² = x³ + A x + B`

Let

```text
D = 4A³ + 27B²,
Δ = -16D.
```

The short-Weierstrass `ψ₅ = preΨ'_5` is

```text
f₅(X) = 5X¹² + 62A X¹⁰ + 380B X⁹ - 105A² X⁸ + 240AB X⁷
        - (300A³ + 240B²)X⁶ - 696A²B X⁵
        - (125A⁴ + 1920AB²)X⁴ - (80A³B + 1600B³)X³
        - (50A⁵ + 240A²B²)X² - (100A⁴B + 640AB³)X
        + A⁶ - 32A³B² - 256B⁴.
```

The resultant is

```text
Res_X(f₅, f₅') = 5¹² · Δ²² = 5¹² · 16²² · D²².
```

I computed and verified a **primitive smaller Bezout certificate**

```text
U₅ · f₅ + V₅ · f₅' = 20480 · D²²
                   = 2¹² · 5 · (4A³ + 27B²)²².
```

Multiplying both cofactors by

```text
G = 2⁷⁶ · 5¹¹ = 3689348814741910323200000000000
```

gives a certificate for the full Sylvester resultant `5¹²·Δ²²`.

The primitive cofactor table has:

```text
terms(U₅) = 216,   deg_X(U₅) = 10,
terms(V₅) = 236,   deg_X(V₅) = 11,
total terms = 452.
```

The exact table is encoded below as compressed JSON.  This is more robust than inlining 452 very large monomials in prose.  The decoder reconstructs `U₅,V₅` and verifies the identity in Sympy.

```python
import base64, json, lzma
import sympy as sp

X, A, B = sp.symbols('X A B')
D = 4*A**3 + 27*B**2

f5 = (
    5*X**12 + 62*A*X**10 + 380*B*X**9 - 105*A**2*X**8 + 240*A*B*X**7
    - (300*A**3 + 240*B**2)*X**6 - 696*A**2*B*X**5
    - (125*A**4 + 1920*A*B**2)*X**4 - (80*A**3*B + 1600*B**3)*X**3
    - (50*A**5 + 240*A**2*B**2)*X**2 - (100*A**4*B + 640*A*B**3)*X
    + A**6 - 32*A**3*B**2 - 256*B**4
)

payload_b64 = """
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
"""

payload = json.loads(lzma.decompress(base64.b64decode(payload_b64)).decode())
assert payload["term_format"] == ["which", "xpow", "Apow", "Bpow", "coeff_primitive"]

U5 = 0
V5 = 0
for which, xpow, Apow, Bpow, coeff in payload["terms"]:
    mon = coeff * A**Apow * B**Bpow * X**xpow
    if which == "a":
        U5 += mon
    elif which == "b":
        V5 += mon
    else:
        raise ValueError(which)

assert sp.expand(U5*f5 + V5*sp.diff(f5, X) - 20480*D**22) == 0
print("verified", len([t for t in payload["terms"] if t[0] == "a"]), len([t for t in payload["terms"] if t[0] == "b"]))
```

The JSON term format is:

```text
[which, xpow, Apow, Bpow, coeff_primitive]
```

so each row means

```text
coeff_primitive · A^Apow · B^Bpow · X^xpow
```

and `which = "a"` contributes to `U₅`, while `which = "b"` contributes to `V₅`.

---

## 4. Lean implementation strategy for per-`n`

The Lean side should not elaborate the expanded identity as a single polynomial expression.  Use a sparse certificate evaluator.

Skeleton:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

/-- A sparse term `c * A^a * B^b * X^i` for short-Weierstrass certificates. -/
structure ShortTerm where
  c : ℤ
  xpow : ℕ
  Apow : ℕ
  Bpow : ℕ

/-- Generated from the decoded payload. -/
def shortPsi5SepU_terms : List ShortTerm := by
  -- generated literal list, 216 terms
  exact []

/-- Generated from the decoded payload. -/
def shortPsi5SepV_terms : List ShortTerm := by
  -- generated literal list, 236 terms
  exact []

/-- Evaluate a sparse certificate term. -/
noncomputable def ShortTerm.eval (t : ShortTerm) : Polynomial (MvPolynomial (Fin 2) ℤ) :=
  Polynomial.C ((t.c : MvPolynomial (Fin 2) ℤ) *
    (MvPolynomial.X 0) ^ t.Apow * (MvPolynomial.X 1) ^ t.Bpow) * Polynomial.X ^ t.xpow

noncomputable def shortPsi5SepU : Polynomial (MvPolynomial (Fin 2) ℤ) :=
  (shortPsi5SepU_terms.map ShortTerm.eval).sum

noncomputable def shortPsi5SepV : Polynomial (MvPolynomial (Fin 2) ℤ) :=
  (shortPsi5SepV_terms.map ShortTerm.eval).sum

/-- Generated checker theorem. -/
theorem shortPsi5SepCert :
    shortPsi5SepU * shortPsi5 + shortPsi5SepV * derivative shortPsi5
      = Polynomial.C (20480 * (4 * A^3 + 27 * B^2)^22) := by
  -- Do not use `ring` on the fully expanded expression.
  -- Use a generated sparse normalizer or native_decide on coefficient maps.
  native_decide

end WeierstrassCurve
```

For the real long-Weierstrass path, replace `MvPolynomial (Fin 2) ℤ` by the chosen universal coefficient ring, and generate analogous sparse term tables.

---

## 5. Strategic recommendation

For the FLT/Mazur torsion bound, the fastest route is:

```text
1. Keep n=1,2 trivial.
2. Keep the existing n=3 Bezout proof.
3. Add n=4 from the existing cofactor/resultant certificate.
4. Generate n=5,6,7 next using the sparse certificate checker.
5. Benchmark n=8.
6. Only after the n=8 benchmark decide whether to generate n=9..16 universally.
```

If the universal long-Weierstrass certs for `n=9..16` become too large, use one of these mitigations:

* specialize to short Weierstrass in characteristic `0`/`≠2,3` if the Mazur statement permits it;
* generate certs in invariant variables rather than raw `a_i`;
* split by primes or by squarefree/separability facts if some indices can be reduced from smaller ones;
* keep the general projective-formula theorem as a later cleanup, not as the shortest path to the bound.

My current assessment: **per-`n` certificates are faster to formalize for the bound**, but they must be generated and checked as sparse data.  The general-`n` projective formula is more elegant and reusable, but it is not the shortest path to `|T| ≤ 16`.
