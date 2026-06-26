# Q820 (dm4): exact Mathlib expansion of `WeierstrassCurve.preΨ₄`

## Checked Mathlib revision

I checked `leanprover-community/mathlib4` at the requested pinned rev `96fd0fff`.

The relevant files are:

```text
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean
Mathlib/FieldTheory/Separable.lean
```

## 1. Exact Mathlib definition of `preΨ₄`

Yes, `WeierstrassCurve.preΨ₄` is explicitly defined as a univariate polynomial in `X`, with coefficients expressed through the standard `bᵢ` invariants.

At rev `96fd0fff`, the definition is exactly:

```lean
/-- The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ψ₂`. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)
```

So, in mathematical notation:

```text
preΨ₄(x) = 2x⁶ + b₂x⁵ + 5b₄x⁴ + 10b₆x³ + 10b₈x²
           + (b₂b₈ - b₄b₆)x + (b₄b₈ - b₆²).
```

The `bᵢ` invariants are also explicit in Mathlib:

```lean
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂

def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃

def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆

def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
```

and Mathlib has the useful relation

```lean
lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
```

## Fully expanded in `a₁,a₂,a₃,a₄,a₆`

Substituting the `bᵢ` definitions, the polynomial is:

```text
preΨ₄(x) =
  2*x^6
  + (a1^2 + 4*a2)*x^5
  + (5*a1*a3 + 10*a4)*x^4
  + (10*a3^2 + 40*a6)*x^3
  + (10*a1^2*a6 - 10*a1*a3*a4 + 10*a2*a3^2 + 40*a2*a6 - 10*a4^2)*x^2
  + (a1^4*a6 - a1^3*a3*a4 + a1^2*a2*a3^2 + 8*a1^2*a2*a6
     - a1^2*a4^2 - 4*a1*a2*a3*a4 - a1*a3^3 - 4*a1*a3*a6
     + 4*a2^2*a3^2 + 16*a2^2*a6 - 4*a2*a4^2 - 2*a3^2*a4 - 8*a4*a6)*x
  + (a1^3*a3*a6 - a1^2*a3^2*a4 + 2*a1^2*a4*a6
     + a1*a2*a3^3 + 4*a1*a2*a3*a6 - 3*a1*a3*a4^2
     + 2*a2*a3^2*a4 + 8*a2*a4*a6
     - a3^4 - 8*a3^2*a6 - 2*a4^3 - 16*a6^2).
```

For Lean, I would normally keep the `bᵢ` form.  It is much smaller, it matches Mathlib definitional unfolding, and it exposes `b_relation`, which is useful for the Bézout certificate below.

## 2. What is `preΨ'(4)`?

Mathlib defines

```lean
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

and has the simp lemma:

```lean
@[simp]
lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ :=
  preNormEDS'_four ..
```

So yes: `preΨ'_four` exists, and it is tagged `@[simp]`.

For proofs, this means that goals involving `W.preΨ' 4` should reduce to `W.preΨ₄` by `simp`.

## 3. Degree of `preΨ₄`

Mathlib proves the unconditional upper bound and the exact degree under `(2 : R) ≠ 0`:

```lean
lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

lemma coeff_preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄.coeff 6 ≠ 0 := by
  rwa [coeff_preΨ₄]

@[simp]
lemma natDegree_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le <| W.coeff_preΨ₄_ne_zero h

@[simp]
lemma leadingCoeff_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.leadingCoeff = 2 := by
  rw [leadingCoeff, W.natDegree_preΨ₄ h, coeff_preΨ₄]
```

So the degree is `6` when `(2 : R) ≠ 0`.  In your theorem for `n = 4`, the hypothesis `(4 : K) ≠ 0` over a field implies `(2 : K) ≠ 0`, so this applies.

## About `Polynomial.Separable` and `decide`

Mathlib defines polynomial separability as a coprimality proposition:

```lean
def Polynomial.Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)

theorem separable_def' (f : R[X]) :
  f.Separable ↔ ∃ a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl
```

I would not expect `decide` to close `W.preΨ₄.Separable` in the symbolic setting.  Even if propositions are classically decidable, `decide` is not going to synthesize a nontrivial Bézout certificate over coefficients involving symbolic `W.a₁,...,W.a₆` and the ellipticity hypothesis.  The right Lean route is an explicit certificate, then normalize a nonzero constant to `1` using the field inverse/unit argument.

## Better certificate target than the raw resultant

A direct resultant computation is possible.  For the actual `preΨ₄` polynomial `p`, over the Weierstrass invariant relation, the resultant satisfies

```text
resultant(p, p') = 512 * Δ^5.
```

But for Lean, a smaller certificate is more useful.  Use `b_relation` to replace `4*b₈` by `b₂*b₆ - b₄²`, and define

```text
q := 4 * preΨ₄.
```

Then, after eliminating `b₈`,

```text
q(x) =
  8*x^6
  + 4*b2*x^5
  + 20*b4*x^4
  + 40*b6*x^3
  + 10*(b2*b6 - b4^2)*x^2
  + (b2^2*b6 - b2*b4^2 - 4*b4*b6)*x
  + (b2*b4*b6 - b4^3 - 4*b6^2).
```

Let

```text
D := b2^3*b6 - b2^2*b4^2 - 36*b2*b4*b6 + 32*b4^3 + 108*b6^2.
```

Using Mathlib’s discriminant convention and `b_relation`, this is

```text
D = -4 * Δ.
```

A compact Bézout certificate is:

```text
(-S) * q + T * q' = 2 * D^2,
```

where

```text
S =
  69*b2^3*b6 + 50*b2^3*x^3 - 69*b2^2*b4^2 + 150*b2^2*b4*x^2
  + 210*b2^2*b6*x + 120*b2^2*x^4 - 60*b2*b4^2*x - 2274*b2*b4*b6
  - 1320*b2*b4*x^3 + 540*b2*b6*x^2 + 2048*b4^3 - 4320*b4^2*x^2
  - 3960*b4*b6*x - 2880*b4*x^4 + 5832*b6^2 + 2160*b6*x^3
```

and

```text
T =
  2*b2^4*b6 - 2*b2^3*b4^2 + 29*b2^3*b6*x + 10*b2^3*x^4
  - 29*b2^2*b4^2*x - 67*b2^2*b4*b6 + 40*b2^2*b4*x^3
  + 80*b2^2*b6*x^2 + 20*b2^2*x^5 + 59*b2*b4^3 - 20*b2*b4^2*x^2
  - 884*b2*b4*b6*x - 260*b2*b4*x^4 + 156*b2*b6^2 + 120*b2*b6*x^3
  + 808*b4^3*x + 50*b4^2*b6 - 1120*b4^2*x^3 - 1560*b4*b6*x^2
  - 480*b4*x^5 + 1872*b6^2*x + 360*b6*x^4.
```

This is probably the best Lean certificate shape:

1. Prove `q = 4 • W.preΨ₄` by unfolding `preΨ₄` and using `W.b_relation`.
2. Prove `(-S) * q + T * derivative q = C (2 * D^2)` by `ring_nf` after unfolding `q`, `S`, `T`, `D`.
3. Prove `D = -4 * W.Δ` by unfolding `D`, `Δ`, and using `W.b_relation` or the already unfolded expression.
4. Since `[Field K]`, `[W.IsElliptic]`, and `(4 : K) ≠ 0`, the constant `2 * D^2 = 32 * W.Δ^2` is nonzero, hence a unit.
5. Convert the certificate for `q` to one for `preΨ₄`, because `q = 4 * preΨ₄` and `4` is a unit.

This avoids producing the much larger `512 * Δ^5` resultant certificate.

## SymPy script

This script does four things:

1. defines Mathlib’s `preΨ₄`,
2. expands it in `a₁,...,a₆`,
3. computes derivative and resultant,
4. computes/prints the compact Bézout certificate above after eliminating `b₈` using `4*b₈ = b₂*b₆ - b₄²`.

```python
#!/usr/bin/env python3
import sympy as sp

# Main polynomial variable.
x = sp.symbols("x")

# Weierstrass coefficients.
a1, a2, a3, a4, a6 = sp.symbols("a1 a2 a3 a4 a6")

# Standard b-invariants, matching Mathlib's WeierstrassCurve.b₂, b₄, b₆, b₈.
b2_a = a1**2 + 4*a2
b4_a = 2*a4 + a1*a3
b6_a = a3**2 + 4*a6
b8_a = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

# Independent b-symbols.  For the compact certificate we use the Weierstrass
# relation 4*b8 = b2*b6 - b4^2 and eliminate b8.
b2, b4, b6, b8 = sp.symbols("b2 b4 b6 b8")

# Mathlib's preΨ₄ in b-invariant form.
pre4_b = (
    2*x**6
    + b2*x**5
    + 5*b4*x**4
    + 10*b6*x**3
    + 10*b8*x**2
    + (b2*b8 - b4*b6)*x
    + (b4*b8 - b6**2)
)

# Same polynomial expanded in a_i.
pre4_a = sp.expand(pre4_b.subs({b2: b2_a, b4: b4_a, b6: b6_a, b8: b8_a}))

dpre4_b = sp.diff(pre4_b, x)
dpre4_a = sp.diff(pre4_a, x)

print("prePsi4 in b-invariants:")
print(sp.Poly(pre4_b, x))
print()

print("prePsi4 expanded in a_i:")
print(sp.Poly(pre4_a, x))
print()

print("derivative in b-invariants:")
print(sp.Poly(dpre4_b, x))
print()

# If b2,b4,b6,b8 are treated as independent, the resultant is huge and does not
# reflect the Weierstrass relation.  Use b8 = (b2*b6 - b4^2)/4.
b8_rel = (b2*b6 - b4**2) / 4
pre4_rel = sp.expand(pre4_b.subs(b8, b8_rel))

# Work with q = 4*preΨ₄ after relation, to keep integral coefficients.
q = sp.expand(4 * pre4_rel)
dq = sp.diff(q, x)

D = b2**3*b6 - b2**2*b4**2 - 36*b2*b4*b6 + 32*b4**3 + 108*b6**2

print("q = 4*prePsi4 after eliminating b8:")
print(sp.Poly(q, x))
print()

print("D =")
print(D)
print()

# GCD and extended GCD over QQ(b2,b4,b6)[x].
K = sp.QQ.frac_field(b2, b4, b6)
Q = sp.Poly(q, x, domain=K)
DQ = sp.Poly(dq, x, domain=K)

g = sp.gcd(Q, DQ)
print("gcd(q, q') over QQ(b2,b4,b6)[x] =")
print(g)
print()

s, t, h = sp.gcdex(Q, DQ)  # s*q + t*q' = h
print("extended gcd h =")
print(h)
print()
print("s =")
print(sp.factor(s.as_expr()))
print()
print("t =")
print(sp.factor(t.as_expr()))
print()

# Compact denominator-cleared cofactors.
S = (
    69*b2**3*b6 + 50*b2**3*x**3 - 69*b2**2*b4**2 + 150*b2**2*b4*x**2
    + 210*b2**2*b6*x + 120*b2**2*x**4 - 60*b2*b4**2*x - 2274*b2*b4*b6
    - 1320*b2*b4*x**3 + 540*b2*b6*x**2 + 2048*b4**3 - 4320*b4**2*x**2
    - 3960*b4*b6*x - 2880*b4*x**4 + 5832*b6**2 + 2160*b6*x**3
)

T = (
    2*b2**4*b6 - 2*b2**3*b4**2 + 29*b2**3*b6*x + 10*b2**3*x**4
    - 29*b2**2*b4**2*x - 67*b2**2*b4*b6 + 40*b2**2*b4*x**3
    + 80*b2**2*b6*x**2 + 20*b2**2*x**5 + 59*b2*b4**3 - 20*b2*b4**2*x**2
    - 884*b2*b4*b6*x - 260*b2*b4*x**4 + 156*b2*b6**2 + 120*b2*b6*x**3
    + 808*b4**3*x + 50*b4**2*b6 - 1120*b4**2*x**3 - 1560*b4*b6*x**2
    - 480*b4*x**5 + 1872*b6**2*x + 360*b6*x**4
)

cert = sp.expand((-S)*q + T*dq - 2*D**2)
print("certificate check (-S)*q + T*q' - 2*D^2 =")
print(sp.factor(cert))
print()

# Resultant check.  For p = preΨ₄, resultant(p,p') = 512*Δ^5.
# For q = 4*p, resultant(q,q') = 4^11 * resultant(p,p').
res_q = sp.factor(sp.resultant(q, dq, x))
print("resultant(q, q') =")
print(res_q)
print()
print("resultant(q, q') / D^5 =")
print(sp.factor(res_q / D**5))
print()

# Relation with Mathlib's discriminant convention:
# Δ = -D/4 after eliminating b8.
Delta_rel = -D/4
res_pre4 = sp.factor(res_q / (4**11))
print("resultant(prePsi4, derivative prePsi4) =")
print(res_pre4)
print()
print("resultant(prePsi4, derivative prePsi4) / Delta^5 =")
print(sp.factor(res_pre4 / Delta_rel**5))
```

Expected important output:

```text
gcd(q, q') over QQ(b2,b4,b6)[x] = Poly(1, x, domain='QQ(b2,b4,b6)')

certificate check (-S)*q + T*q' - 2*D^2 =
0

resultant(q, q') / D^5 =
-2097152

resultant(prePsi4, derivative prePsi4) / Delta^5 =
512
```

The sign in `resultant(q,q') / D^5` is negative because `D = -4Δ`; since the exponent is `5`, this matches the positive `512*Δ^5` for `preΨ₄`.

## Lean proof sketch for `preΨ₄.Separable`

A Lean-friendly proof should avoid the full resultant and use the compact certificate.

Schematic shape:

```lean
-- Define the b-only eliminated polynomial q = 4 * preΨ₄.
private noncomputable def preΨ₄_q (W : WeierstrassCurve K) : K[X] :=
  8 * X ^ 6
    + 4 * C W.b₂ * X ^ 5
    + 20 * C W.b₄ * X ^ 4
    + 40 * C W.b₆ * X ^ 3
    + 10 * C (W.b₂ * W.b₆ - W.b₄ ^ 2) * X ^ 2
    + C (W.b₂ ^ 2 * W.b₆ - W.b₂ * W.b₄ ^ 2 - 4 * W.b₄ * W.b₆) * X
    + C (W.b₂ * W.b₄ * W.b₆ - W.b₄ ^ 3 - 4 * W.b₆ ^ 2)

private def preΨ₄_D (W : WeierstrassCurve K) : K :=
  W.b₂ ^ 3 * W.b₆ - W.b₂ ^ 2 * W.b₄ ^ 2
    - 36 * W.b₂ * W.b₄ * W.b₆ + 32 * W.b₄ ^ 3 + 108 * W.b₆ ^ 2
```

Then prove:

```lean
private lemma preΨ₄_q_eq_four_mul (W : WeierstrassCurve K) :
    preΨ₄_q W = C (4 : K) * W.preΨ₄ := by
  rw [preΨ₄_q, preΨ₄]
  -- use W.b_relation to eliminate b₈
  -- ring_nf should finish after rewriting `4 * W.b₈`.
  sorry

private lemma preΨ₄_D_eq_neg_four_delta (W : WeierstrassCurve K) :
    preΨ₄_D W = -4 * W.Δ := by
  rw [preΨ₄_D, Δ]
  -- either unfold b_relation or use it; ring_nf.
  sorry

private lemma preΨ₄_q_bezout (W : WeierstrassCurve K) :
    ∃ A B : K[X],
      A * preΨ₄_q W + B * derivative (preΨ₄_q W) = C (2 * preΨ₄_D W ^ 2) := by
  refine ⟨-S_poly W, T_poly W, ?_⟩
  -- `S_poly` and `T_poly` are the polynomial cofactors listed above.
  -- Unfold q, S, T, D and use ring_nf.
  sorry
```

Finally, under `[Field K]`, `[W.IsElliptic]`, and `(4 : K) ≠ 0`:

```lean
have h2 : (2 : K) ≠ 0 := by
  -- from `(4 : K) ≠ 0`; in a field, if 2 = 0 then 4 = 0.
  sorry
have hD : preΨ₄_D W ≠ 0 := by
  rw [preΨ₄_D_eq_neg_four_delta]
  -- `W.IsElliptic` gives `W.Δ ≠ 0`, and `4 ≠ 0`.
  sorry
have hconst : IsUnit (2 * preΨ₄_D W ^ 2) := by
  exact isUnit_iff_ne_zero.mpr (by field_simp [h2, hD])
```

Normalize the certificate by multiplying both cofactors by the inverse of the constant.  This gives `IsCoprime (preΨ₄_q W) (derivative (preΨ₄_q W))`, hence separability of `preΨ₄_q W`.  Since `preΨ₄_q W = C 4 * W.preΨ₄` and `C 4` is a unit, transfer separability back to `W.preΨ₄`.

This should be much more tractable than asking Lean to discover separability automatically.
