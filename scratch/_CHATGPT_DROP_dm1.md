# Q229-dm4: EDS/Somos relation attack for the division-polynomial doubling identity

## Bottom line

The residual after expanding the raw duplication identity is exactly the missing EDS relation with indices

```text
(i,j,k) = (m,2,1)
```

in the general elliptic-sequence law

```text
ψ_{i+j} ψ_{i-j} ψ_k^2
  = ψ_{i+k} ψ_{i-k} ψ_j^2 - ψ_{j+k} ψ_{j-k} ψ_i^2.
```

Since `ψ₁ = 1`, `ψ₂² = Ψ₂Sq`, `ψ₃ = Ψ₃`, and `ψ₁` rather than `ψ_{-1}` appears in Mathlib's orientation, this specialization is

```text
ψ_{m+2} ψ_{m-2}
  = ψ_{m+1} ψ_{m-1} ψ₂² - ψ₃ ψ_m²,
```

or equivalently

```text
ψ_{m+2} ψ_{m-2} + ψ₃ ψ_m² = ψ_{m+1} ψ_{m-1} ψ₂².
```

For Mathlib's `preΨ` normalization, this becomes the following parity-normalized relation:

```lean
W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 =
  W.preΨ (m + 1) * W.preΨ (m - 1) *
    (if Even m then 1 else W.Ψ₂Sq ^ 2)
```

This is the concrete missing relation.  There is no current one-line Mathlib theorem named like
`preNormEDS_somos`, `normEDS_somos`, `IsEllSequence_normEDS`, or `preNormEDS_rel`.  Mathlib defines
`IsEllSequence`, `preNormEDS`, `normEDS`, `preNormEDS_even`, `preNormEDS_odd`, `normEDS_even`, and
`normEDS_odd`, but the file still says the theorem that `normEDS` satisfies `IsEllDivSequence` is TODO.  So add the relation locally.

---

## 1. The exact relation to add

Use a general sequence-level theorem first, then specialize to `W.preΨ`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- The concrete Somos/EDS relation for Mathlib's `preΨ` normalization.

This is the normalized form of
`ψ_{m+2} ψ_{m-2} + ψ₃ ψ_m^2 = ψ_{m+1} ψ_{m-1} ψ₂^2`.
When `m` is even, the factors of `ψ₂²` cancel in the normalized univariate sequence.
When `m` is odd, both `m+1` and `m-1` are even, so the right side picks up `Ψ₂Sq^2`.
-/
theorem preΨ_somos_1_2 (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 =
      W.preΨ (m + 1) * W.preΨ (m - 1) *
        (if Even m then 1 else W.Ψ₂Sq ^ 2) := by
  /-
  This theorem is not currently in Mathlib.  It should be proved once in
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, in a general form for
  `preNormEDS`, by induction using `normEDSRec` or `preNormEDS_even`/`preNormEDS_odd`.

  General target before specialization:

    theorem preNormEDS_somos_1_2
        {R : Type*} [CommRing R] (q c d : R) (m : ℤ) :
        preNormEDS q c d (m + 2) * preNormEDS q c d (m - 2) +
          c * preNormEDS q c d m ^ 2 =
        preNormEDS q c d (m + 1) * preNormEDS q c d (m - 1) *
          (if Even m then 1 else q) := ...

  Since `W.preΨ n = preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`, substituting
  `q = W.Ψ₂Sq ^ 2` gives the displayed theorem.

  The proof is finite EDS algebra.  The base cases `m = 0, ±1, ±2, ±3, ±4` close by `simp`.
  The induction steps split by parity and rewrite the terms at `2*t` and `2*t+1` using
  `preNormEDS_even` and `preNormEDS_odd`; the residuals close with the induction hypotheses at
  `t-1`, `t`, and `t+1` plus `ring1`.
  -/
  sorry

/-- Even-parity spelling used by `rw [if_pos hm]`. -/
theorem preΨ_somos_1_2_even {m : ℤ} (hm : Even m) :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 =
      W.preΨ (m + 1) * W.preΨ (m - 1) := by
  simpa [hm] using W.preΨ_somos_1_2 m

/-- Odd-parity spelling used by `rw [if_neg hm]`. -/
theorem preΨ_somos_1_2_odd {m : ℤ} (hm : ¬ Even m) :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 =
      W.preΨ (m + 1) * W.preΨ (m - 1) * W.Ψ₂Sq ^ 2 := by
  simpa [hm] using W.preΨ_somos_1_2 m

end WeierstrassCurve
```

### Index check

Mathlib's `IsEllSequence` is oriented as

```lean
W (m + n) * W (m - n) * W r ^ 2 =
  W (m + r) * W (m - r) * W n ^ 2 -
    W (n + r) * W (n - r) * W m ^ 2
```

With `n=2`, `r=1`, this gives

```text
ψ_{m+2}ψ_{m-2}
  = ψ_{m+1}ψ_{m-1}ψ₂² - ψ₃ψ₁ψ_m².
```

Since `ψ₁ = 1`, the correct Mathlib-specialized relation is:

```text
ψ_{m+2} ψ_{m-2} + ψ₃ ψ_m² = ψ_{m+1} ψ_{m-1} ψ₂².
```

That is the relation used above.

---

## 2. The raw duplication polynomial definitions

```lean
namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

noncomputable def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4 - C W.b₄ * P ^ 2 * Q ^ 2 - C (2 * W.b₆) * P * Q ^ 3 - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : R[X]) : R[X] :=
  C (4 : R) * P ^ 3 * Q + C W.b₂ * P ^ 2 * Q ^ 2 +
    C (2 * W.b₄) * P * Q ^ 3 + C W.b₆ * Q ^ 4

end WeierstrassCurve
```

The target identity is:

```lean
namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Raw projective duplication identity for division-polynomial coordinates. -/
theorem Φ_two_mul_mul_dupDenP_eq_ΨSq_two_mul_mul_dupNumP (m : ℤ) :
    W.Φ (2 * m) * W.dupDenP (W.Φ m) (W.ΨSq m) =
      W.ΨSq (2 * m) * W.dupNumP (W.Φ m) (W.ΨSq m) := by
  classical
  by_cases hm : Even m
  · -- even `m`
    /-
    1. Rewrite:
       `W.ΨSq m`, `W.Φ m`, `W.ΨSq (2*m)`, `W.Φ (2*m)`.
    2. Rewrite `W.preΨ (2*m)` by `W.preΨ_even m`.
    3. Rewrite `W.preΨ (2*m+1)` by `W.preΨ_odd m`.
    4. Rewrite `W.preΨ (2*m-1)` by `W.preΨ_odd (m-1)`.
    5. Simplify parity using `hm` and `Int.not_even_iff_odd` / `even_sub` facts.
    6. Close by one linear combination of the EDS relation
       `W.preΨ_somos_1_2_even hm` and the `b`-invariant relation.
    -/
    sorry
  · -- odd `m`
    /-
    Same proof, but the EDS relation is `W.preΨ_somos_1_2_odd hm`.
    -/
    sorry

end WeierstrassCurve
```

---

## 3. The concrete residual relation in local variable form

After the standard rewrites, name the five adjacent terms and `q`:

```text
a = W.preΨ (m - 2)
b = W.preΨ (m - 1)
c = W.preΨ m
d = W.preΨ (m + 1)
e = W.preΨ (m + 2)
q = W.Ψ₂Sq
p3 = W.Ψ₃
```

The only EDS relation needed is:

### even `m`

```text
e*a + p3*c^2 - d*b = 0.
```

Lean spelling:

```lean
have hEDS :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 -
      W.preΨ (m + 1) * W.preΨ (m - 1) = 0 := by
  linear_combination (norm := ring1) W.preΨ_somos_1_2_even hm
```

### odd `m`

```text
e*a + p3*c^2 - q^2*d*b = 0.
```

Lean spelling:

```lean
have hEDS :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 -
      W.preΨ (m + 1) * W.preΨ (m - 1) * W.Ψ₂Sq ^ 2 = 0 := by
  linear_combination (norm := ring1) W.preΨ_somos_1_2_odd hm
```

Also expose the two curve-polynomial coefficient relations to `ring`:

```lean
-- `Ψ₂Sq` definition
rw [WeierstrassCurve.Ψ₂Sq]

-- b-invariant relation; Mathlib uses this name in the elliptic-curve files.
-- If the local goal is in `R`, use:
have hb : W.b₂ * W.b₆ = W.b₄ ^ 2 + 4 * W.b₈ := by
  simpa using W.b_relation

-- If the local goal is in `R[X]`, use the polynomial-cast version:
have hbC : C (W.b₂ * W.b₆) = C (W.b₄ ^ 2 + 4 * W.b₈ : R) := by
  exact congrArg C hb
```

If your goal has `4 * C W.b₈`, `C (4 * W.b₈)`, or `C W.b₄ ^ 2`, normalize before `linear_combination`:

```lean
simp only [map_mul, map_add, map_pow, map_ofNat] at hbC
```

---

## 4. Closing tactic pattern

The exact human tactic is:

```lean
  -- after all unfold/rw/parity simplification
  have hEDS : ... = 0 := by
    linear_combination (norm := ring1) W.preΨ_somos_1_2_even hm

  have hb : W.b₂ * W.b₆ = W.b₄ ^ 2 + 4 * W.b₈ := by
    simpa using W.b_relation

  -- For a polynomial goal over `R[X]`, push `hb` through `C`.
  have hbC : C (W.b₂ * W.b₆) = C (W.b₄ ^ 2 + 4 * W.b₈ : R) := by
    exact congrArg C hb

  -- The final residual is in the ideal generated by `hEDS` and `hbC`.
  -- If `linear_combination` can find the scalar cofactors itself:
  linear_combination (norm := ring1) F₁ * hEDS + F₂ * hbC
```

In many cases, after fully unfolding `b₂ b₄ b₆ b₈` to `aᵢ`, `hbC` is unnecessary and `ring1` handles it.  Then the final line is simply:

```lean
  linear_combination (norm := ring1) F * hEDS
```

where `F` is the cofactor of the residual by the EDS relation.

I do **not** recommend trying to hand-write `F`.  It is large and brittle.  Compute it once from the post-rewrite residual and paste it if necessary.

---

## 5. Precise method to compute the cofactor(s)

The robust method is to instrument the Lean proof to print the post-rewrite goal as a polynomial identity in symbolic variables, then compute the quotient by the EDS relation in Sage/Singular.

Use the following symbolic variables:

```text
x,b2,b4,b6,b8,q,a,b,c,d,e
```

with abbreviations:

```text
a = preΨ(m-2), b = preΨ(m-1), c = preΨ(m), d = preΨ(m+1), e = preΨ(m+2)
q = Ψ₂Sq
p3 = 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8
A  = b^2*e - a*d^2                         -- preΨ(2m)/preΨ(m)
```

Even case:

```text
Ψm      = c^2*q
Φm      = x*c^2*q - d*b
pre2m1  = e*c^3*q^2 - b*d^3
pre2m_1 = d*b^3 - a*c^3*q^2
Ψ2m     = c^2*A^2*q
Φ2m     = x*c^2*A^2*q - pre2m1*pre2m_1
REDS    = e*a + p3*c^2 - d*b
```

Odd case:

```text
Ψm      = c^2
Φm      = x*c^2 - d*b*q
pre2m1  = e*c^3 - b*d^3*q^2
pre2m_1 = d*b^3*q^2 - a*c^3
Ψ2m     = c^2*A^2*q
Φ2m     = x*c^2*A^2*q - pre2m1*pre2m_1
REDS    = e*a + p3*c^2 - q^2*d*b
```

Common duplication polynomials:

```text
dupNum(P,Q) = P^4 - b4*P^2*Q^2 - 2*b6*P*Q^3 - b8*Q^4

dupDen(P,Q) = 4*P^3*Q + b2*P^2*Q^2 + 2*b4*P*Q^3 + b6*Q^4
```

Common coefficient relations:

```text
Rq  = q - (4*x^3 + b2*x^2 + 2*b4*x + b6)
Rb8 = 4*b8 - (b2*b6 - b4^2)
```

Sage/Singular computation:

```python
R.<x,b2,b4,b6,b8,q,a,b,c,d,e> = PolynomialRing(QQ, order='degrevlex')

p3 = 3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8
A  = b^2*e - a*d^2

def dupNum(P,Q):
    return P^4 - b4*P^2*Q^2 - 2*b6*P*Q^3 - b8*Q^4

def dupDen(P,Q):
    return 4*P^3*Q + b2*P^2*Q^2 + 2*b4*P*Q^3 + b6*Q^4

Rq  = q - (4*x^3 + b2*x^2 + 2*b4*x + b6)
Rb8 = 4*b8 - (b2*b6 - b4^2)

# even case
Psi_m      = c^2*q
Phi_m      = x*c^2*q - d*b
pre2m1     = e*c^3*q^2 - b*d^3
pre2m_1    = d*b^3 - a*c^3*q^2
Psi_2m     = c^2*A^2*q
Phi_2m     = x*c^2*A^2*q - pre2m1*pre2m_1
REDS_even  = e*a + p3*c^2 - d*b
Residual_even = expand(Phi_2m*dupDen(Phi_m,Psi_m) - Psi_2m*dupNum(Phi_m,Psi_m))

I_even = ideal([REDS_even, Rq, Rb8])
assert Residual_even.reduce(I_even.groebner_basis()) == 0
# To get cofactors, use Singular's lift:
#   lift(matrix(gens), matrix([Residual_even]))

# odd case
Psi_m      = c^2
Phi_m      = x*c^2 - d*b*q
pre2m1     = e*c^3 - b*d^3*q^2
pre2m_1    = d*b^3*q^2 - a*c^3
Psi_2m     = c^2*A^2*q
Phi_2m     = x*c^2*A^2*q - pre2m1*pre2m_1
REDS_odd   = e*a + p3*c^2 - q^2*d*b
Residual_odd = expand(Phi_2m*dupDen(Phi_m,Psi_m) - Psi_2m*dupNum(Phi_m,Psi_m))

I_odd = ideal([REDS_odd, Rq, Rb8])
assert Residual_odd.reduce(I_odd.groebner_basis()) == 0
# Again use Singular lift for cofactors.
```

Then translate the lift output into Lean:

```lean
linear_combination (norm := ring1)
  Feds * hEDS + Fq * hq + Fb8 * hbC
```

where:

```lean
hEDS : REDS = 0
hq   : W.Ψ₂Sq - (4*X^3 + C W.b₂*X^2 + C(2*W.b₄)*X + C W.b₆) = 0
hbC  : C (4 * W.b₈) - C (W.b₂ * W.b₆ - W.b₄^2) = 0
```

In practice, if the Lean proof already unfolds `W.Ψ₂Sq` and the `bᵢ` invariants to `aᵢ`, then `Fq` and `Fb8` disappear and only the `Feds * hEDS` term remains.

---

## 6. Recommended Lean attack layout

Do not try to prove the full identity in one `ring` call.  Add exactly these local lemmas:

```lean
namespace WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

-- 1. Missing EDS relation.
theorem preΨ_somos_1_2 (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2) + W.Ψ₃ * W.preΨ m ^ 2 =
      W.preΨ (m + 1) * W.preΨ (m - 1) *
        (if Even m then 1 else W.Ψ₂Sq ^ 2) := by
  sorry

-- 2. Duplication identity with parity split.
theorem Φ_two_mul_mul_dupDenP_eq_ΨSq_two_mul_mul_dupNumP (m : ℤ) :
    W.Φ (2 * m) * W.dupDenP (W.Φ m) (W.ΨSq m) =
      W.ΨSq (2 * m) * W.dupNumP (W.Φ m) (W.ΨSq m) := by
  classical
  by_cases hm : Even m
  · have hEDS := W.preΨ_somos_1_2_even hm
    -- rewrite `ΨSq`, `Φ`, `preΨ_even`, `preΨ_odd`, parity; then:
    -- linear_combination (norm := ring1) F_even * hEDS
    sorry
  · have hEDS := W.preΨ_somos_1_2_odd hm
    -- same with odd formulas; then:
    -- linear_combination (norm := ring1) F_odd * hEDS
    sorry

end WeierstrassCurve
```

The important point is that there are not many hidden EDS relations.  The needed relation is the single adjacent-index Somos relation `preΨ_somos_1_2`; the rest is coefficient algebra.
