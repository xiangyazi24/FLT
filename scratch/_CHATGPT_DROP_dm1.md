# Q206-dm1: x-coordinate doubling identity for `Φ` / `ΨSq`

## Short diagnosis

The displayed cross-identity is the **right mathematical compatibility** of the x-coordinate division polynomials with the duplication map:

```lean
W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
  =
W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)
```

but the attempted proof is not a valid `ring` proof because, after rewriting only

```lean
W.ΨSq (2*m)
W.preΨ (2*m+1)
W.preΨ (2*m-1)
```

Lean treats the five neighboring symbols

```lean
W.preΨ (m-2), W.preΨ (m-1), W.preΨ m, W.preΨ (m+1), W.preΨ (m+2)
```

as algebraically independent.  They are not.  They satisfy the elliptic divisibility sequence identities.  The residual you see is not primarily a sign/index bug; it is the missing EDS relation layer.

So the failure of `ring` after those rewrites does **not** prove the desired identity is false.  It proves that the identity is not a formal consequence of just the three recurrences you expanded.

---

## 1. Is the identity raw in `R[X]` or only modulo the curve relation?

There are two levels.

### Bivariate classical level

Classically, the division polynomials live in `R[X,Y]`.  The duplication formula uses the Weierstrass equation to eliminate `Y`, especially through

```text
ψ₂² = Ψ₂Sq + 4 * (Weierstrass equation).
```

At this level, identities involving `ψ`, `φ`, and the duplication formula are naturally identities in the affine coordinate ring

```lean
R[X,Y] / (Y^2 + a₁XY + a₃Y - X^3 - a₂X^2 - a₄X - a₆).
```

Mathlib exposes exactly this bridge through coordinate-ring lemmas:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
WeierstrassCurve.C_Ψ₂Sq
WeierstrassCurve.ψ₂_sq
```

The docs state the key relation:

```lean
W.ψ₂ ^ 2 = Polynomial.C W.Ψ₂Sq + 4 * W.toAffine.polynomial
```

and also that `ΨSqₙ` and `Φₙ` are the univariate representatives congruent to `ψₙ²` and `φₙ` in the coordinate ring.

### Univariate `Φ` / `ΨSq` level

Once you use Mathlib's univariate definitions

```lean
W.Φ n
W.ΨSq n
```

the `Y`-elimination has already been built into the definitions.  Therefore the desired identity should be viewed as a **raw univariate polynomial identity** in the universal coefficient ring, hence after specialization in `R[X]`.

However, the clean Lean proof should not be a giant direct `ring` proof after opening only the `2m` recurrences.  It should be proved either:

1. projectively from the already-proved x-coordinate formula, or
2. in the coordinate ring using `mk_φ` / `mk_Ψ_sq`, then transported to the univariate representative if you have the needed injectivity/normal-form lemma.

---

## 2. The concrete bug in the attempted proof

Your proof expands:

```lean
hΦ2m : W.Φ (2 * m) = X * W.ΨSq (2 * m)
  - W.preΨ (2 * m + 1) * W.preΨ (2 * m - 1)

W.ΨSq_even m
W.preΨ_odd m
W.preΨ_odd (m - 1)
```

and then expands `W.Φ m` and `W.ΨSq m` by definition.

After the parity split, the goal is an identity in variables morally named:

```lean
A = W.preΨ (m - 2)
B = W.preΨ (m - 1)
C = W.preΨ m
D = W.preΨ (m + 1)
E = W.preΨ (m + 2)
Q = W.Ψ₂Sq
X = Polynomial.X
```

But the identity is not true for arbitrary independent `A B C D E Q X`.  It depends on the fact that these are consecutive terms of the same normalized EDS attached to `Q = Ψ₂Sq`, with initial data `Ψ₃` and `preΨ₄`.

That is why `ring` runs to completion and leaves a nonzero residual.

This is the same phenomenon as trying to prove an identity involving Fibonacci numbers after rewriting only

```text
F_{2m}, F_{2m+1}
```

but leaving

```text
F_{m-2}, F_{m-1}, F_m, F_{m+1}, F_{m+2}
```

as unrelated variables.  A polynomial residual is expected.

---

## 3. Correct Lean formulation: projective compatibility

The best target is not initially the cross-multiplied polynomial equality.  Prove the projective statement:

```lean
namespace DoublingTest

import Mathlib

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

noncomputable def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4
    - C W.b₄ * P ^ 2 * Q ^ 2
    - C (2 * W.b₆) * P * Q ^ 3
    - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q
    + C W.b₂ * P ^ 2 * Q ^ 2
    + C (2 * W.b₄) * P * Q ^ 3
    + C W.b₆ * Q ^ 4

/-- The projective x-coordinate pair attached to `n`. -/
def xPair (n : ℤ) : Fin 2 → R[X] :=
  ![W.Φ n, W.ΨSq n]

/-- The degree-4 homogeneous duplication map on projective x-coordinates. -/
def dupMap (v : Fin 2 → R[X]) : Fin 2 → R[X] :=
  ![dupNumP W (v 0) (v 1), dupDenP W (v 0) (v 1)]

/-- Projective compatibility of division-polynomial x-pairs with doubling. -/
theorem xPair_two_mul_same_dupMap (m : ℤ) :
    SameP1 (xPair W (2 * m)) (dupMap W (xPair W m)) := by
  -- This is the right theorem to prove from the x-coordinate formula, or from
  -- coordinate-ring division polynomial identities.
  sorry

/-- The cross product version follows from the projective statement. -/
theorem dup_doubling_cross_from_sameP1
    (m : ℤ)
    (h : SameP1 (xPair W (2 * m)) (dupMap W (xPair W m))) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      =
    W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  -- If `SameP1 v w` is represented by cross multiplication, this is immediate.
  -- If your `SameP1` is `∃ u : Units _, w = u • v`, destruct the unit and compare coordinates.
  -- For a pure cross-product definition, this is `simpa [xPair, dupMap] using h`.
  sorry

end DoublingTest
```

If your `SameP1` definition is the unit-scaling version

```lean
def SameP1 (v w : Fin 2 → A) : Prop := ∃ u : Aˣ, w = u • v
```

then the cross equality follows by destructing the unit:

```lean
lemma cross_eq_of_sameP1_unit
    {A : Type*} [CommRing A]
    {v w : Fin 2 → A}
    (h : SameP1 v w) :
    v 0 * w 1 = v 1 * w 0 := by
  rcases h with ⟨u, rfl⟩
  simp
  ring
```

If your `SameP1` is already determinant-zero/cross-product equality, the lemma is just unfolding.

---

## 4. Route A: prove it from the x-coordinate formula

If SEAM2 is available, this is the shortest non-circular route.

Assume you have:

```lean
theorem xRep_zsmul_same_xPair
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (n : ℤ) :
    SameP1
      ((n • (W.toAffine.Point.some x y h : W.toAffine.Point)).xRep)
      ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

and the x-only duplication formula for actual points:

```lean
theorem xRep_two_nsmul_same_dupMap
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) :
    SameP1
      ((2 • P).xRep)
      ![
        dupNumP_eval W (P.xRep 0) (P.xRep 1),
        dupDenP_eval W (P.xRep 0) (P.xRep 1)
      ]
```

Then for any affine `P`, compare two projective representatives of `x(2mP)`:

```lean
have h₁ := xRep_zsmul_same_xPair W hxy (2 * m)
have h₂ := xRep_zsmul_same_xPair W hxy m
have hdup := xRep_two_nsmul_same_dupMap W (m • Point.some x y hxy)
```

Use `h₂` plus homogeneity of `dupMap` to rewrite `dupMap ((m•P).xRep)` as

```lean
![dupNumP W ((W.Φ m).eval x) ((W.ΨSq m).eval x),
  dupDenP W ((W.Φ m).eval x) ((W.ΨSq m).eval x)]
```

and then transitivity of `SameP1` gives the projective identity pointwise over every algebraically closed field.  Finally convert pointwise polynomial equality to raw polynomial equality by the usual polynomial extensionality over an infinite field / universal specialization argument.

For the repo, I recommend stopping at the projective theorem unless the raw polynomial equality is explicitly needed.

---

## 5. Route B: coordinate ring formulation with `mk_φ` and `mk_Ψ_sq`

If you want to avoid using pointwise `xRep`, formulate the theorem in the affine coordinate ring first.

Schematic statement:

```lean
namespace DoublingTest.CoordinateRing

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Lift a univariate polynomial to the bivariate polynomial ring as a constant in `Y`. -/
abbrev Cx (p : R[X]) : Polynomial (Polynomial R) := Polynomial.C p

/-- Coordinate-ring version of the doubling compatibility. -/
theorem mk_dup_doubling_cross (m : ℤ) :
    WeierstrassCurve.Affine.CoordinateRing.mk W
      (Cx (W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
        - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)))
      = 0 := by
  -- Use:
  --   WeierstrassCurve.Affine.CoordinateRing.mk_φ
  --   WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
  --   WeierstrassCurve.ψ₂_sq / C_Ψ₂Sq
  -- and the bivariate division-polynomial recurrence for `ψ` / `φ`.
  -- This is where the curve equation is legitimately used.
  sorry

end DoublingTest.CoordinateRing
```

This is the right place to use:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_φ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.C_Ψ₂Sq
WeierstrassCurve.ψ₂_sq
```

Then, if you have or prove injectivity of the inclusion of univariate polynomials into the coordinate ring, you can descend to the raw `R[X]` identity.

The relevant injectivity lemma should look like:

```lean
theorem CoordinateRing.mk_C_injective
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    Function.Injective
      (fun p : R[X] =>
        WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C p)) := by
  -- Algebraically: the curve polynomial is monic in `Y`, so the quotient is free
  -- over `R[X]` with basis `1,Y`; constants in `Y` inject.
  sorry
```

If this injection lemma is not already available, it is a small standalone algebra lemma about quotienting by a monic quadratic in `Y`; it is much smaller than the division-polynomial identity itself.

---

## 6. Why the pure `ring` proof fails

The attempted proof says:

```lean
rw [hΦ2m, W.ΨSq_even m, W.preΨ_odd m, h2m1, W.preΨ_odd (m - 1)]
simp only [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq, dupNumP, dupDenP, ...]
rcases Int.even_or_odd m with hm | hm
...
ring
```

At this point, the goal still contains opaque terms such as:

```lean
W.preΨ (m - 2)
W.preΨ (m - 1)
W.preΨ m
W.preΨ (m + 1)
W.preΨ (m + 2)
```

They are not arbitrary variables.  The residual is a nontrivial consequence of the EDS recurrence relation, not of commutative-ring arithmetic.

Mathlib's EDS file defines:

```lean
IsEllSequence
IsDivSequence
IsEllDivSequence
preNormEDS'
preNormEDS
normEDS
complEDS
preNormEDS_even
preNormEDS_odd
normEDS_even
normEDS_odd
```

but its documentation still marks as TODO the proof that `normEDS` satisfies the expected elliptic divisibility sequence properties.  In particular, there is no ready theorem you can call that packages all higher EDS identities needed to make this residual vanish.

So the corrected low-level proof would need a new lemma of this kind:

```lean
theorem preΨ_five_term_duplication_residual
    (W : WeierstrassCurve R) (m : ℤ) :
    -- exactly the residual polynomial produced by your proof is zero
    True := by
  -- prove from the full EDS recurrence, not just the even/odd defining equations
  sorry
```

But this lemma is essentially the same difficulty as the target theorem.  It is not a good route.

---

## 7. Answer to the three concrete questions

### Q1. Raw polynomial identity or coordinate-ring identity?

The best mathematical answer is:

```text
The compatibility is naturally proved in the coordinate ring / rational function field.
After passing to Mathlib's univariate `Φ` and `ΨSq`, the relation should become a raw
univariate polynomial identity, because the curve relation has already been used to define
these univariate representatives.
```

So: it is not merely `mod curve` at the `Φ`/`ΨSq` level.  But a proof may legitimately go through the coordinate ring first.

### Q2. If raw, where is the bug?

The bug is not obviously a sign, index, or parity error.  The issue is that the proof expands only the `2m` recurrences and then asks `ring` to prove an identity that also depends on deeper EDS relations among the five neighboring terms around `m`.

Your recurrence rewrites may be individually correct, and the residual can still be nonzero as a polynomial in the uninterpreted neighboring terms.

### Q3. If coordinate-ring formulation is needed, what is the right Lean formulation?

Use:

```lean
theorem mk_dup_doubling_cross (m : ℤ) :
    WeierstrassCurve.Affine.CoordinateRing.mk W
      (Polynomial.C
        (W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
          - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)))
      = 0
```

and prove it with:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_φ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.ψ₂_sq
WeierstrassCurve.C_Ψ₂Sq
```

Then descend to raw `R[X]` using an injectivity lemma for `mk` on constants in `Y`.

If your immediate goal is SEAM2, the even better route is to avoid this standalone raw identity and prove the projective compatibility by composing already-proved `xRep` statements and the x-only duplication formula.

---

## Practical recommendation

Do not spend more time trying to make the current `ring` proof close.  It is missing a genuine EDS identity layer.

Use this priority order:

1. Prove the projective theorem `xPair_two_mul_same_dupMap` from SEAM2/xRep functoriality.
2. Derive the cross-product equality from projective equivalence if needed.
3. If a raw polynomial theorem is required for rewriting, prove the coordinate-ring version with `mk_φ`/`mk_Ψ_sq`, then use injectivity of univariate constants in the coordinate ring.
4. Avoid a direct `ring` proof after only expanding `preΨ_odd`/`ΨSq_even`; it treats EDS neighbors as independent and will continue producing a residual.
