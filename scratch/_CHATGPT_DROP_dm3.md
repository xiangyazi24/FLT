# Q185 (dm3): Mathlib survey for `n • P = 0 ↔ ΨSqₙ(x(P)) = 0`

Bottom line: current Mathlib has a useful **definition layer** for elliptic divisibility sequences and Weierstrass division polynomials, but I do **not** see a shortcut theorem connecting those polynomials to the actual affine point group law.  In particular, I do not see an existing declaration of the form

```lean
x (n • P) = Φₙ(x P) / ΨSqₙ(x P)
```

or

```lean
n • P = 0 ↔ IsRoot (W.ΨSq n) (x P)
```

or

```lean
n • P = 0 ↔ eval₂ ... (W.ψ n) x y = 0
```

So the hand-rolled x-only ladder remains the shortest route unless a new bridge theorem is built.

## 1. What Mathlib has

The relevant imports are:

```lean
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
```

### EDS layer

Mathlib has the EDS recurrence infrastructure:

```lean
#check IsEllSequence
#check IsDivSequence
#check IsEllDivSequence

#check preNormEDS'
#check preNormEDS
#check preNormEDS'_zero
#check preNormEDS'_one
#check preNormEDS'_two
#check preNormEDS'_three
#check preNormEDS'_four
#check preNormEDS'_even
#check preNormEDS'_odd
#check preNormEDS_zero
#check preNormEDS_one
#check preNormEDS_two
#check preNormEDS_three
#check preNormEDS_four
#check preNormEDS_even
#check preNormEDS_odd

#check complEDS₂
#check preNormEDS_mul_complEDS₂

#check normEDS
#check normEDS_zero
#check normEDS_one
#check normEDS_two
#check normEDS_three
#check normEDS_four
#check normEDS_neg
#check normEDS_even
#check normEDS_odd
#check normEDSRec'
#check normEDSRec
```

Important caveat: the file documentation still says the main EDS theorem is TODO:

```text
TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.
```

So this is recurrence infrastructure, not a completed arithmetic theory of EDSs.

### Weierstrass division-polynomial layer

Mathlib has the following Weierstrass division-polynomial declarations:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

open Polynomial
open scoped Polynomial.Bivariate

#check WeierstrassCurve.ψ₂
#check WeierstrassCurve.Ψ₂Sq
#check WeierstrassCurve.C_Ψ₂Sq
#check WeierstrassCurve.ψ₂_sq
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq
#check WeierstrassCurve.Ψ₂Sq_eq

#check WeierstrassCurve.Ψ₃
#check WeierstrassCurve.preΨ₄

#check WeierstrassCurve.preΨ'
#check WeierstrassCurve.preΨ'_zero
#check WeierstrassCurve.preΨ'_one
#check WeierstrassCurve.preΨ'_two
#check WeierstrassCurve.preΨ'_three
#check WeierstrassCurve.preΨ'_four
#check WeierstrassCurve.preΨ'_even
#check WeierstrassCurve.preΨ'_odd

#check WeierstrassCurve.preΨ
#check WeierstrassCurve.preΨ_zero
#check WeierstrassCurve.preΨ_one
#check WeierstrassCurve.preΨ_two
#check WeierstrassCurve.preΨ_three
#check WeierstrassCurve.preΨ_four
#check WeierstrassCurve.preΨ_neg
#check WeierstrassCurve.preΨ_even
#check WeierstrassCurve.preΨ_odd

#check WeierstrassCurve.ΨSq
#check WeierstrassCurve.ΨSq_zero
#check WeierstrassCurve.ΨSq_one
#check WeierstrassCurve.ΨSq_two
#check WeierstrassCurve.ΨSq_three
#check WeierstrassCurve.ΨSq_four
#check WeierstrassCurve.ΨSq_neg
#check WeierstrassCurve.ΨSq_even
#check WeierstrassCurve.ΨSq_odd

#check WeierstrassCurve.Ψ
#check WeierstrassCurve.Ψ_zero
#check WeierstrassCurve.Ψ_one
#check WeierstrassCurve.Ψ_two
#check WeierstrassCurve.Ψ_three
#check WeierstrassCurve.Ψ_four
#check WeierstrassCurve.Ψ_neg
#check WeierstrassCurve.Ψ_even
#check WeierstrassCurve.Ψ_odd
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq

#check WeierstrassCurve.Φ
#check WeierstrassCurve.Φ_zero
#check WeierstrassCurve.Φ_one
#check WeierstrassCurve.Φ_two
#check WeierstrassCurve.Φ_three
#check WeierstrassCurve.Φ_four
#check WeierstrassCurve.Φ_neg

#check WeierstrassCurve.ψ
#check WeierstrassCurve.ψ_zero
#check WeierstrassCurve.ψ_one
#check WeierstrassCurve.ψ_two
#check WeierstrassCurve.ψ_three
#check WeierstrassCurve.ψ_four
#check WeierstrassCurve.ψ_neg
#check WeierstrassCurve.ψ_even
#check WeierstrassCurve.ψ_odd
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ

#check WeierstrassCurve.φ
#check WeierstrassCurve.φ_zero
#check WeierstrassCurve.φ_one
#check WeierstrassCurve.φ_two
#check WeierstrassCurve.φ_three
#check WeierstrassCurve.φ_four
#check WeierstrassCurve.φ_neg
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ

#check WeierstrassCurve.map_ΨSq
#check WeierstrassCurve.map_Φ
#check WeierstrassCurve.map_ψ
#check WeierstrassCurve.map_φ
#check WeierstrassCurve.baseChange_ΨSq
#check WeierstrassCurve.baseChange_Φ
#check WeierstrassCurve.baseChange_ψ
#check WeierstrassCurve.baseChange_φ
```

The definitions are exactly the ones we want to target:

```lean
-- schematic types
WeierstrassCurve.ΨSq (W : WeierstrassCurve R) (n : ℤ) : R[X]
WeierstrassCurve.Φ   (W : WeierstrassCurve R) (n : ℤ) : R[X]
WeierstrassCurve.Ψ   (W : WeierstrassCurve R) (n : ℤ) : R[X][Y]
WeierstrassCurve.ψ   (W : WeierstrassCurve R) (n : ℤ) : R[X][Y]
WeierstrassCurve.φ   (W : WeierstrassCurve R) (n : ℤ) : R[X][Y]
```

The strongest current congruence lemmas I found are coordinate-ring congruences:

```lean
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq
-- (mk W W.ψ₂)^2 = mk W (C W.Ψ₂Sq)

#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
-- mk W (W.Ψ n)^2 = mk W (C (W.ΨSq n))

#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
-- mk W (W.ψ n) = mk W (W.Ψ n)

#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
-- mk W (W.φ n) = mk W (C (W.Φ n))
```

These are useful, but they stop inside the coordinate ring.  They do **not** say anything like `n • P = 0`, `x(nP)`, or roots of `ΨSq`.

## 2. What Mathlib does not appear to have

I do not see declarations with any of the following intended shapes:

```lean
-- Not found / not current Mathlib API:
#check WeierstrassCurve.Affine.Point.x_nsmul_eq_Φ_div_ΨSq
#check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_ψ_eval_eq_zero
#check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_ΨSq_eval_eq_zero
#check WeierstrassCurve.Affine.Point.divisionPolynomial_eval_eq_zero_iff
#check WeierstrassCurve.ΨSq_roots_eq_xCoords_nTorsion
#check WeierstrassCurve.ψ_roots_eq_nTorsion
#check WeierstrassCurve.Φ_ΨSq_x_nsmul
```

Also, I do not see an elliptic subgroup-scheme API that would bypass coordinates and give:

```lean
E[n] cut out by ψₙ
```

or

```lean
E[n](K) = zeros of division polynomial on affine chart plus infinity
```

The current affine point group API has `Point`, `Point.add`, `Point.neg`, `Point.instAddCommGroup`, etc., but not a torsion/division-polynomial bridge.

## 3. Repo-local FLT status

The repo has `FLT/EllipticCurve/Torsion.lean`, with the abstract type

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and then theorem-shaped placeholders such as:

```lean
#check WeierstrassCurve.n_torsion_finite
#check WeierstrassCurve.n_torsion_card
#check WeierstrassCurve.n_torsion_dimension
```

Those are the geometric `E[n]` API direction, but they do not provide a division-polynomial root characterization either.  The comments explicitly point toward division polynomials as the future proof route, not as an already available theorem.

## 4. Roots / separability / degree information

Current Mathlib exposes only limited root-adjacent information for this topic.

For `n = 2`, there is:

```lean
#check WeierstrassCurve.twoTorsionPolynomial
#check WeierstrassCurve.twoTorsionPolynomial_discr
#check WeierstrassCurve.twoTorsionPolynomial_discr_isUnit
#check WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero
#check WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero_of_isElliptic
#check WeierstrassCurve.Ψ₂Sq_eq
```

The docstring of `twoTorsionPolynomial` says that over a field of characteristic different from `2`, its roots over a splitting field are precisely the `X`-coordinates of nonzero 2-torsion points.  But I do not see that root characterization as a formal theorem; the formal theorem is about the discriminant:

```lean
WeierstrassCurve.twoTorsionPolynomial_discr :
  W.twoTorsionPolynomial.discr = 16 * W.Δ
```

For general `n`, I do not see:

```lean
#check WeierstrassCurve.ΨSq_natDegree
#check WeierstrassCurve.ΨSq_degree
#check WeierstrassCurve.ΨSq_monic
#check WeierstrassCurve.ΨSq_separable
#check WeierstrassCurve.ΨSq_roots
#check WeierstrassCurve.ψ_separable
#check WeierstrassCurve.ψ_roots
```

The `DivisionPolynomial.Basic` file defines recurrences and proves base-change/congruence lemmas; it does not appear to prove root counts, separability, degree formulas, or the root/torsion equivalence.

## 5. Can we avoid the x-only ladder?

I do not see a current Mathlib path that avoids a group-law coordinate proof.

The desired theorem is essentially:

```lean
namespace WeierstrassCurve
namespace Affine

-- target shape, not existing Mathlib
lemma Point.nsmul_eq_zero_iff_ΨSq_eval_eq_zero
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ)
    {x y : K} (hP : (W⁄K).Nonsingular x y) :
    n • (.some x y hP : (W⁄K).Point) = 0
      ↔ Polynomial.eval x (W.ΨSq (n : ℤ)) = 0 := by
  sorry

end Affine
end WeierstrassCurve
```

Possible proof routes:

### Route A: x-only ladder / Kummer recurrence

This is the current hand-rolled route:

```text
Point.add/neg/double  →  projective x-only differential addition
                     →  ladder for x(nP)
                     →  identify ladder polynomials with Φₙ/ΨSqₙ recurrences
                     →  nP = 0 iff denominator/numerator projective output is [1:0]
                     →  ΨSqₙ(x(P)) = 0.
```

This route matches the existing Mathlib objects `Φ`, `ΨSq`, `preΨ`, and the EDS recurrences.  It is still work, but it uses the definitions Mathlib actually has.

### Route B: coordinate-ring division polynomial action theorem

One could try to prove a stronger coordinate-ring theorem:

```lean
-- not existing, possible new theorem
lemma mk_X_of_nsmul_eq_Φ_ΨSq
    (P : (W⁄K).Point) :
    P1Q.SameQ (xRep W (n • P))
      { X := Polynomial.eval (x P) (W.Φ n)
        Z := Polynomial.eval (x P) (W.ΨSq n) } := by
  sorry
```

But proving this still requires induction through the group law or a Kummer addition formula.  This is basically the ladder route in coordinate-ring clothing.

### Route C: subgroup scheme / roots theorem

This would be ideal:

```lean
-- not existing
E[n] = V(ψₙ)
```

But Mathlib does not currently expose an elliptic-curve finite subgroup scheme API or a theorem that `ψₙ` cuts out `E[n]`.  Building this route would be much larger than the ladder.

### Route D: use only cardinality/root counts

Even if Mathlib had degree and separability lemmas, root counts alone would not prove the exact pointwise equivalence without a map from torsion points to roots and back.  The missing bridge remains the coordinate formula or subgroup-scheme theorem.

## 6. Concrete useful Mathlib facts for the ladder route

Even though there is no shortcut, Mathlib's definitions are valuable targets.  The ladder should aim to prove statements like:

```lean
-- project local statement, not existing Mathlib
lemma xRep_nsmul_same_Φ_ΨSq
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (P : (W⁄K).Point) :
    P1.Same
      (xRep W (n • P))
      (P1.mk
        (Polynomial.eval (xRep W P).x (W.Φ (n : ℤ)))
        (Polynomial.eval (xRep W P).x (W.ΨSq (n : ℤ)))) := by
  -- prove by ladder + recurrence matching
  sorry
```

Then derive:

```lean
-- project local statement
lemma nsmul_eq_zero_iff_ΨSq_eval_eq_zero
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K} (hP : (W⁄K).Nonsingular x y)
    (hn_nonzero_output : (* handle n=0 / projective numerator cases *)) :
    n • (.some x y hP : (W⁄K).Point) = 0
      ↔ Polynomial.eval x (W.ΨSq (n : ℤ)) = 0 := by
  sorry
```

The exact theorem should special-case `n = 0` and `P = 0` carefully.  For affine nonzero points and positive `n`, the denominator-zero characterization is the intended form.

## 7. Bottom line

There is no existing Mathlib theorem that gives the keystone directly.

What Mathlib gives:

```text
✅ EDS recurrence definitions: preNormEDS, normEDS.
✅ Weierstrass division polynomial definitions: ψ₂, Ψ₂Sq, preΨ, ΨSq, Ψ, Φ, ψ, φ.
✅ initial values and recurrence lemmas for those sequences.
✅ coordinate-ring congruences: mk_ψ, mk_φ, mk_Ψ_sq.
✅ base-change/map lemmas for the polynomials.
✅ 2-torsion polynomial discriminant and equality Ψ₂Sq = twoTorsionPolynomial.toPoly.
```

What Mathlib does not appear to give:

```text
❌ x(nP) = Φₙ(x(P)) / ΨSqₙ(x(P)).
❌ n • P = 0 ↔ ψₙ(P) = 0.
❌ n • P = 0 ↔ ΨSqₙ(x(P)) = 0.
❌ roots of ΨSqₙ are exactly x-coordinates of n-torsion.
❌ degree/separability/root-count theorem for ΨSqₙ.
❌ subgroup-scheme theorem saying E[n] is cut out by ψₙ.
```

Therefore the Montgomery/Kummer x-only ladder is not redundant.  It is the practical bridge from Mathlib's point group law to Mathlib's division-polynomial definitions.  The shortest path remains:

```text
1. Prove x-only differential addition from Mathlib Point.add.
2. Build the Montgomery/Kummer ladder on xRep.
3. Match the ladder recurrence to Mathlib's `preΨ`, `Φ`, `ΨSq` recurrences.
4. Derive `n • P = 0 ↔ ΨSqₙ(x(P)) = 0`.
```

If a shortcut is desired later, the most reusable theorem to upstream would be the coordinate formula:

```lean
theorem WeierstrassCurve.Affine.Point.x_nsmul_same_Φ_ΨSq
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (P : (W⁄K).Point) :
    P1.Same (xRep W (n • P))
      (P1.mk (evalX P (W.Φ (n : ℤ))) (evalX P (W.ΨSq (n : ℤ)))) := by
  sorry
```

But proving that theorem is exactly the ladder/differential-addition project.
