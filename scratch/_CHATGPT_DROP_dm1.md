# Q80 (dm1): `preΨ'` separability for division polynomials

## Executive answer

The target theorem

```lean
theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

is mathematically true under the stated hypotheses, but current Mathlib does **not** already contain the elliptic-curve brick that proves it.  The polynomial infrastructure is present; the missing part is the elliptic-curve/simple-root theorem for division polynomials.

The most tractable route in the present API is **E2**, but not as a variable-`n` CAS resultant.  The clean Mathlib-facing form is a single structural lemma saying that `preΨ' n` has no repeated algebraic roots when `(n : k) ≠ 0`.  Once that lemma is available, the desired theorem is a short wrapper using `Polynomial.nodup_aroots_iff_of_splits` or, equivalently, `Polynomial.separable_def`.

The **E1** route (`[n]` is étale, kernel reduced) is mathematically best, but current Mathlib/FLT does not expose enough scheme/isogeny API for elliptic curves to make it the short proof.  In `FLT/EllipticCurve/Torsion.lean`, even `n_torsion_finite` and `n_torsion_card` are still placeholders; using those to prove separability would be circular for the torsion development.

---

## API currently available and useful

From `Mathlib.FieldTheory.Separable`:

```lean
Polynomial.Separable f = IsCoprime f (Polynomial.derivative f)
Polynomial.separable_def
Polynomial.separable_def'
Polynomial.separable_map
Polynomial.nodup_aroots_iff_of_splits
Polynomial.card_rootSet_eq_natDegree_iff_of_splits
Polynomial.Separable.map
Polynomial.Separable.ne_zero
Polynomial.Separable.squarefree
```

The most important exact facts are:

```lean
#check Polynomial.separable_def
-- p.Separable ↔ IsCoprime p (derivative p)

#check Polynomial.separable_def'
-- p.Separable ↔ ∃ a b, a * p + b * derivative p = 1

#check Polynomial.separable_map
-- (map f p).Separable ↔ p.Separable

#check Polynomial.nodup_aroots_iff_of_splits
-- f ≠ 0 → (map (algebraMap F K) f).Splits →
--   (f.aroots K).Nodup ↔ f.Separable
```

From `Mathlib.FieldTheory.IsAlgClosed.Basic`:

```lean
#check IsAlgClosed.splits
#check IsAlgClosed.splits_codomain
```

The deprecated `IsAlgClosed.splits_codomain` is still exactly the shape one wants for algebraic closures:

```lean
(map (algebraMap k (AlgebraicClosure k)) p).Splits
```

but the non-deprecated form

```lean
IsAlgClosed.splits (Polynomial.map (algebraMap k (AlgebraicClosure k)) p)
```

also works.

From `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`:

```lean
#check WeierstrassCurve.preΨ'
#check WeierstrassCurve.preΨ'_zero
#check WeierstrassCurve.preΨ'_one
#check WeierstrassCurve.preΨ'_two
#check WeierstrassCurve.preΨ'_three
#check WeierstrassCurve.preΨ'_four
#check WeierstrassCurve.preΨ'_even
#check WeierstrassCurve.preΨ'_odd
#check WeierstrassCurve.map_preΨ'
#check WeierstrassCurve.baseChange_preΨ'
```

From `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`:

```lean
#check WeierstrassCurve.natDegree_preΨ'_le
#check WeierstrassCurve.coeff_preΨ'
#check WeierstrassCurve.coeff_preΨ'_ne_zero
#check WeierstrassCurve.natDegree_preΨ'
#check WeierstrassCurve.leadingCoeff_preΨ'
#check WeierstrassCurve.preΨ'_ne_zero
```

These prove that `preΨ' n` has the expected degree and is nonzero when `(n : k) ≠ 0`, but they do not prove squarefreeness/separability.

---

## What is missing

There is no current Mathlib theorem of the following kind:

```lean
theorem Isogeny.mul_separable_of_natCast_ne_zero ...
theorem WeierstrassCurve.mul_by_n_etale ...
theorem WeierstrassCurve.nTorsion_reduced ...
theorem WeierstrassCurve.preΨ'_separable_of_natCast_ne_zero ...
theorem WeierstrassCurve.preΨ'_isCoprime_derivative_of_natCast_ne_zero ...
```

The minimal useful missing lemma can be stated in either of the following two equivalent styles.

### Missing brick A: direct Bézout / derivative coprimality

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Missing structural theorem: division polynomials have no repeated roots when `char k ∤ n`. -/
theorem preΨ'_isCoprime_derivative_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- Missing in current Mathlib/FLT.
  -- Mathematical proof: `[n] : E → E` is separable/étale because `(n : k) ≠ 0`;
  -- therefore the finite kernel is reduced.  Passing to the quotient by `P ~ -P`
  -- gives that the univariate `x`-coordinate division polynomial has simple roots.
  -- Algebraic proof: construct a Bezout identity
  --   A_n * preΨ' n + B_n * derivative (preΨ' n) = 1
  -- over the universal nonsingular Weierstrass ring after inverting `n`.
  sorry

end WeierstrassCurve
```

With this brick, the target theorem is literally just `Polynomial.separable_def`:

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

theorem preΨ'_separable_of_natCast_ne_zero_via_coprime
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  rw [Polynomial.separable_def]
  exact W.preΨ'_isCoprime_derivative_of_natCast_ne_zero hn

end WeierstrassCurve
```

### Missing brick B: no repeated algebraic roots

This form is often easier to connect to the geometric proof over an algebraic closure:

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Missing structural theorem, root form. -/
theorem preΨ'_aroots_nodup_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    ((W.preΨ' n).aroots (AlgebraicClosure k)).Nodup := by
  -- Missing in current Mathlib/FLT.
  -- Equivalent content: every algebraic root of `preΨ' n` is a simple root.
  -- This is the `x`-coordinate shadow of the reducedness of `ker [n]`.
  sorry

end WeierstrassCurve
```

Given this root-form brick, the wrapper theorem is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- This is the desired theorem, assuming the missing simple-root brick above. -/
theorem preΨ'_separable_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  classical
  let K := AlgebraicClosure k
  let i : k →+* K := algebraMap k K
  have hne : W.preΨ' n ≠ 0 := W.preΨ'_ne_zero hn
  have hsplit : (Polynomial.map i (W.preΨ' n)).Splits := by
    -- `K` is algebraically closed, so every polynomial over `K` splits.
    exact IsAlgClosed.splits (Polynomial.map i (W.preΨ' n))
  exact (Polynomial.nodup_aroots_iff_of_splits
    (K := K) hne hsplit).mp
      (W.preΨ'_aroots_nodup_of_natCast_ne_zero hn)

end

end WeierstrassCurve
```

This proof uses only the general polynomial API and `preΨ'_ne_zero`; all elliptic content is isolated in `preΨ'_aroots_nodup_of_natCast_ne_zero`.

---

## A more geometric statement of the missing brick

If you want the missing theorem to line up with the standard `[n]`-étale proof, use this shape over an arbitrary algebraically closed extension.  It avoids hard-coding `AlgebraicClosure k` and is reusable for torsion counting.

```lean
namespace WeierstrassCurve

open Polynomial

variable {k K : Type*} [Field k] [Field K]
variable [Algebra k K] [IsScalarTower k k K]
variable [DecidableEq k] [DecidableEq K]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Preferred geometric missing lemma: after base change to an algebraically closed field,
`preΨ' n` has simple roots if `(n : K) ≠ 0`. -/
theorem baseChange_preΨ'_aroots_nodup_of_natCast_ne_zero
    [IsAlgClosed K]
    {n : ℕ} (hnK : (n : K) ≠ 0) :
    (((W.baseChange K).preΨ' n).aroots K).Nodup := by
  -- Missing geometric proof.
  -- Outline:
  -- 1. Interpret roots of `(W.baseChange K).preΨ' n` as `x`-coordinates of nonzero
  --    `n`-torsion points, excluding the pure `2`-torsion factor in the even case.
  -- 2. Prove `[n]` has differential multiplication by `(n : K)` on the tangent space at `O`.
  -- 3. Since `(n : K) ≠ 0`, `[n]` is étale, so `ker [n]` is reduced.
  -- 4. The quotient by `P ↦ -P` is unramified away from 2-torsion; the normalized `preΨ'`
  --    has removed the `ψ₂` factor in the even case, so every remaining `x`-root is simple.
  sorry

end WeierstrassCurve
```

Then specialize to `K = AlgebraicClosure k`.  The base-change relation is already available:

```lean
#check WeierstrassCurve.baseChange_preΨ'
#check WeierstrassCurve.map_preΨ'
```

---

## Why a pure resultant proof is not currently the best route

For a fixed small `n`, a CAS-generated Bezout certificate

```text
A_n * preΨ' n + B_n * derivative (preΨ' n) = 1
```

is practical.  For variable `n`, this is not a single finite polynomial identity; it is a theorem about the multiplication-by-`n` morphism or about the universal division-polynomial recurrence.  Mathlib has `Polynomial.resultant` and the separability/coprimality API, but it does not contain a universal formula

```text
Res(preΨ' n, (preΨ' n)') = unit * Δ^e * n^a
```

nor the formal group/isogeny result from which it follows.  Proving that resultant formula for all `n` would be at least as hard as proving the simple-root theorem directly.

---

## Extra hypotheses

No extra field hypothesis is mathematically needed.

* No `[PerfectField k]` is needed.  Separability of this particular polynomial follows from `char k ∤ n`, not from all finite extensions of `k` being separable.
* No `[IsSepClosed k]` or algebraic-closedness hypothesis is needed in the final theorem.  It is fine to pass temporarily to `AlgebraicClosure k` because `Polynomial.separable_map` and `Polynomial.nodup_aroots_iff_of_splits` are designed for this.
* No `[CharZero k]` is needed.  Positive characteristic is allowed as long as `(n : k) ≠ 0`.
* `[DecidableEq k]` is not mathematically needed for `Polynomial.Separable`, but it is harmless in the surrounding `Torsion.lean` namespace and is often needed by the elliptic-curve point API.
* `[W.IsElliptic]` is genuinely needed.  On singular Weierstrass cubics, division polynomials can acquire multiple roots even when the relevant integer is nonzero in the field.

---

## Recommendation for FLT

Add the missing theorem in the direct form first:

```lean
theorem WeierstrassCurve.preΨ'_isCoprime_derivative_of_natCast_ne_zero
    {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

Then the target theorem in `FLT/EllipticCurve/Torsion.lean` is stable and tiny:

```lean
theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  rw [Polynomial.separable_def]
  exact W.preΨ'_isCoprime_derivative_of_natCast_ne_zero hn
```

If the proof is developed geometrically, first prove the algebraic-root nodup statement over `AlgebraicClosure k`, then derive the direct coprimality theorem using `Polynomial.nodup_aroots_iff_of_splits`.  If the proof is developed algebraically, prove the direct `IsCoprime`/Bezout theorem and skip roots entirely.
