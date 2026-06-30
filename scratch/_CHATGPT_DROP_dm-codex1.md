# Q2650 (dm-codex1): independent `RatQuarticEisensteinDegenerate` route

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
GitHub repo/branch: `xiangyazi24/FLT`, branch `scratch`  
Goal: prove

```lean
def RatQuarticEisensteinDegenerate : Prop :=
  ∀ {t s : ℚ}, s ^ 2 = t ^ 4 - t ^ 2 + 1 → t = 0 ∨ t ^ 2 = 1
```

without using the E24/E1 finite-point theorem, `RationalPointsN12`, or the full-cover residual loop.

## Executive answer

1. Yes: the rational theorem is exactly the primitive homogeneous Eisenstein/Ljunggren quartic
   `S^2 = A^4 - A^2*N^2 + N^4`, with `gcd A N = 1` and `N ≠ 0`.  In Eisenstein notation, if `ω^2 + ω + 1 = 0`, then
   `A^4 - A^2*N^2 + N^4 = Norm (A^2 + N^2*ω)`.
2. I did not find a ready Mathlib theorem classifying this quartic under names like Ljunggren/Eisenstein/quartic norm.  Mathlib has useful ingredients, not the classification.
3. Do **not** plan to derive it from `not_fermat_42` by denominator clearing.  `not_fermat_42` forbids `a^4 + b^4 = c^2`; the cleared target is an Eisenstein norm-square.  A bridge from this norm-square to FLT4 would itself be a nontrivial new descent.
4. Best Lean target: prove the primitive integer theorem below, then obtain the rational theorem by a small denominator-clearing file.

## 1. Exact integer theorem to target

The theorem needed by Lean should be primitive.  The non-primitive version is optional; the rational denominator reduction naturally gives primitive `A,N`.

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.PythagoreanTriples

namespace MazurProof.RationalPointsN12

/-- Primitive homogeneous Eisenstein/Ljunggren quartic obstruction. -/
def IntQuarticEisensteinPrimitive : Prop :=
  ∀ {A N S : ℤ},
    IsCoprime A N →
    N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- Bad primitive solution, for a minimal-descent proof. -/
def EisensteinQuarticBad (A N S : ℤ) : Prop :=
  IsCoprime A N ∧
  A ≠ 0 ∧ N ≠ 0 ∧ A ^ 2 ≠ N ^ 2 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Descent step sufficient to prove `IntQuarticEisensteinPrimitive`. -/
def EisensteinQuarticDescentStep : Prop :=
  ∀ {A N S : ℤ},
    EisensteinQuarticBad A N S →
    ∃ A' N' S' : ℤ,
      EisensteinQuarticBad A' N' S' ∧
      Int.natAbs A' + Int.natAbs N' < Int.natAbs A + Int.natAbs N

end MazurProof.RationalPointsN12
```

Then prove:

```lean
-- theorem no_eisensteinQuarticBad_of_descent
--     (hdesc : EisensteinQuarticDescentStep) :
--     ¬ ∃ A N S : ℤ, EisensteinQuarticBad A N S

-- theorem intQuarticEisensteinPrimitive_of_descent
--     (hdesc : EisensteinQuarticDescentStep) :
--     IntQuarticEisensteinPrimitive
```

The last two are routine well-founded/minimal-counterexample wrappers over the measure
`Int.natAbs A + Int.natAbs N`.

## 2. Rational/integer equivalence

Classically, `RatQuarticEisensteinDegenerate` and `IntQuarticEisensteinPrimitive` are equivalent.

### Integer theorem implies rational theorem

Use `A = t.num`, `N = (t.den : ℤ)`.  From `Rat.reduced`, get `IsCoprime A N`; from `Rat.den_nz`, get `N ≠ 0`.

Main denominator lemma:

```lean
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Int.Basic

namespace MazurProof.RationalPointsN12

/-- If a rational square is an integer, then the rational number is an integer. -/
def RatSquareIntegral : Prop :=
  ∀ {q : ℚ} {m : ℤ}, q ^ 2 = (m : ℚ) → ∃ z : ℤ, q = z

/-- Denominator-cleared quartic datum from a rational point. -/
def RatQuarticToPrimitiveIntDatum : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    ∃ A N S : ℤ,
      IsCoprime A N ∧
      N ≠ 0 ∧
      t = (A : ℚ) / (N : ℚ) ∧
      S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

end MazurProof.RationalPointsN12
```

Proof DAG for `RatQuarticToPrimitiveIntDatum`:

1. Set `A := t.num`, `N := (t.den : ℤ)`.
2. Rewrite `t = A / N` using `Rat.num_div_den`.
3. Let `P : ℤ := A^4 - A^2*N^2 + N^4`.
4. From `s^2 = t^4 - t^2 + 1`, prove
   ```lean
   (s * (N : ℚ) ^ 2) ^ 2 = (P : ℚ)
   ```
   by `field_simp [Rat.den_nz]` and `ring`.
5. Apply `RatSquareIntegral` to `q := s * (N : ℚ)^2`, obtaining `S : ℤ`.
6. Cast back to `ℤ` to get `S^2 = P`.

Then:

```lean
-- theorem ratQuarticEisensteinDegenerate_of_intQuarticEisensteinPrimitive
--     (hZ : IntQuarticEisensteinPrimitive) :
--     RatQuarticEisensteinDegenerate
```

Proof: obtain `A,N,S`; apply `hZ`; translate `A = 0` to `t = 0`, and `A^2 = N^2` to `t^2 = 1` using `N ≠ 0`.

### Rational theorem implies integer theorem

For completeness, the reverse direction is immediate:

```lean
-- theorem intQuarticEisensteinPrimitive_of_ratQuarticEisensteinDegenerate
--     (hQ : RatQuarticEisensteinDegenerate) :
--     IntQuarticEisensteinPrimitive
```

Given primitive `A,N,S`, set `t := (A : ℚ)/(N : ℚ)` and `s := (S : ℚ)/(N : ℚ)^2`; clear denominators, apply `hQ`, and use `N ≠ 0`.

## 3. Why `not_fermat_42` is not enough

Mathlib’s FLT4 theorem has the shape:

```lean
-- in Mathlib.NumberTheory.FLT.Four
-- theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
--   a ^ 4 + b ^ 4 ≠ c ^ 2
```

The cleared Eisenstein target is instead:

```text
S^2 = A^4 - A^2*N^2 + N^4.
```

Useful identity:

```text
(A^2 + N^2) * S^2 = A^6 + N^6.
```

This does **not** produce `u^4 + v^4 = w^2`; it leaves the extra factor `A^2 + N^2`.  Therefore `not_fermat_42` is not a short denominator-clearing dependency.  It is still reasonable to reuse Mathlib lemmas that FLT4 uses, especially:

```lean
-- Int.sq_of_gcd_eq_one
-- PythagoreanTriple.coprime_classification
-- PythagoreanTriple.coprime_classification'
```

but not to make `not_fermat_42` the main theorem dependency.

## 4. Concrete integer-descent proof DAG

There are two Lean-feasible variants.  The first is more “Mathlib algebraic number theory”; the second keeps the theorem as an explicit integer descent.

### Route A: Eisenstein PID/UFD route using existing Mathlib

Relevant Mathlib facts already exist:

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
```

Useful existing APIs:

```lean
-- IsCyclotomicExtension.Rat.three_pid
-- IsCyclotomicExtension.Rat.Three.Units.mem
-- IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
-- IsCyclotomicExtension.Rat.Three.eta_sq
-- IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
```

Proof skeleton:

1. Work in `𝓞 K` for a third cyclotomic field, with `ω = ζ₃` and `ω^2 + ω + 1 = 0`.
2. Define
   ```text
   α = A^2 + N^2 * ω.
   ```
   Its norm is `A^4 - A^2*N^2 + N^4 = S^2`.
3. Prove primitive coprimality:
   ```lean
   -- lemma eis_alpha_coprime_conj
   --   IsCoprime A N → IsCoprime α (star α)
   ```
   The only possible common Eisenstein prime is above `3`; exclude it because primitive `A,N` cannot satisfy `3 ∣ A^2 + N^2` unless both are divisible by `3`.
4. In a PID/UFD, if `α * star α` is a square and `α` is coprime to `star α`, then `α` is associated to a square:
   ```lean
   -- lemma eis_alpha_associated_square
   --   IsCoprime α (star α) → norm α = S^2 → ∃ u β, IsUnit u ∧ α = u * β^2
   ```
   Search for `exists_associated_pow_of_mul_eq_pow`; this is what `Int.sq_of_gcd_eq_one` uses internally.
5. Reduce the unit using the six Eisenstein units.  Since unit squares have index two in the unit group, reduce to:
   ```text
   α = β^2   or   α = -β^2.
   ```
6. Finish with an integer coefficient-square descent:
   ```lean
   -- theorem eis_unit_square_coeffs_trivial
   --   IsCoprime A N → N ≠ 0 →
   --   (∃ r s, (A^2, N^2) = coeffs ((r + s*ω)^2)) ∨
   --   (∃ r s, (A^2, N^2) = coeffs (-(r + s*ω)^2)) →
   --   A = 0 ∨ A^2 = N^2
   ```

This route is independent of the E1 finite-point theorem, but it imports heavy number-field infrastructure.  It may still be faster than formalizing a Euclidean algorithm for Eisenstein integers from scratch.

### Route B: explicit integer descent, no number-field import

Prove the same square-in-Eisenstein conclusion by elementary factorization in integers.

Core factorization:

```text
(A^2 + N^2 + S) * (A^2 + N^2 - S) = 3 * A^2 * N^2.
```

Suggested helper lemmas:

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.PythagoreanTriples

namespace MazurProof.RationalPointsN12

/-- Primitive quartic solutions have numerator/denominator coprime to `S`. -/
def EisensteinQuarticCoprimeSideLemmas : Prop :=
  ∀ {A N S : ℤ},
    IsCoprime A N →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    IsCoprime A S ∧ IsCoprime N S

/-- GCD control for the two factors `A^2+N^2±S`. -/
def EisensteinQuarticFactorGcdControl : Prop :=
  ∀ {A N S : ℤ},
    IsCoprime A N →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    -- exact statement should case-split powers of `2` and `3`
    True

/-- The hard bounded descent step. -/
def EisensteinQuarticDescentTheorem : Prop :=
  EisensteinQuarticDescentStep

end MazurProof.RationalPointsN12
```

Concrete descent target:

```lean
-- theorem eisensteinQuartic_descent_step : EisensteinQuarticDescentStep
```

Recommended construction shape:

1. Normalize a bad solution by signs and symmetry so `0 < |A| ≤ |N|`, `A ≠ 0`, `A^2 ≠ N^2`.
2. Use the factorization above and primitive gcd facts to show the factors `A^2+N^2±S` are, up to controlled factors `1,2,3,6`, squares times the square parts of `A` and `N`.
3. Equivalently derive the coefficient-square form
   ```text
   A^2 + N^2*ω = ±(r + s*ω)^2
   ```
   without introducing an Eisenstein-integer type.
4. Expanding `(r+sω)^2 = (r^2-s^2) + (2rs-s^2)ω`, reduce to products of coprime integer factors that are squares using `Int.sq_of_gcd_eq_one`.
5. Produce a smaller primitive bad solution `(A',N',S')` with
   ```text
   |A'| + |N'| < |A| + |N|.
   ```
6. Close by minimal counterexample.

This route has more parity/gcd casework but the dependencies stay close to `N12DoubleLegDegenerate.lean`: `Mathlib.Tactic`, `Mathlib.RingTheory.Int.Basic`, and possibly `Mathlib.NumberTheory.PythagoreanTriples`.

## 5. File layout recommendation

Add a new independent file, for example:

```lean
-- FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.PythagoreanTriples
-- optional, only for Route A:
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

-- Do NOT import:
-- import FLT.Assumptions.MazurProof.RationalPointsN12
-- import any E24/E1 finite-point terminal theorem
```

Then have `N12DoubleLegDegenerate.lean` import this new file, or keep the current conditional theorem and add a separate theorem supplying `RatQuarticEisensteinDegenerate` from the new file.

## 6. Mathlib files/API to grep first

Project is pinned to Mathlib rev `96fd0fff3b8837985ae21dd02e712cb5df72ec05` in `lakefile.toml`.

Grep these first:

```text
Mathlib/NumberTheory/FLT/Four.lean
  not_fermat_42
  Fermat42
  Fermat42.exists_minimal
  Fermat42.not_minimal

Mathlib/NumberTheory/PythagoreanTriples.lean
  PythagoreanTriple.coprime_classification
  PythagoreanTriple.coprime_classification'
  PythagoreanTriple.classification

Mathlib/RingTheory/Int/Basic.lean
  Int.sq_of_gcd_eq_one
  Int.sq_of_isCoprime
  Int.eq_pow_of_mul_eq_pow_odd

Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean
  IsCyclotomicExtension.Rat.three_pid

Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean
  IsCyclotomicExtension.Rat.Three.Units.mem
  IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
  IsCyclotomicExtension.Rat.Three.eta_sq
  IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one

Mathlib/NumberTheory/Zsqrtd/Basic.lean
  Zsqrtd.norm
  Zsqrtd.norm_mul
  Zsqrtd.intCast_dvd
```

Search notes:

```text
Ljunggren             -- no ready classification found
Eisenstein quartic    -- no ready classification found
x^4 - x^2*y^2 + y^4  -- no ready classification found
not_fermat_42         -- exists, but wrong equation shape
```

## 7. Minimal next Lean milestone

Prove these first, in this order:

```lean
-- 1. local denominator lemma
-- lemma Rat.exists_int_eq_of_sq_eq_int
--     {q : ℚ} {m : ℤ} (h : q ^ 2 = (m : ℚ)) : ∃ z : ℤ, q = z

-- 2. rational-to-primitive-integer data
-- lemma ratQuartic_to_primitive_intDatum
--     {t s : ℚ} (h : s ^ 2 = t ^ 4 - t ^ 2 + 1) :
--     ∃ A N S : ℤ,
--       IsCoprime A N ∧ N ≠ 0 ∧
--       t = (A : ℚ) / (N : ℚ) ∧
--       S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

-- 3. wrapper
-- theorem ratQuarticEisensteinDegenerate_of_intQuarticEisensteinPrimitive
--     (hZ : IntQuarticEisensteinPrimitive) :
--     RatQuarticEisensteinDegenerate

-- 4. hard theorem
-- theorem intQuarticEisensteinPrimitive : IntQuarticEisensteinPrimitive
```

Once milestone 1–3 are checked, the project has a clean seam: all remaining difficulty is the standalone integer descent theorem, with no dependency on E1 finite-point classification.
