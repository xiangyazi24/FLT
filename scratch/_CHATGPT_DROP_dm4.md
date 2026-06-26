# Q662 (dm4): linear coefficients of `formalGroupLaw`

## Executive answer

The clean local lemma is the degree-one product formula for multivariate power series:

```lean
coeff (single i 1) (f * g)
  = constantCoeff f * coeff (single i 1) g
    + coeff (single i 1) f * constantCoeff g
```

Then specialize it to `f = -A`, where `A = normalizedAddX W`, and `g = ↑u⁻¹`, where

```lean
u := (normalizedAddY_isUnit W).unit.
```

If `constantCoeff A = 0`, the first summand dies, so

```lean
coeff (single i 1) (-A * ↑u⁻¹)
  = - coeff (single i 1) A * constantCoeff (↑u⁻¹).
```

Finally, if `constantCoeff (↑u) = 1`, then `constantCoeff (↑u⁻¹) = 1`, because `constantCoeff` is a ring hom and `↑u * ↑u⁻¹ = 1`.  Therefore, using

```lean
coeff (single i 1) (normalizedAddX W) = -1,
```

the formal group law coefficient is

```text
-(-1) * 1 = 1.
```

This is better than trying to prove a special theorem about units directly: the only coefficient computation is the `coeff_mul` computation at `single i 1`.

---

## Drop-in Lean lemmas

The following code is written so the product-coefficient lemmas are independent of the elliptic-curve code.  The final theorem is parameterized by the three normalized coefficient facts; at the bottom I show how to specialize it using the expected names from the quotient-extraction lemmas.

```lean
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.Tactic
-- import the local file that defines:
--   formalGroupLaw
--   normalizedAddX
--   normalizedAddY
--   normalizedAddY_isUnit
-- and the normalized coefficient lemmas.
-- import FLT.<path>.FormalGroupW

noncomputable section

open MvPowerSeries Finsupp
open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local notation "e" i => Finsupp.single i 1
local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n

/-- The linear coefficient of a product of two bivariate formal power series.

This is the only real `coeff_mul` calculation needed for the linear coefficients of
`formalGroupLaw`.  The antidiagonal of `single i 1` has exactly the two splittings
`0 + single i 1` and `single i 1 + 0`. -/
private lemma coeff_mul_single_one
    (i : Fin 2) (f g : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e i) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (e i) g
        + MvPowerSeries.coeff (e i) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul]
  -- `Finsupp.antidiagonal_single` reduces the bivariate antidiagonal to the
  -- natural-number antidiagonal of `1`, namely `(0,1)` and `(1,0)`.
  rw [Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_comm, add_left_comm, add_assoc]

/-- If the left factor has zero constant coefficient, then the degree-one coefficient
of `-A * V` only sees the degree-one coefficient of `A` and the constant coefficient
of `V`. -/
private lemma coeff_neg_mul_single_one_of_constantCoeff_eq_zero
    (i : Fin 2) {A V : MvPowerSeries (Fin 2) R}
    (hA0 : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.coeff (e i) (-A * V) =
      - MvPowerSeries.coeff (e i) A * MvPowerSeries.constantCoeff V := by
  rw [coeff_mul_single_one]
  simp [hA0]
  ring

/-- If a power-series unit has constant coefficient `1`, then its inverse also has
constant coefficient `1`. -/
private lemma constantCoeff_unit_inv_eq_one
    (u : Units (MvPowerSeries (Fin 2) R))
    (hu : MvPowerSeries.constantCoeff (u : MvPowerSeries (Fin 2) R) = 1) :
    MvPowerSeries.constantCoeff
      ((u⁻¹ : Units (MvPowerSeries (Fin 2) R)) : MvPowerSeries (Fin 2) R) = 1 := by
  have hmul := congrArg
    (fun f : MvPowerSeries (Fin 2) R => MvPowerSeries.constantCoeff f)
    (Units.mul_inv u)
  -- `constantCoeff` is a ring hom, so the constant coefficient of the product is
  -- the product of constant coefficients.
  simpa [hu] using hmul
```

If the first lemma does not close by the `simp` line in your local revision, replace the proof by this slightly more explicit version of the last two lines:

```lean
  rw [Finsupp.antidiagonal_single]
  rw [Finset.Nat.antidiagonal_succ]
  simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_comm, add_left_comm, add_assoc]
```

The important point is that `Finsupp.antidiagonal_single i 1` reduces the sum to exactly the two terms corresponding to `(0, 1)` and `(1, 0)`.

---

## Generic formalGroupLaw linear-coefficient theorem

Use this theorem for either variable `i = 0` or `i = 1`.

```lean
/-- Linear coefficient of `formalGroupLaw`, assuming the corresponding normalized
coefficient facts for `normalizedAddX` and `normalizedAddY`.

The hypotheses are exactly the facts obtained from the previous quotient-extraction step:
* `hA0`: `normalizedAddX` has zero constant coefficient;
* `hAi`: its `i`th linear coefficient is `-1`;
* `hB0`: `normalizedAddY` has constant coefficient `1`.
-/
lemma formalGroupLaw_coeff_single_one_of_normalizedAddX
    (W : WeierstrassCurve R) (i : Fin 2)
    (hA0 : MvPowerSeries.constantCoeff (normalizedAddX W) = 0)
    (hAi : MvPowerSeries.coeff (e i) (normalizedAddX W) = (-1 : R))
    (hB0 : MvPowerSeries.constantCoeff (normalizedAddY W) = 1) :
    MvPowerSeries.coeff (e i) (formalGroupLaw W) = (1 : R) := by
  classical
  let A : MvPowerSeries (Fin 2) R := normalizedAddX W
  let u : Units (MvPowerSeries (Fin 2) R) := (normalizedAddY_isUnit W).unit
  let V : MvPowerSeries (Fin 2) R :=
    ((u⁻¹ : Units (MvPowerSeries (Fin 2) R)) : MvPowerSeries (Fin 2) R)

  have hA0' : MvPowerSeries.constantCoeff A = 0 := by
    simpa [A] using hA0

  have hAi' : MvPowerSeries.coeff (e i) A = (-1 : R) := by
    simpa [A] using hAi

  have hu0 : MvPowerSeries.constantCoeff (u : MvPowerSeries (Fin 2) R) = 1 := by
    -- Usually this is just `simpa [u] using hB0` because `u.val = normalizedAddY W`.
    -- If your local `IsUnit.unit_spec` has the opposite orientation, the `simp`
    -- line below handles it as long as the theorem is visible.
    simpa [u, (normalizedAddY_isUnit W).unit_spec] using hB0

  have hV0 : MvPowerSeries.constantCoeff V = 1 := by
    simpa [V] using constantCoeff_unit_inv_eq_one (R := R) u hu0

  calc
    MvPowerSeries.coeff (e i) (formalGroupLaw W)
        = MvPowerSeries.coeff (e i) (-A * V) := by
            simp [formalGroupLaw, A, V, u]
    _ = - MvPowerSeries.coeff (e i) A * MvPowerSeries.constantCoeff V := by
            exact coeff_neg_mul_single_one_of_constantCoeff_eq_zero
              (R := R) (i := i) (A := A) (V := V) hA0'
    _ = 1 := by
            simp [hAi', hV0]
```

The proof uses only the linear product formula.  Notice that it never needs to know any higher coefficients of `↑u⁻¹`; those cannot contribute to degree `1`.

---

## Specializations to `X₀` and `X₁`

Assuming the quotient-extraction lemmas have the names from the previous plan:

```lean
normalizedAddX_constantCoeff      : constantCoeff (normalizedAddX W) = 0
normalizedAddX_lin_coeff_X        : coeff (single 0 1) (normalizedAddX W) = -1
normalizedAddX_lin_coeff_Y        : coeff (single 1 1) (normalizedAddX W) = -1
normalizedAddY_constantCoeff      : constantCoeff (normalizedAddY W) = 1
```

then the two formal-group linear coefficient proofs are just:

```lean
lemma formalGroupLaw_coeff_X0
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (formalGroupLaw W) = (1 : R) := by
  exact formalGroupLaw_coeff_single_one_of_normalizedAddX
    (W := W) (i := (0 : Fin 2))
    (hA0 := normalizedAddX_constantCoeff W)
    (hAi := normalizedAddX_lin_coeff_X W)
    (hB0 := normalizedAddY_constantCoeff W)

lemma formalGroupLaw_coeff_X1
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (formalGroupLaw W) = (1 : R) := by
  exact formalGroupLaw_coeff_single_one_of_normalizedAddX
    (W := W) (i := (1 : Fin 2))
    (hA0 := normalizedAddX_constantCoeff W)
    (hAi := normalizedAddX_lin_coeff_Y W)
    (hB0 := normalizedAddY_constantCoeff W)

end WeierstrassCurve
```

If your local names differ, only the four lemma names in the final two proofs need changing.  The three reusable lemmas above should remain unchanged.

---

## Why this avoids the unit-coefficient trap

A tempting but brittle route is to prove a special theorem about coefficients of `↑u⁻¹`.  You do not need that.  At degree `1`, `coeff_mul` sees only two splittings:

```text
(single i 1) = 0 + single i 1
(single i 1) = single i 1 + 0.
```

Since `constantCoeff(normalizedAddX W) = 0`, the first splitting contributes zero.  The second splitting uses only

```lean
constantCoeff (↑u⁻¹) = 1,
```

which follows from applying `constantCoeff` to `↑u * ↑u⁻¹ = 1`.  That is the full bridge from the normalized quotient coefficients to the formal-group linear coefficients.
