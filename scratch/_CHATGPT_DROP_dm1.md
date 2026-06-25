# Q615 (dm1): `normalizedAddY_constantCoeff` by coefficient extraction

Below is the complete patch I would use.  It proves the coefficient-extraction lemma once, then the final theorem is a three-line argument from `formalAddY_eq_cube_mul` and the raw numerator coefficient.

The only project-local name I had to guess is the raw numerator coefficient lemma.  I call it

```lean
formalAddY_coeff_single0_three
```

with expected statement

```lean
MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) W.formalAddY = 1
```

If your lemma has a different name, change only that one line in the final theorem.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

open Finsupp

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

/-- The bidegree `(3,0)`. -/
private abbrev e30 : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) 3

private lemma not_single1_le_e30 :
    ¬ Finsupp.single (1 : Fin 2) 1 ≤ e30 := by
  intro h
  have h1 : (1 : ℕ) ≤ 0 := by
    simpa [e30] using h (1 : Fin 2)
  exact Nat.not_succ_le_zero 0 h1

/-- Coefficient `(3,0)` of `X₁ * q` is zero. -/
private lemma coeff_e30_X1_mul (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) * q) = 0 := by
  classical
  rw [MvPowerSeries.X_def (R := R) (s := (1 : Fin 2))]
  rw [MvPowerSeries.coeff_monomial_mul
    (m := e30)
    (n := Finsupp.single (1 : Fin 2) 1)
    (φ := q)
    (a := (1 : R))]
  simp [not_single1_le_e30]

/-- Coefficient `(3,0)` of `X₀^3 * q` is the constant coefficient of `q`. -/
private lemma coeff_e30_X0_cube_mul (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      (((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 3) * q) =
        MvPowerSeries.constantCoeff q := by
  classical
  rw [MvPowerSeries.X_pow_eq (R := R) (s := (0 : Fin 2)) (n := 3)]
  rw [MvPowerSeries.coeff_monomial_mul
    (m := e30)
    (n := e30)
    (φ := q)
    (a := (1 : R))]
  have hsub : e30 - e30 = (0 : Fin 2 →₀ ℕ) := by
    simp [e30]
  simp [e30, hsub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The coefficient `(3,0)` of `(X₀-X₁)^3 * q` extracts the constant coefficient of `q`. -/
private lemma coeff_e30_X0_sub_X1_cube_mul (q : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff e30
      ((((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) -
          (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) ^ 3) * q) =
        MvPowerSeries.constantCoeff q := by
  classical
  let X0 : MvPowerSeries (Fin 2) R := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) R := MvPowerSeries.X (1 : Fin 2)
  let A : MvPowerSeries (Fin 2) R :=
    -(3 : MvPowerSeries (Fin 2) R) * X0 ^ 2 +
      (3 : MvPowerSeries (Fin 2) R) * X0 * X1 - X1 ^ 2
  change MvPowerSeries.coeff e30 ((X0 - X1) ^ 3 * q) =
    MvPowerSeries.constantCoeff q
  have hsplit : (X0 - X1) ^ 3 = X0 ^ 3 + X1 * A := by
    dsimp [A, X0, X1]
    ring
  have hmain : MvPowerSeries.coeff e30 (X0 ^ 3 * q) =
      MvPowerSeries.constantCoeff q := by
    dsimp [X0]
    exact coeff_e30_X0_cube_mul (R := R) q
  have hzero : MvPowerSeries.coeff e30 ((X1 * A) * q) = 0 := by
    rw [mul_assoc]
    dsimp [X1]
    exact coeff_e30_X1_mul (R := R) (A * q)
  rw [hsplit, add_mul]
  simp only [map_add]
  rw [hmain, hzero, add_zero]

/-- Version that isolates the only project-local input: the raw numerator coefficient. -/
theorem normalizedAddY_constantCoeff_of_formalAddY_coeff
    (W : WeierstrassCurve R)
    (hraw : MvPowerSeries.coeff e30 W.formalAddY = 1) :
    MvPowerSeries.constantCoeff W.normalizedAddY = 1 := by
  classical
  have hcoeff := congrArg (MvPowerSeries.coeff (R := R) e30)
    (formalAddY_eq_cube_mul W)
  rw [hraw] at hcoeff
  rw [coeff_e30_X0_sub_X1_cube_mul (R := R) W.normalizedAddY] at hcoeff
  exact hcoeff.symm

/-- The normalized `Y` quotient has constant coefficient `1`. -/
theorem normalizedAddY_constantCoeff (W : WeierstrassCurve R) :
    MvPowerSeries.constantCoeff W.normalizedAddY = 1 := by
  classical
  apply normalizedAddY_constantCoeff_of_formalAddY_coeff (W := W)
  -- Replace this line if your raw coefficient lemma has a different name.
  simpa [e30] using formalAddY_coeff_single0_three W

end

end WeierstrassCurve
```

## If you want to see the hidden `coeff_mul`/antidiagonal content

The helper `coeff_e30_X1_mul` and `coeff_e30_X0_cube_mul` use `MvPowerSeries.coeff_monomial_mul`, which is the specialized form of `MvPowerSeries.coeff_mul` for a monomial on the left.  This avoids explicitly enumerating the four antidiagonal decompositions of `(3,0)`, but it is proving the exact same convolution statement:

* `X₀^3 * q` contributes only the decomposition `(3,0)+(0,0)`;
* every term with a left factor `X₁` has zero `(3,0)` coefficient because `single 1 1 ≤ single 0 3` is false.

This is much more robust than manually rewriting the whole `Finsupp.antidiagonal e30` sum.
