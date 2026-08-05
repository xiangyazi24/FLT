import FLT.Assumptions.MazurProof.X017IsogenySequence
import FLT.Assumptions.MazurProof.RationalPointsN15Descent

/-!
# First-coordinate descent on the standard `X₀(17)` curve

The standard source model is

`y² = x(x² + 30x + 289)`.

The quadratic factor is everywhere positive over `ℚ`, so every nonzero
rational first coordinate is positive.  Clearing square denominators and
extracting the squarefree core shows that this coordinate has squareclass
`1` or `17`.  This is the arithmetic input for the right endpoint of the
two-isogeny exact sequence; no quotient-cardinality conclusion is asserted
until explicit dual-isogeny preimages are constructed.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017Descent

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.RationalPointsN15Descent
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model

/-! ## Squarefree divisors of the constant coefficient -/

/-- A squarefree divisor of `17²` is either `1` or `17`. -/
theorem squarefree_dvd_289 {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 289) :
    d = 1 ∨ d = 17 := by
  have hpow : d ∣ 17 ^ 2 := by
    norm_num at hdiv ⊢
    exact hdiv
  have hd17 : d ∣ 17 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  exact (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hd17

/-! ## Rational squareclasses on the source model -/

/-- A nonzero affine point on the standard source model has positive first
coordinate of squareclass `1` or `17`. -/
theorem source_x_squareclass {x y : ℚ}
    (h : Equation standard x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = 17 * q ^ 2 := by
  have hcurve0 :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h
  have hcurve :
      y ^ 2 = x ^ 3 + (30 : ℚ) * x ^ 2 + (289 : ℚ) * x := by
    norm_num [a17, b17, veluT] at hcurve0
    nlinarith
  have hquad_pos : 0 < x ^ 2 + 30 * x + 289 := by
    nlinarith [sq_nonneg (x + 15)]
  have hx_nonneg : 0 ≤ x := by
    have hfactor : y ^ 2 = x * (x ^ 2 + 30 * x + 289) := by
      nlinarith
    nlinarith [sq_nonneg y]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    integral_model_monic 30 289 x y hcurve
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    norm_num
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel
  rcases squarefree_dvd_289 hd (by simpa using hdiv) with rfl | rfl
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
      rw [hx, hA]
      push_cast
      ring
    · exfalso
      rw [hx, hA] at hx_pos
      push_cast at hx_pos
      have hnum : -(1 * (r : ℚ) ^ 2) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
      have hden : 0 ≤ (B : ℚ) ^ 2 := sq_nonneg _
      exact (not_lt_of_ge
        (div_nonpos_of_nonpos_of_nonneg hnum hden)) hx_pos
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
      rw [hx, hA]
      push_cast
      ring
    · exfalso
      rw [hx, hA] at hx_pos
      push_cast at hx_pos
      have hnum : -(17 * (r : ℚ) ^ 2) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
      have hden : 0 ≤ (B : ℚ) ^ 2 := sq_nonneg _
      exact (not_lt_of_ge
        (div_nonpos_of_nonpos_of_nonneg hnum hden)) hx_pos

end MazurProof.X017Descent
