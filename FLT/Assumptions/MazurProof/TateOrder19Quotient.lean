import FLT.Assumptions.MazurProof.N19SutherlandModels

/-!
# The algebraic order-nineteen quotient argument

The only arithmetic input to this file is the statement that every affine
rational point on

`v² + v = u³ + u² + u`

has `u=0`.  From that input, the explicit identities in
`N19SutherlandModels` exclude every rational solution of the Tate division
factor `F₁₉(b,c)=0` with `b ≠ 0`.

This is a direct algebraic proof.  It does not use a modular interpretation
of either affine model or of the quotient map.
-/

namespace MazurProof.TateOrder19Quotient

open N19SutherlandModels

noncomputable section

set_option maxHeartbeats 0 in
/-- The rational-point classification of the genus-one quotient implies the
global nonvanishing statement required by the order-nineteen exclusion. -/
theorem no_F19_rational_solution_of_diamond_x_eq_zero
    (hclass :
      ∀ u v : ℚ, diamondResidual u v = 0 → u = 0)
    (b c : ℚ) (hb : b ≠ 0) :
    TateNFDivision.F19 b c ≠ 0 := by
  intro hF19
  have hc : c ≠ 0 := by
    intro hc
    subst c
    norm_num [TateNFDivision.F19] at hF19
    exact hb hF19
  have hbc : b - c ≠ 0 := by
    intro hbc
    have hbeq : b = c := sub_eq_zero.mp hbc
    rw [hbeq] at hF19 hb
    norm_num [TateNFDivision.F19] at hF19
    ring_nf at hF19
    exact hb (eq_zero_of_pow_eq_zero hF19)
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hr : r ≠ 0 := by
    exact div_ne_zero hb hc
  have hs : s ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hc) hbc
  have hr1 : r - 1 ≠ 0 := by
    intro hr1
    have hrEq : r = 1 := sub_eq_zero.mp hr1
    apply hbc
    dsimp [r] at hrEq
    field_simp [hc] at hrEq
    linarith
  have hcCoord : c = s * (r - 1) := by
    dsimp [r, s]
    field_simp [hc, hbc]
  have hbCoord : b = r * s * (r - 1) := by
    calc
      b = r * c := by
        dsimp [r]
        field_simp [hc]
      _ = r * s * (r - 1) := by rw [hcCoord]; ring
  have hraw : rawF19 r s = 0 := by
    rw [hbCoord, hcCoord, F19_raw_identity] at hF19
    exact (mul_eq_zero.mp hF19).resolve_left
      (mul_ne_zero (pow_ne_zero 15 hs) (pow_ne_zero 24 hr1))
  have hrs : r - s ≠ 0 :=
    raw_r_sub_s_ne_zero hs hr1 hraw
  have hs1 : s - 1 ≠ 0 :=
    raw_s_sub_one_ne_zero hr1 hraw
  have hxFactor : rawXFactor r s ≠ 0 :=
    rawXFactor_ne_zero hr hr1 hraw
  have hdelta : rawDelta r s ≠ 0 :=
    rawDelta_ne_zero hs hr1 hraw
  let x : ℚ := rawToOptX r s
  let y : ℚ := rawToOptY r s
  have hx : x ≠ 0 := by
    dsimp [x]
    exact rawToOptX_ne_zero hs1 hxFactor hdelta
  have hopt : optF19 x y = 0 := by
    dsimp [x, y]
    rw [raw_to_opt_residual_identity hrs hdelta, hraw]
    ring
  let u : ℚ := diamondU x y
  let v : ℚ := diamondV x y
  have hdiamond : diamondResidual u v = 0 := by
    dsimp [u, v]
    rw [diamond_residual_identity hx, hopt]
    ring
  have hu : u = 0 := hclass u v hdiamond
  have hxneg : x = -1 := by
    apply x_eq_neg_one_of_diamondU_eq_zero hx hopt
    exact hu
  have hxnot : rawToOptX r s ≠ -1 :=
    rawToOptX_ne_neg_one hs hr1 hraw hdelta
  exact hxnot (by simpa [x] using hxneg)

end

end MazurProof.TateOrder19Quotient
