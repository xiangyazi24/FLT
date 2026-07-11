import Mathlib.Tactic

/-!
# Residual cover wrappers for the shifted N=12 elliptic curve

This module contains the elementary algebra for the two global residual covers
in the full `2`-cover route for
`E1 : Y² = X(X-1)(X+3)`.  The hard arithmetic input is the named residual
`FourRatSquaresAPConst`.
-/

namespace MazurProof.RationalPointsN12

/-- Rational full-cover equations for fixed squareclass representatives. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2 ∧
  (d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2

/-- Fermat's theorem that four rational squares in arithmetic progression are
constant.  Kept as a named global residual for the E1 full-cover route. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
    y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- Independent double-leg right-triangle obstruction, stated locally for the
degenerate full-cover residuals. -/
def DoubleLegCoverDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h ^ 2 = x ^ 2 + y ^ 2 →
    k ^ 2 = (2 * x) ^ 2 + y ^ 2 →
    x = 0 ∨ y = 0

private theorem sq_div_eq_one_of_sq_eq {a t : ℚ}
    (ht : t ≠ 0) (h : a ^ 2 = t ^ 2) :
    (a / t) ^ 2 = 1 := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  calc
    (a / t) ^ 2 = a ^ 2 / t ^ 2 := by ring
    _ = t ^ 2 / t ^ 2 := by rw [h]
    _ = 1 := div_self ht2

/-- The `(3,2,6)` residual cover gives the AP
`B², A², C², T²`, hence all four squares are equal. -/
theorem coverQ_3_2_6_AP_const
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    T ^ 2 = C ^ 2 ∧ C ^ 2 = A ^ 2 ∧ A ^ 2 = B ^ 2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : A ^ 2 - B ^ 2 = C ^ 2 - A ^ 2 := by
    nlinarith [h1, h2]
  have hap2 : C ^ 2 - A ^ 2 = T ^ 2 - C ^ 2 := by
    nlinarith [h2]
  have hconst := hAP (w := B) (x := A) (y := C) (z := T) hap1 hap2
  rcases hconst with ⟨hBA, hAC, hCT⟩
  exact ⟨hCT.symm, hAC.symm, hBA.symm⟩

/-- The `(-1,-2,2)` residual cover gives the AP
`A², B², T², C²`, hence all four squares are equal. -/
theorem coverQ_neg1_neg2_2_AP_const
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A ^ 2 = B ^ 2 ∧ B ^ 2 = T ^ 2 ∧ T ^ 2 = C ^ 2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : B ^ 2 - A ^ 2 = T ^ 2 - B ^ 2 := by
    nlinarith [h1]
  have hap2 : T ^ 2 - B ^ 2 = C ^ 2 - T ^ 2 := by
    nlinarith [h1, h2]
  exact hAP (w := A) (x := B) (y := T) (z := C) hap1 hap2

/-- On the `(3,2,6)` residual cover, the squareclass formula
`X = 3*(A/T)^2` forces `X = 3`. -/
theorem coverQ_3_2_6_forces_X_eq_three
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (3 : ℚ) * (A / T) ^ 2)
    (hcover : CoverQ 3 2 6 A B C T) :
    X = 3 := by
  have hconst := coverQ_3_2_6_AP_const hAP hcover
  rcases hconst with ⟨hTC, hCA, _hAB⟩
  have hAT : A ^ 2 = T ^ 2 := by
    nlinarith [hTC, hCA]
  have hratio : (A / T) ^ 2 = 1 := sq_div_eq_one_of_sq_eq hT hAT
  rw [hratio] at hX
  norm_num at hX
  exact hX

/-- On the `(-1,-2,2)` residual cover, the squareclass formula
`X = -1*(A/T)^2` forces `X = -1`. -/
theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (-1 : ℚ) * (A / T) ^ 2)
    (hcover : CoverQ (-1) (-2) 2 A B C T) :
    X = -1 := by
  have hconst := coverQ_neg1_neg2_2_AP_const hAP hcover
  rcases hconst with ⟨hAB, hBT, _hTC⟩
  have hAT : A ^ 2 = T ^ 2 := by
    nlinarith [hAB, hBT]
  have hratio : (A / T) ^ 2 = 1 := sq_div_eq_one_of_sq_eq hT hAT
  rw [hratio] at hX
  norm_num at hX
  exact hX

/-- The `(1,1,1)` cover is a double-leg right-triangle configuration, hence
has no solution with `B,T` both nonzero. -/
theorem coverQ_1_1_1_no_nonzero_of_doubleLeg
    (hDL : DoubleLegCoverDegenerate)
    {A B C T : ℚ}
    (_hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0) (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    False := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : A ^ 2 = T ^ 2 + B ^ 2 := by
    nlinarith [h1]
  have hpy2 : C ^ 2 = (2 * T) ^ 2 + B ^ 2 := by
    nlinarith [h1, h2]
  rcases hDL hpy1 hpy2 with hT0 | hB0
  · exact hT hT0
  · exact hB hB0

/-- The `(-3,-1,3)` cover is a double-leg right-triangle configuration, hence
has no solution with `A,C` both nonzero. -/
theorem coverQ_neg3_neg1_3_no_nonzero_of_doubleLeg
    (hDL : DoubleLegCoverDegenerate)
    {A B C T : ℚ}
    (hA : A ≠ 0) (_hB : B ≠ 0) (hC : C ≠ 0) (_hT : T ≠ 0)
    (h : CoverQ (-3) (-1) 3 A B C T) :
    False := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : T ^ 2 = A ^ 2 + C ^ 2 := by
    nlinarith [h2]
  have hpy2 : B ^ 2 = (2 * A) ^ 2 + C ^ 2 := by
    nlinarith [h1, h2]
  rcases hDL hpy1 hpy2 with hA0 | hC0
  · exact hA hA0
  · exact hC hC0

end MazurProof.RationalPointsN12
