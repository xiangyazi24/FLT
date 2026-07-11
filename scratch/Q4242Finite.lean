import Mathlib

set_option autoImplicit false

namespace N15Finite

/-- The original auxiliary curve in affine coordinates. -/
def OnE (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 15) * (X - 16)

/-- The affine `X`-coordinate of the double, away from 2-torsion. -/
def dupX (X Y : ℚ) : ℚ :=
  (X ^ 2 - 240) ^ 2 / (4 * Y ^ 2)

lemma zero_ordinate_candidates {X : ℚ}
    (h : OnE X 0) : X = 0 ∨ X = 15 ∨ X = 16 := by
  unfold OnE at h
  norm_num at h
  rcases mul_eq_zero.mp h.symm with hX | hrest
  · exact Or.inl hX
  rcases mul_eq_zero.mp hrest with h15 | h16
  · exact Or.inr (Or.inl (sub_eq_zero.mp h15))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h16))

lemma no_rational_sq_240 {X : ℚ} : X ^ 2 ≠ 240 := by
  intro hX
  have hs : IsSquare (240 : ℚ) := by
    refine ⟨X, ?_⟩
    simpa [pow_two] using hX.symm
  have hsZ : IsSquare (240 : ℤ) :=
    Rat.isSquare_intCast_iff.mp hs
  norm_num at hsZ

lemma dupX_ne_zero {X Y : ℚ}
    (hY : Y ≠ 0) : dupX X Y ≠ 0 := by
  intro h0
  have hden : (4 * Y ^ 2 : ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hY)
  have hnum : (X ^ 2 - 240) ^ 2 = 0 := by
    rw [dupX] at h0
    exact (div_eq_zero_iff.mp h0).resolve_right hden
  have : X ^ 2 = 240 := by nlinarith
  exact no_rational_sq_240 this

lemma dupX_eq_fifteen_impossible {X Y : ℚ}
    (hE : OnE X Y) (hY : Y ≠ 0)
    (h15 : dupX X Y = 15) : False := by
  have hden : (4 * Y ^ 2 : ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hY)
  have hraw : (X ^ 2 - 240) ^ 2 = 15 * (4 * Y ^ 2) := by
    rw [dupX] at h15
    exact (div_eq_iff hden).mp h15
  have hq : (X ^ 2 - 30 * X + 240) ^ 2 = 0 := by
    calc
      (X ^ 2 - 30 * X + 240) ^ 2 =
          (X ^ 2 - 240) ^ 2 - 60 * (X * (X - 15) * (X - 16)) := by ring
      _ = (X ^ 2 - 240) ^ 2 - 60 * Y ^ 2 := by rw [hE]
      _ = 0 := by linarith
  have hq0 : X ^ 2 - 30 * X + 240 = 0 := by nlinarith
  nlinarith [sq_nonneg (X - 15)]

lemma dupX_eq_sixteen_candidates {X Y : ℚ}
    (hE : OnE X Y) (hY : Y ≠ 0)
    (h16 : dupX X Y = 16) :
    (X = 12 ∧ (Y = 12 ∨ Y = -12)) ∨
      (X = 20 ∧ (Y = 20 ∨ Y = -20)) := by
  have hden : (4 * Y ^ 2 : ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hY)
  have hraw : (X ^ 2 - 240) ^ 2 = 16 * (4 * Y ^ 2) := by
    rw [dupX] at h16
    exact (div_eq_iff hden).mp h16
  have hfacSq : ((X - 12) * (X - 20)) ^ 2 = 0 := by
    calc
      ((X - 12) * (X - 20)) ^ 2 =
          (X ^ 2 - 240) ^ 2 - 64 * (X * (X - 15) * (X - 16)) := by ring
      _ = (X ^ 2 - 240) ^ 2 - 64 * Y ^ 2 := by rw [hE]
      _ = 0 := by linarith
  have hfac : (X - 12) * (X - 20) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h12 | h20
  · left
    have hX : X = 12 := sub_eq_zero.mp h12
    refine ⟨hX, ?_⟩
    have hYsq : Y ^ 2 = (12 : ℚ) ^ 2 := by
      rw [hX] at hE
      norm_num [OnE] at hE ⊢
      exact hE
    exact eq_or_eq_neg_of_sq_eq_sq Y 12 hYsq
  · right
    have hX : X = 20 := sub_eq_zero.mp h20
    refine ⟨hX, ?_⟩
    have hYsq : Y ^ 2 = (20 : ℚ) ^ 2 := by
      rw [hX] at hE
      norm_num [OnE] at hE ⊢
      exact hE
    exact eq_or_eq_neg_of_sq_eq_sq Y 20 hYsq

/-- The finite duplication-polynomial endpoint used after proving `4P=O`. -/
theorem affine_candidates_of_double_two_torsion {X Y : ℚ}
    (hE : OnE X Y)
    (hdup : Y = 0 ∨ dupX X Y = 0 ∨ dupX X Y = 15 ∨ dupX X Y = 16) :
    (X = 0 ∧ Y = 0) ∨
      (X = 15 ∧ Y = 0) ∨
      (X = 16 ∧ Y = 0) ∨
      (X = 12 ∧ (Y = 12 ∨ Y = -12)) ∨
      (X = 20 ∧ (Y = 20 ∨ Y = -20)) := by
  rcases hdup with hY0 | h0 | h15 | h16
  · subst Y
    rcases zero_ordinate_candidates hE with hX | hX | hX
    · exact Or.inl ⟨hX, rfl⟩
    · exact Or.inr (Or.inl ⟨hX, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hX, rfl⟩))
  · exact (dupX_ne_zero (by aesop) h0).elim
  · exact (dupX_eq_fifteen_impossible hE (by aesop) h15).elim
  · rcases dupX_eq_sixteen_candidates hE (by aesop) h16 with h12 | h20
    · exact Or.inr (Or.inr (Or.inr (Or.inl h12)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h20)))

end N15Finite
