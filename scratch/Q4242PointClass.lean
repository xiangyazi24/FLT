import Mathlib

set_option autoImplicit false

noncomputable section

namespace N15PointClass

open WeierstrassCurve

/-- The original auxiliary curve. -/
def E15 : WeierstrassCurve ℚ :=
  ⟨0, -31, 0, 240, 0⟩

lemma E15_discriminant : E15.Δ = (921600 : ℚ) := by
  norm_num [E15, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E15.IsElliptic := by
  refine ⟨?_⟩
  rw [E15_discriminant]
  norm_num

abbrev Pt := WeierstrassCurve.Affine.Point E15

lemma equation_iff_onE (X Y : ℚ) :
    WeierstrassCurve.Affine.Equation E15 X Y ↔
      Y ^ 2 = X * (X - 15) * (X - 16) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E15]
  ring_nf

def P00 : Pt := .mk (equation_iff_onE 0 0 |>.mpr (by norm_num))
def P150 : Pt := .mk (equation_iff_onE 15 0 |>.mpr (by norm_num))
def P160 : Pt := .mk (equation_iff_onE 16 0 |>.mpr (by norm_num))
def P12p : Pt := .mk (equation_iff_onE 12 12 |>.mpr (by norm_num))
def P12m : Pt := .mk (equation_iff_onE 12 (-12) |>.mpr (by norm_num))
def P20p : Pt := .mk (equation_iff_onE 20 20 |>.mpr (by norm_num))
def P20m : Pt := .mk (equation_iff_onE 20 (-20) |>.mpr (by norm_num))

def Listed (P : Pt) : Prop :=
  P = 0 ∨ P = P00 ∨ P = P150 ∨ P = P160 ∨
    P = P12p ∨ P = P12m ∨ P = P20p ∨ P = P20m

def dupX (X Y : ℚ) : ℚ :=
  (X ^ 2 - 240) ^ 2 / (4 * Y ^ 2)

lemma zero_ordinate_candidates {X : ℚ}
    (h : (0 : ℚ) ^ 2 = X * (X - 15) * (X - 16)) :
    X = 0 ∨ X = 15 ∨ X = 16 := by
  have hp : X * (X - 15) * (X - 16) = 0 := by simpa using h.symm
  rcases mul_eq_zero.mp hp with hleft | h16
  · rcases mul_eq_zero.mp hleft with hX | h15
    · exact Or.inl hX
    · exact Or.inr (Or.inl (sub_eq_zero.mp h15))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h16))

lemma no_rational_sq_240 {X : ℚ} : X ^ 2 ≠ 240 := by
  intro hX
  have hs : IsSquare (240 : ℚ) := by
    refine ⟨X, ?_⟩
    simpa [pow_two] using hX.symm
  have hsZ : IsSquare (240 : ℤ) := Rat.isSquare_intCast_iff.mp hs
  norm_num at hsZ

lemma dupX_ne_zero {X Y : ℚ} (hY : Y ≠ 0) : dupX X Y ≠ 0 := by
  intro h0
  have hden : (4 * Y ^ 2 : ℚ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hY)
  have hnum : (X ^ 2 - 240) ^ 2 = 0 := by
    rw [dupX] at h0
    exact (div_eq_zero_iff.mp h0).resolve_right hden
  have : X ^ 2 = 240 := by nlinarith
  exact no_rational_sq_240 this

lemma dupX_eq_fifteen_impossible {X Y : ℚ}
    (hE : Y ^ 2 = X * (X - 15) * (X - 16)) (hY : Y ≠ 0)
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
    (hE : Y ^ 2 = X * (X - 15) * (X - 16)) (hY : Y ≠ 0)
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
      norm_num at hE ⊢
      exact hE
    exact eq_or_eq_neg_of_sq_eq_sq Y 12 hYsq
  · right
    have hX : X = 20 := sub_eq_zero.mp h20
    refine ⟨hX, ?_⟩
    have hYsq : Y ^ 2 = (20 : ℚ) ^ 2 := by
      rw [hX] at hE
      norm_num at hE ⊢
      exact hE
    exact eq_or_eq_neg_of_sq_eq_sq Y 20 hYsq

lemma negY_E15 (X Y : ℚ) :
    WeierstrassCurve.Affine.negY E15 X Y = -Y := by
  simp [WeierstrassCurve.Affine.negY, E15]

lemma addX_self_eq_dupX {X Y : ℚ}
    (hE : Y ^ 2 = X * (X - 15) * (X - 16)) (hY : Y ≠ 0) :
    WeierstrassCurve.Affine.addX E15 X X
      (WeierstrassCurve.Affine.slope E15 X X Y Y) = dupX X Y := by
  have hy : Y ≠ WeierstrassCurve.Affine.negY E15 X Y := by
    rw [negY_E15]
    intro heq
    apply hY
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp only [WeierstrassCurve.Affine.addX]
  simp [E15]
  field_simp [hY]
  rw [hE]
  ring

/-- Once the separatedness/descent part has proved `4P=0`, the remaining
classification is a finite duplication-polynomial calculation. -/
theorem listed_of_four_nsmul_eq_zero (P : Pt) (h4 : 4 • P = 0) : Listed P := by
  rcases P with _ | ⟨X, Y, hP⟩
  · exact Or.inl rfl
  have hE : Y ^ 2 = X * (X - 15) * (X - 16) :=
    (equation_iff_onE X Y).mp hP.1
  by_cases hY0 : Y = 0
  · subst Y
    rcases zero_ordinate_candidates hE with hX | hX | hX
    · subst X
      exact Or.inr (Or.inl rfl)
    · subst X
      exact Or.inr (Or.inr (Or.inl rfl))
    · subst X
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hy : Y ≠ WeierstrassCurve.Affine.negY E15 X Y := by
    rw [negY_E15]
    intro heq
    apply hY0
    linarith
  let X₂ : ℚ := WeierstrassCurve.Affine.addX E15 X X
    (WeierstrassCurve.Affine.slope E15 X X Y Y)
  let Y₂ : ℚ := WeierstrassCurve.Affine.addY E15 X X Y
    (WeierstrassCurve.Affine.slope E15 X X Y Y)
  have hdouble := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (W := E15) (h₁ := hP) hy
  have h₂ : WeierstrassCurve.Affine.Nonsingular E15 X₂ Y₂ := by
    exact WeierstrassCurve.Affine.nonsingular_add E15 hP hP
  let Q : Pt := WeierstrassCurve.Affine.Point.some X₂ Y₂ h₂
  have hQeq : Q = 2 • (WeierstrassCurve.Affine.Point.some X Y hP : Pt) := by
    dsimp [Q, X₂, Y₂]
    rw [two_nsmul]
    exact hdouble.symm
  have h2Q : 2 • Q = 0 := by
    rw [hQeq]
    calc
      2 • (2 • (WeierstrassCurve.Affine.Point.some X Y hP : Pt)) =
          4 • (WeierstrassCurve.Affine.Point.some X Y hP : Pt) := by
            rw [← mul_nsmul']
            norm_num
      _ = 0 := h4
  have hY₂zero : Y₂ = 0 := by
    by_contra hY₂0
    have hY₂neNeg : Y₂ ≠ WeierstrassCurve.Affine.negY E15 X₂ Y₂ := by
      rw [negY_E15]
      intro heq
      apply hY₂0
      linarith
    have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := E15) (h₁ := h₂) hY₂neNeg
    have hselfzero : Q + Q = 0 := by
      rw [← two_nsmul, h2Q]
    dsimp [Q] at hselfzero
    rw [hselfzero] at hadd
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hadd.symm
  have hX₂root : X₂ = 0 ∨ X₂ = 15 ∨ X₂ = 16 := by
    apply zero_ordinate_candidates
    have heq := h₂.1
    rw [hY₂zero] at heq
    exact (equation_iff_onE X₂ 0).mp heq
  have hX₂dup : X₂ = dupX X Y := by
    dsimp [X₂]
    exact addX_self_eq_dupX hE hY0
  rcases hX₂root with h0 | h15 | h16
  · exfalso
    apply dupX_ne_zero hY0
    rw [← hX₂dup, h0]
  · exfalso
    apply dupX_eq_fifteen_impossible hE hY0
    rw [← hX₂dup, h15]
  · have hdup16 : dupX X Y = 16 := by rw [← hX₂dup, h16]
    rcases dupX_eq_sixteen_candidates hE hY0 hdup16 with h12 | h20
    · rcases h12 with ⟨rfl, rfl | rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · rcases h20 with ⟨rfl, rfl | rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

end N15PointClass
