import Mathlib

/-!
# The explicit 2-isogeny for the `20.a4` obstruction curve

This scratch file records the raw affine formula check for

`E  : y² = x³ + x² - x`
`E' : Y² = X³ - 2X² + 5X`.
-/

open scoped WeierstrassCurve.Affine

namespace Isogeny20a4

def E20 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -1
  a₆ := 0

def E20' : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -2
  a₃ := 0
  a₄ := 5
  a₆ := 0

lemma E20_delta : E20.Δ = (80 : ℚ) := by
  norm_num [E20, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma E20'_delta : E20'.Δ = (-6400 : ℚ) := by
  norm_num [E20', WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E20_isElliptic : E20.IsElliptic where
  isUnit := by
    rw [E20_delta]
    norm_num

instance E20'_isElliptic : E20'.IsElliptic where
  isUnit := by
    rw [E20'_delta]
    norm_num

def phiX (x y : ℚ) : ℚ :=
  y ^ 2 / x ^ 2

def phiY (x y : ℚ) : ℚ :=
  -y * (x ^ 2 + 1) / x ^ 2

def dualPhiX (x y : ℚ) : ℚ :=
  y ^ 2 / (4 * x ^ 2)

def dualPhiY (x y : ℚ) : ℚ :=
  y * (5 - x ^ 2) / (8 * x ^ 2)

/--
The affine formula for the 2-isogeny sends points on
`y² = x³ + x² - x`, away from the kernel point `x = 0`, to points on
`Y² = X³ - 2X² + 5X`.
-/
theorem phi_affine_equation {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + x ^ 2 - x) (hx : x ≠ 0) :
    (phiY x y) ^ 2 =
      (phiX x y) ^ 3 - 2 * (phiX x y) ^ 2 + 5 * (phiX x y) := by
  dsimp [phiX, phiY]
  field_simp [hx]
  rw [h]
  ring

/-- The same check phrased using Mathlib's affine equation predicate. -/
theorem phi_affine_equation_of_Equation {x y : ℚ}
    (h : WeierstrassCurve.Affine.Equation E20 x y) (hx : x ≠ 0) :
    WeierstrassCurve.Affine.Equation E20' (phiX x y) (phiY x y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  norm_num [E20, E20'] at h ⊢
  have hraw : y ^ 2 = x ^ 3 + x ^ 2 - x := by
    simpa [sub_eq_add_neg] using h
  simpa [sub_eq_add_neg] using phi_affine_equation hraw hx

/--
The dual affine formula sends points on
`Y² = X³ - 2X² + 5X`, away from the kernel point `X = 0`, back to points on
`y² = x³ + x² - x`.
-/
theorem dual_phi_affine_equation (X Y : ℚ) (hX : X ≠ 0)
    (hE' : Y ^ 2 = X ^ 3 - 2 * X ^ 2 + 5 * X) :
    (dualPhiY X Y) ^ 2 =
      (dualPhiX X Y) ^ 3 + (dualPhiX X Y) ^ 2 - (dualPhiX X Y) := by
  dsimp [dualPhiX, dualPhiY]
  field_simp [hX]
  rw [hE']
  ring

/-- The dual formula phrased using Mathlib's affine equation predicate. -/
theorem dual_phi_affine_equation_of_Equation {X Y : ℚ}
    (h : WeierstrassCurve.Affine.Equation E20' X Y) (hX : X ≠ 0) :
    WeierstrassCurve.Affine.Equation E20 (dualPhiX X Y) (dualPhiY X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  norm_num [E20, E20'] at h ⊢
  have hraw : Y ^ 2 = X ^ 3 - 2 * X ^ 2 + 5 * X := by
    simpa [sub_eq_add_neg] using h
  simpa [sub_eq_add_neg] using dual_phi_affine_equation X Y hX hraw

theorem phi_at_1_1 : phiX 1 1 = 1 ∧ phiY 1 1 = -2 := by
  constructor <;> norm_num [phiX, phiY]

theorem phi_at_neg1_1 : phiX (-1) 1 = 1 ∧ phiY (-1) 1 = -2 := by
  constructor <;> norm_num [phiX, phiY]

end Isogeny20a4
