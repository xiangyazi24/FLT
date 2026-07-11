import Mathlib

set_option autoImplicit false

noncomputable section

namespace N15Points

open WeierstrassCurve

/-- The original auxiliary curve `Y² = X(X-15)(X-16)`. -/
def E15 : WeierstrassCurve ℚ :=
  ⟨0, -31, 0, 240, 0⟩

lemma E15_discriminant : E15.Δ = (921600 : ℚ) := by
  norm_num [E15, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E15.IsElliptic := by
  refine ⟨?_⟩
  rw [E15_discriminant]
  norm_num

abbrev Pt := E15.Affine.Point

lemma equation_iff_onE (X Y : ℚ) :
    E15.Affine.Equation X Y ↔ Y ^ 2 = X * (X - 15) * (X - 16) := by
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

/-- The advertised set contains eight points: the point at infinity and seven affine points. -/
def Listed (P : Pt) : Prop :=
  P = 0 ∨ P = P00 ∨ P = P150 ∨ P = P160 ∨
    P = P12p ∨ P = P12m ∨ P = P20p ∨ P = P20m

end N15Points
