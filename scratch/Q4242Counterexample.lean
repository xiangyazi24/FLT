import Mathlib

set_option autoImplicit false

noncomputable section

namespace N15Counterexample

open WeierstrassCurve

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The good model in the question. -/
def E0 : WeierstrassCurve ℚ :=
  ⟨1, 1, 1, -5, 2⟩

lemma E0_discriminant : E0.Δ = (225 : ℚ) := by
  norm_num [E0, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E0.IsElliptic := by
  refine ⟨?_⟩
  rw [E0_discriminant]
  norm_num

abbrev Pt := WeierstrassCurve.Affine.Point E0

lemma T_equation : WeierstrassCurve.Affine.Equation E0 (3 / 4 : ℚ) (-7 / 8 : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E0]

def T : Pt := .mk T_equation

lemma T_ne_zero : T ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

lemma T_negY : (-7 / 8 : ℚ) =
    WeierstrassCurve.Affine.negY E0 (3 / 4 : ℚ) (-7 / 8 : ℚ) := by
  norm_num [WeierstrassCurve.Affine.negY, E0]

/-- This is the image of `(15,0)` under the stated integral change of variables. -/
lemma two_nsmul_T : 2 • T = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq T_negY

def formalParameter (P : Pt) : ℚ :=
  match P with
  | 0 => 0
  | .some x y _ => -x / y

def formalW (P : Pt) : ℚ :=
  match P with
  | 0 => 0
  | .some _ y _ => -1 / y

lemma formalParameter_T : formalParameter T = 6 / 7 := by
  norm_num [formalParameter, T]

lemma formalW_T : formalW T = 8 / 7 := by
  norm_num [formalW, T]

lemma v2_formalParameter_T :
    padicValRat 2 (formalParameter T) = 1 := by
  rw [formalParameter_T]
  norm_num [padicValRat, padicValInt, padicValNat]

lemma v2_formalW_T :
    padicValRat 2 (formalW T) = 3 := by
  rw [formalW_T]
  norm_num [padicValRat, padicValInt, padicValNat]

lemma formalParameter_two_T : formalParameter (2 • T) = 0 := by
  rw [two_nsmul_T]
  rfl

/-- Therefore the inequality requested in the question is false for ordinary
`padicValRat`, whose value at zero is defined to be zero. -/
theorem requested_v2_inequality_is_false :
    ¬(padicValRat 2 (formalParameter T) + 1 ≤
        padicValRat 2 (formalParameter (2 • T))) := by
  rw [v2_formalParameter_T, formalParameter_two_T]
  norm_num

end N15Counterexample
