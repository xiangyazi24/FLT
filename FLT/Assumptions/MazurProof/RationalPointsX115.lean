import FLT.Assumptions.MazurProof.TateOrder18

/-!
# Rational points on X₁(15)

This file proves the rational-point exhaustion for
\`Y² = X(X - 15)(X - 16)\` by explicit two-isogeny descent and
curve-specific two-adic separatedness.
-/

namespace MazurProof.RationalPointsX115

noncomputable section

open Scratch.TateZ2xZ10Reduction

/-- The auxiliary cubic birational to the non-boundary X₁(15) quartic. -/
def OnX115 (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 15) * (X - 16)

/-- The seven affine rational points on the auxiliary cubic. -/
def X115AffineCandidate (X Y : ℚ) : Prop :=
  (X = 0 ∧ Y = 0) ∨
    (X = 15 ∧ Y = 0) ∨
    (X = 16 ∧ Y = 0) ∨
    (X = 12 ∧ Y = 12) ∨
    (X = 12 ∧ Y = -12) ∨
    (X = 20 ∧ Y = 20) ∨
    (X = 20 ∧ Y = -20)

private def N15AuxiliaryEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 15) * (X - 16)

private def N15AuxiliaryAffineCandidate (X Y : ℚ) : Prop :=
  (X = 0 ∧ Y = 0) ∨
    (X = 15 ∧ Y = 0) ∨
    (X = 16 ∧ Y = 0) ∨
    (X = 12 ∧ Y = 12) ∨
    (X = 12 ∧ Y = -12) ∨
    (X = 20 ∧ Y = 20) ∨
    (X = 20 ∧ Y = -20)

/-! ### Kernel-checked finite arithmetic for the two-descent -/

private def n15Reduce16to2 : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_two_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 2 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 120 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_six_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 6 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 40 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_ten_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 10 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 24 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_thirty_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 30 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 8 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_dual_negative_class_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ -(M ^ 4) + 62 * M ^ 2 * N ^ 2 - N ^ 4 := by
  decide

/-- The auxiliary cubic has seven affine points over `𝔽₇`; adding infinity
gives the good-reduction count `#E(𝔽₇)=8`. -/
private theorem n15_auxiliary_affine_mod7_card :
    ((Finset.univ.filter fun P : ZMod 7 × ZMod 7 =>
      P.2 ^ 2 = P.1 * (P.1 - 15) * (P.1 - 16)).card) = 7 := by
  decide

/-! ### The auxiliary two-isogeny as actual elliptic-curve point maps -/

private def n15AuxCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -31
  a₃ := 0
  a₄ := 240
  a₆ := 0

private def n15IsoCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 62
  a₃ := 0
  a₄ := 1
  a₆ := 0

private theorem n15AuxCurve_delta : n15AuxCurve.Δ = (921600 : ℚ) := by
  norm_num [n15AuxCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private theorem n15IsoCurve_delta : n15IsoCurve.Δ = (61440 : ℚ) := by
  norm_num [n15IsoCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance n15AuxCurve_isElliptic : n15AuxCurve.IsElliptic where
  isUnit := by rw [n15AuxCurve_delta]; norm_num

private instance n15IsoCurve_isElliptic : n15IsoCurve.IsElliptic where
  isUnit := by rw [n15IsoCurve_delta]; norm_num

private def N15IsogenousEquation (T V : ℚ) : Prop :=
  V ^ 2 = T ^ 3 + 62 * T ^ 2 + T

@[simp] private theorem n15AuxCurve_equation_iff (X Y : ℚ) :
    WeierstrassCurve.Affine.Equation n15AuxCurve X Y ↔
      N15AuxiliaryEquation X Y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold N15AuxiliaryEquation
  simp [n15AuxCurve]
  ring_nf

@[simp] private theorem n15IsoCurve_equation_iff (T V : ℚ) :
    WeierstrassCurve.Affine.Equation n15IsoCurve T V ↔
      N15IsogenousEquation T V := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold N15IsogenousEquation
  simp [n15IsoCurve]

private abbrev N15AuxPoint :=
  WeierstrassCurve.Affine.Point n15AuxCurve

private abbrev N15IsoPoint :=
  WeierstrassCurve.Affine.Point n15IsoCurve

private def n15ForwardX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2

private def n15ForwardY (x y : ℚ) : ℚ :=
  y * (240 - x ^ 2) / x ^ 2

private def n15DualX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4

private def n15DualY (x y : ℚ) : ℚ :=
  y * (1 - x ^ 2) / x ^ 2 / 8

private theorem n15_forward_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation n15AuxCurve x y) :
    WeierstrassCurve.Affine.Equation n15IsoCurve
      (n15ForwardX x y) (n15ForwardY x y) := by
  rw [n15IsoCurve_equation_iff]
  have hcurve := (n15AuxCurve_equation_iff x y).mp h
  unfold N15AuxiliaryEquation at hcurve
  unfold N15IsogenousEquation n15ForwardX n15ForwardY
  field_simp [hx]
  rw [hcurve]
  ring

private theorem n15_dual_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation n15IsoCurve x y) :
    WeierstrassCurve.Affine.Equation n15AuxCurve
      (n15DualX x y) (n15DualY x y) := by
  rw [n15AuxCurve_equation_iff]
  have hcurve := (n15IsoCurve_equation_iff x y).mp h
  unfold N15IsogenousEquation at hcurve
  unfold N15AuxiliaryEquation n15DualX n15DualY
  field_simp [hx]
  rw [hcurve]
  ring

private noncomputable def n15ForwardPoint : N15AuxPoint → N15IsoPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (n15_forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

private noncomputable def n15DualPoint : N15IsoPoint → N15AuxPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (n15_dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

@[simp] private theorem n15ForwardPoint_zero :
    n15ForwardPoint 0 = 0 := rfl

@[simp] private theorem n15DualPoint_zero :
    n15DualPoint 0 = 0 := rfl

@[simp] private theorem n15ForwardPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x = 0) :
    n15ForwardPoint (.some x y h) = 0 := by
  rw [n15ForwardPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] private theorem n15DualPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x = 0) :
    n15DualPoint (.some x y h) = 0 := by
  rw [n15DualPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

private theorem n15ForwardPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) :
    n15ForwardPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (n15_forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [n15ForwardPoint, hx]

private theorem n15DualPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x ≠ 0) :
    n15DualPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (n15_dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [n15DualPoint, hx]

private def n15DualPreimageX (r y : ℚ) : ℚ :=
  -31 + 2 * r ^ 2 - 2 * y / r

private def n15DualPreimageY (r y : ℚ) : ℚ :=
  2 * r * n15DualPreimageX r y

private def n15ForwardPreimageX (r y : ℚ) : ℚ :=
  (r ^ 2 + 31 - y / r) / 2

private def n15ForwardPreimageY (r y : ℚ) : ℚ :=
  r * n15ForwardPreimageX r y

/-- A square first coordinate on the auxiliary curve has an explicit
preimage under the dual isogeny. -/
private theorem n15_exists_dual_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : N15IsoPoint,
      n15DualPoint Q = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    have heq := (n15AuxCurve_equation_iff x y).mp h.1
    unfold N15AuxiliaryEquation at heq
    nlinarith
  have hcurveR : y ^ 2 = r ^ 6 - 31 * r ^ 4 + 240 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := n15DualPreimageX r y
  let qy := n15DualPreimageY r y
  have hprod :
      qx * (-31 + 2 * r ^ 2 + 2 * y / r) = 1 := by
    dsimp [qx, n15DualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : 1 - qx ^ 2 = 4 * qx * y / r := by
    rw [← hprod]
    dsimp [qx, n15DualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : N15IsogenousEquation qx qy := by
    unfold N15IsogenousEquation
    dsimp [qx, qy, n15DualPreimageX, n15DualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (-2 * r ^ 3 + 31 * r + 2 * y) * hcurveR
  have hqns : WeierstrassCurve.Affine.Nonsingular n15IsoCurve qx qy :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15IsoCurve_equation_iff qx qy).mpr hqeq)
  let Q : N15IsoPoint :=
    WeierstrassCurve.Affine.Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [n15DualPoint_some_of_x_ne_zero hqns hqx]
  change WeierstrassCurve.Affine.Point.some
      (n15DualX qx qy) (n15DualY qx qy) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / qx ^ 2 / 4 = x
    rw [hr]
    field_simp [hqx]
    ring
  · change (2 * r * qx) * (1 - qx ^ 2) / qx ^ 2 / 8 = y
    rw [hnum]
    field_simp [hqx, hr0]
    ring

/-- A square first coordinate on the isogenous curve has an explicit
preimage under the forward isogeny. -/
private theorem n15_exists_forward_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : N15AuxPoint,
      n15ForwardPoint P = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 + 62 * x ^ 2 + x :=
    (n15IsoCurve_equation_iff x y).mp h.1
  have hcurveR : y ^ 2 = r ^ 6 + 62 * r ^ 4 + r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := n15ForwardPreimageX r y
  let py := n15ForwardPreimageY r y
  have hprod :
      px * ((r ^ 2 + 31 + y / r) / 2) = 240 := by
    dsimp [px, n15ForwardPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 240 - px ^ 2 = px * y / r := by
    rw [← hprod]
    dsimp [px, n15ForwardPreimageX]
    field_simp [hr0]
    ring
  have hpeq : N15AuxiliaryEquation px py := by
    unfold N15AuxiliaryEquation
    dsimp [px, py, n15ForwardPreimageX, n15ForwardPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 - 31 * r + y) * hcurveR
  have hpns : WeierstrassCurve.Affine.Nonsingular n15AuxCurve px py :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15AuxCurve_equation_iff px py).mpr hpeq)
  let P : N15AuxPoint :=
    WeierstrassCurve.Affine.Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [n15ForwardPoint_some_of_x_ne_zero hpns hpx]
  change WeierstrassCurve.Affine.Point.some
      (n15ForwardX px py) (n15ForwardY px py) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = x
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (240 - px ^ 2) / px ^ 2 = y
    rw [hnum]
    field_simp [hpx, hr0]

@[simp] private theorem n15AuxCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY n15AuxCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, n15AuxCurve]

private def n15AuxTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 62 * x + 240) / (2 * y)

private def n15TangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

private def n15TangentY (a₂ x y m : ℚ) : ℚ :=
  -(m * (n15TangentX a₂ x m - x) + y)

private theorem n15_dual_forward_x {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : N15AuxiliaryEquation x y) :
    n15DualX (n15ForwardX x y) (n15ForwardY x y) =
      n15TangentX (-31) x (n15AuxTangent x y) := by
  unfold n15DualX n15ForwardX n15ForwardY n15TangentX n15AuxTangent
  unfold N15AuxiliaryEquation at h
  field_simp [hx, hy]
  rw [h]
  ring

private theorem n15_dual_forward_y {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : N15AuxiliaryEquation x y) :
    n15DualY (n15ForwardX x y) (n15ForwardY x y) =
      n15TangentY (-31) x y (n15AuxTangent x y) := by
  unfold n15DualY n15ForwardX n15ForwardY n15TangentY
    n15TangentX n15AuxTangent
  unfold N15AuxiliaryEquation at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x - 15) * (x - 16)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x * (x - 15) * (x - 16)) ^ 2 := by rw [h]
  rw [hy4, h]
  ring

private theorem n15AuxCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope n15AuxCurve x x y y =
      n15AuxTangent x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY n15AuxCurve x y := by
    intro h
    apply hy
    rw [n15AuxCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [n15AuxCurve, n15AuxTangent,
    WeierstrassCurve.Affine.negY]
  ring

private theorem n15AuxCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX n15AuxCurve x x
      (n15AuxTangent x y) =
        n15TangentX (-31) x (n15AuxTangent x y) := by
  simp [n15AuxCurve, n15TangentX]
  ring

private theorem n15AuxCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY n15AuxCurve x x y
      (n15AuxTangent x y) =
        n15TangentY (-31) x y (n15AuxTangent x y) := by
  unfold WeierstrassCurve.Affine.addY
    WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.addX
    n15TangentY n15TangentX n15AuxCurve
  ring

private theorem n15Aux_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x = 0) : y = 0 := by
  have heq := (n15AuxCurve_equation_iff x y).mp h.1
  unfold N15AuxiliaryEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem n15Aux_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : N15AuxPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, n15AuxCurve])

private theorem n15Aux_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY n15AuxCurve x y := by
  intro h
  apply hy
  rw [n15AuxCurve_negY] at h
  linarith

/-- The dual isogeny after the forward isogeny is doubling, including all
exceptional affine branches. -/
private theorem n15_dual_comp_forwardPoint (P : N15AuxPoint) :
    n15DualPoint (n15ForwardPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := n15Aux_y_zero_of_x_zero h hx
        rw [n15ForwardPoint_some_of_x_eq_zero h hx]
        simp only [n15DualPoint_zero]
        exact (n15Aux_double_eq_zero_of_y_zero h hy).symm
      · rw [n15ForwardPoint_some_of_x_ne_zero h hx]
        by_cases hy : y = 0
        · have hfx : n15ForwardX x y = 0 := by
            simp [n15ForwardX, hy]
          change n15DualPoint
              (.some (n15ForwardX x y) (n15ForwardY x y) _) = _
          rw [n15DualPoint_some_of_x_eq_zero _ hfx]
          exact (n15Aux_double_eq_zero_of_y_zero h hy).symm
        · have hfx : n15ForwardX x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          change n15DualPoint
              (.some (n15ForwardX x y) (n15ForwardY x y) _) = _
          rw [n15DualPoint_some_of_x_ne_zero _ hfx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (n15Aux_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (n15DualX (n15ForwardX x y) (n15ForwardY x y))
              (n15DualY (n15ForwardX x y) (n15ForwardY x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX n15AuxCurve x x
                (WeierstrassCurve.Affine.slope n15AuxCurve x x y y))
              (WeierstrassCurve.Affine.addY n15AuxCurve x x y
                (WeierstrassCurve.Affine.slope n15AuxCurve x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : N15AuxiliaryEquation x y :=
            (n15AuxCurve_equation_iff x y).mp h.1
          constructor
          · rw [n15_dual_forward_x hx hy heq,
              n15AuxCurve_slope_self hy,
              n15AuxCurve_addX_tangent]
          · rw [n15_dual_forward_y hx hy heq,
              n15AuxCurve_slope_self hy,
              n15AuxCurve_addY_tangent]

/-! ### Denominator normalization and the two Kummer images -/

private theorem n15_nat_isSquare_of_isSquare_cube {n : ℕ}
    (hn : n ≠ 0) (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

private theorem n15_den_monic_cubic (a b : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D)) D :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

private theorem n15_rat_denom_square_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den =
        x.den ^ 3 := by
    exact_mod_cast n15_den_monic_cubic a b x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    n15_nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

private theorem n15_integral_model_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4) := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ :=
    n15_rat_denom_square_monic a b x y h
  have hBne : (B : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  rw [sq C]
  exact hC.symm

private theorem n15_aux_integral_model {x y : ℚ}
    (h : N15AuxiliaryEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A - 15 * B ^ 2) * (A - 16 * B ^ 2) := by
  have hcubic : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    unfold N15AuxiliaryEquation at h
    nlinarith
  have hcubic' : y ^ 2 =
      x ^ 3 + ((-31 : ℤ) : ℚ) * x ^ 2 + ((240 : ℤ) : ℚ) * x := by
    norm_num at ⊢
    simpa [sub_eq_add_neg] using hcubic
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    n15_integral_model_monic (-31) 240 x y hcubic'
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  calc
    C ^ 2 = A * (A ^ 2 - 31 * A * B ^ 2 + 240 * B ^ 4) := by
      simpa [sub_eq_add_neg] using hC
    _ = A * (A - 15 * B ^ 2) * (A - 16 * B ^ 2) := by ring

private theorem n15_iso_integral_model {x y : ℚ}
    (h : N15IsogenousEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + 62 * A * B ^ 2 + B ^ 4) := by
  have hcubic : y ^ 2 =
      x ^ 3 + ((62 : ℤ) : ℚ) * x ^ 2 + ((1 : ℤ) : ℚ) * x := by
    unfold N15IsogenousEquation at h
    norm_num at ⊢
    exact h
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    n15_integral_model_monic 62 1 x y hcubic
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  simpa using hC

private theorem n15_squarefree_core_dvd_other {a q c d r : ℕ}
    (ha0 : a ≠ 0) (hdecomp : r ^ 2 * d = a) (hd : Squarefree d)
    (hsq : c ^ 2 = a * q) : d ∣ q := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    simp at hdecomp
    exact ha0 hdecomp.symm
  have hr2dvd : r ^ 2 ∣ c ^ 2 := by
    refine ⟨d * q, ?_⟩
    rw [hsq, ← hdecomp]
    ring
  have hrdvd : r ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hr2dvd
  obtain ⟨k, rfl⟩ := hrdvd
  have hk : k ^ 2 = d * q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hr0)
    calc
      r ^ 2 * k ^ 2 = (r * k) ^ 2 := by ring
      _ = a * q := hsq
      _ = (r ^ 2 * d) * q := by rw [hdecomp]
      _ = r ^ 2 * (d * q) := by ring
  have hdk2 : d ∣ k ^ 2 := ⟨q, hk⟩
  have hdk : d ∣ k := (hd.dvd_pow_iff_dvd two_ne_zero).mp hdk2
  obtain ⟨l, rfl⟩ := hdk
  have hcancel : d * (d * l ^ 2) = d * q := by
    calc
      d * (d * l ^ 2) = (d * l) ^ 2 := by ring
      _ = d * q := hk
  have hq : d * l ^ 2 = q := mul_left_cancel₀ hd.ne_zero hcancel
  exact ⟨l ^ 2, hq.symm⟩

private theorem n15_coprime_of_dvd_left {a b d : ℤ}
    (hab : IsCoprime a b) (hd : d ∣ a) : IsCoprime d b := by
  rcases hab with ⟨u, v, huv⟩
  rcases hd with ⟨k, rfl⟩
  exact ⟨u * k, v, by rw [← huv]; ring⟩

private theorem n15_squarefree_core_dvd_cubic_coefficient
    {a b A B C : ℤ} {d r : ℕ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4))
    (hdecomp : r ^ 2 * d = A.natAbs) (hd : Squarefree d) :
    d ∣ b.natAbs := by
  let Q : ℤ := A ^ 2 + a * A * B ^ 2 + b * B ^ 4
  have hAabs0 : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA0
  have habs : C.natAbs ^ 2 = A.natAbs * Q.natAbs := by
    simpa [Q, Int.natAbs_pow, Int.natAbs_mul] using
      congrArg Int.natAbs hmodel
  have hdQ : d ∣ Q.natAbs :=
    n15_squarefree_core_dvd_other hAabs0 hdecomp hd habs
  have hdA : d ∣ A.natAbs := by
    exact hdecomp ▸ dvd_mul_left d (r ^ 2)
  have hdAZ : (d : ℤ) ∣ A := Int.natCast_dvd.mpr hdA
  have hdQZ : (d : ℤ) ∣ Q := Int.natCast_dvd.mpr hdQ
  have hdbB4 : (d : ℤ) ∣ b * B ^ 4 := by
    rw [show b * B ^ 4 = Q - A * (A + a * B ^ 2) by
      simp only [Q]
      ring]
    exact dvd_sub hdQZ (dvd_mul_of_dvd_left hdAZ _)
  have hAB : IsCoprime A B :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hdB4 : IsCoprime (d : ℤ) (B ^ 4) :=
    (n15_coprime_of_dvd_left hAB hdAZ).pow_right
  have hdbZ : (d : ℤ) ∣ b := hdB4.dvd_of_dvd_mul_right hdbB4
  exact Int.natCast_dvd.mp hdbZ

private theorem n15_first_coordinate_squareclass
    {a b A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ d r : ℕ, Squarefree d ∧ d ∣ b.natAbs ∧
      (A = (d : ℤ) * (r : ℤ) ^ 2 ∨
       A = -((d : ℤ) * (r : ℤ) ^ 2)) := by
  obtain ⟨d, r, hdecomp, hd⟩ := Nat.sq_mul_squarefree A.natAbs
  have hdb := n15_squarefree_core_dvd_cubic_coefficient
    hcop hA0 hmodel hdecomp hd
  have habs : (A.natAbs : ℤ) = (d : ℤ) * (r : ℤ) ^ 2 := by
    have hcast : (A.natAbs : ℤ) = ((r ^ 2 * d : ℕ) : ℤ) := by
      exact_mod_cast hdecomp.symm
    rw [hcast]
    push_cast
    ring
  refine ⟨d, r, hd, hdb, ?_⟩
  rcases Int.natAbs_eq A with hpos | hneg
  · left
    rw [hpos, habs]
  · right
    rw [hneg, habs]

private theorem n15_squarefree_dvd_240 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 240) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨
      d = 6 ∨ d = 10 ∨ d = 15 ∨ d = 30 := by
  have hd30 : d ∣ 30 := by
    have hdPow : d ∣ 30 ^ 4 := hdiv.trans (by norm_num)
    exact (hd.dvd_pow_iff_dvd (by norm_num : 4 ≠ 0)).mp hdPow
  have hdle : d ≤ 30 := Nat.le_of_dvd (by norm_num) hd30
  interval_cases d
  all_goals norm_num at hd30
  all_goals simp

private theorem n15_quartic_cover_of_squareclass
    {a b d e A B C r : ℤ} (hd : d ≠ 0) (hr : r ≠ 0)
    (hb : b = d * e) (hA : A = d * r ^ 2)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ z : ℤ,
      z ^ 2 = d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4 := by
  let Q : ℤ := d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4
  have hfactor : C ^ 2 = (d * r) ^ 2 * Q := by
    rw [hmodel, hA, hb]
    simp only [Q]
    ring
  have hfactor' : C ^ 2 = d ^ 2 * r ^ 2 * Q := by
    calc
      C ^ 2 = (d * r) ^ 2 * Q := hfactor
      _ = d ^ 2 * r ^ 2 * Q := by ring
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hrq : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrat : ((C : ℚ) / ((d : ℚ) * (r : ℚ))) ^ 2 = (Q : ℚ) := by
    field_simp [hdq, hrq]
    exact_mod_cast hfactor'
  have hsq : IsSquare (Q : ℚ) :=
    ⟨(C : ℚ) / ((d : ℚ) * (r : ℚ)), by
      rw [← sq]
      exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨z, hz⟩ := hsq
  refine ⟨z, ?_⟩
  rw [sq]
  exact hz.symm

private theorem n15_root_coprime_denominator {d r A B : ℤ}
    (hcop : Int.gcd A B = 1) (hA : A = d * r ^ 2) :
    Int.gcd r B = 1 := by
  have hAB : IsCoprime A B :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hrA : r ∣ A := by
    rw [hA]
    exact ⟨d * r, by ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (n15_coprime_of_dvd_left hAB hrA)

private theorem n15_primitive_mod_two {r B : ℤ}
    (hcop : Int.gcd r B = 1) :
    n15Reduce16to2 (r : ZMod 16) ≠ 0 ∨
      n15Reduce16to2 (B : ZMod 16) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [n15Reduce16to2, ZMod.castHom_apply] using hmod2

private theorem n15_no_primitive_kummer_two (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 120 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_two_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 6 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 40 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_six_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_ten (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 10 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 24 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_ten_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_thirty (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 30 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 8 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_thirty_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_dual_negative (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -(r ^ 4) + 62 * r ^ 2 * B ^ 2 - B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_dual_negative_class_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_aux_x_nonnegative {x y : ℚ}
    (h : N15AuxiliaryEquation x y) : 0 ≤ x := by
  by_contra hx
  have hxneg : x < 0 := lt_of_not_ge hx
  have hx15 : x - 15 < 0 := by linarith
  have hx16 : x - 16 < 0 := by linarith
  have hprod : x * (x - 15) * (x - 16) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hxneg hx15) hx16
  unfold N15AuxiliaryEquation at h
  nlinarith [sq_nonneg y]

private theorem n15_rat_squareclass_of_integral
    {x : ℚ} {A B d r : ℤ} (hB : B ≠ 0)
    (hx : x = (A : ℚ) / (B : ℚ) ^ 2)
    (hA : A = d * r ^ 2) :
    x = (d : ℚ) * ((r : ℚ) / (B : ℚ)) ^ 2 := by
  rw [hx, hA]
  push_cast
  field_simp [Int.cast_ne_zero.mpr hB]

private theorem n15_aux_rational_x_squareclasses {x y : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ,
      x = q ^ 2 ∨ x = 3 * q ^ 2 ∨ x = 5 * q ^ 2 ∨ x = 15 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    n15_aux_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hAz
    apply hx0
    rw [hx, hAz]
    norm_num
  have hmodel' : C ^ 2 =
      A * (A ^ 2 + (-31) * A * B ^ 2 + 240 * B ^ 4) := by
    rw [hmodel]
    ring
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    n15_first_coordinate_squareclass hcop hA0 hmodel'
  have hdiv240 : d ∣ 240 := by simpa using hdiv
  have hxpos : 0 < x :=
    lt_of_le_of_ne (n15_aux_x_nonnegative h) (Ne.symm hx0)
  have hApos : 0 < A := by
    have hBq0 : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB0
    have hmul : (A : ℚ) = x * (B : ℚ) ^ 2 := by
      rw [hx]
      field_simp [hBq0]
    have hAqpos : (0 : ℚ) < (A : ℚ) := by
      rw [hmul]
      exact mul_pos hxpos (sq_pos_of_ne_zero hBq0)
    exact_mod_cast hAqpos
  have hA : A = (d : ℤ) * (r : ℤ) ^ 2 := by
    rcases hsign with hpos | hneg
    · exact hpos
    · exfalso
      rw [hneg] at hApos
      have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
      nlinarith [sq_nonneg (r : ℤ)]
  have hr0 : (r : ℤ) ≠ 0 := by
    intro hr
    apply hA0
    rw [hA, hr]
    norm_num
  have hcopRB : Int.gcd (r : ℤ) B = 1 :=
    n15_root_coprime_denominator hcop hA
  rcases n15_squarefree_dvd_240 hd hdiv240 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (2 : ℤ)) (e := 120) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_two (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; right; left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (6 : ℤ)) (e := 40) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_six (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (10 : ℤ)) (e := 24) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_ten (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; right; right
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (30 : ℤ)) (e := 8) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_thirty (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim

private theorem n15_iso_rational_x_square {x y : ℚ}
    (h : N15IsogenousEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    n15_iso_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hAz
    apply hx0
    rw [hx, hAz]
    norm_num
  have hmodel' : C ^ 2 =
      A * (A ^ 2 + (62 : ℤ) * A * B ^ 2 + (1 : ℤ) * B ^ 4) := by
    simpa using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    n15_first_coordinate_squareclass hcop hA0 hmodel'
  have hd1 : d = 1 := by
    have : d ∣ 1 := by simpa using hdiv
    exact Nat.dvd_one.mp this
  subst d
  rcases hsign with hA | hA
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    have hcopRB : Int.gcd (r : ℤ) B = 1 := by
      exact n15_root_coprime_denominator (d := (-1 : ℤ)) hcop
        (by simpa using hA)
    obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (-1 : ℤ)) (e := -1) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) (by simpa using hA) hmodel'
    exact (n15_no_primitive_dual_negative (r : ℤ) B z hcopRB
      (by calc
        z ^ 2 = -1 * (r : ℤ) ^ 4 + 62 * (r : ℤ) ^ 2 * B ^ 2 +
            -1 * B ^ 4 := hz
        _ = -((r : ℤ) ^ 4) + 62 * (r : ℤ) ^ 2 * B ^ 2 - B ^ 4 := by
          ring)).elim

private def n15AuxPointOf (x y : ℚ) (h : N15AuxiliaryEquation x y) :
    N15AuxPoint :=
  WeierstrassCurve.Affine.Point.some x y
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15AuxCurve_equation_iff x y).mpr h))

private def n15P00 : N15AuxPoint :=
  n15AuxPointOf 0 0 (by norm_num [N15AuxiliaryEquation])

private def n15P15 : N15AuxPoint :=
  n15AuxPointOf 15 0 (by norm_num [N15AuxiliaryEquation])

private def n15P16 : N15AuxPoint :=
  n15AuxPointOf 16 0 (by norm_num [N15AuxiliaryEquation])

private def n15P12 : N15AuxPoint :=
  n15AuxPointOf 12 12 (by norm_num [N15AuxiliaryEquation])

private def n15P20 : N15AuxPoint :=
  n15AuxPointOf 20 20 (by norm_num [N15AuxiliaryEquation])

private theorem n15_exists_half_of_square_x {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) (hsq : ∃ q : ℚ, x = q ^ 2) :
    ∃ Q : N15AuxPoint,
      2 • Q = WeierstrassCurve.Affine.Point.some x y h := by
  obtain ⟨q, hq⟩ := hsq
  obtain ⟨S, hS⟩ := n15_exists_dual_preimage_of_x_eq_sq h hx hq
  cases S with
  | zero =>
      change n15DualPoint (0 : N15IsoPoint) = _ at hS
      rw [n15DualPoint_zero] at hS
      cases hS
  | some t v ht =>
      by_cases ht0 : t = 0
      · rw [n15DualPoint_some_of_x_eq_zero ht ht0] at hS
        cases hS
      · have hteq : N15IsogenousEquation t v :=
          (n15IsoCurve_equation_iff t v).mp ht.1
        obtain ⟨r, hr⟩ := n15_iso_rational_x_square hteq ht0
        obtain ⟨Q, hQ⟩ :=
          n15_exists_forward_preimage_of_x_eq_sq ht ht0 hr
        refine ⟨Q, ?_⟩
        rw [← n15_dual_comp_forwardPoint Q, hQ, hS]

private theorem n15P00_two : 2 • n15P00 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P15_two : 2 • n15P15 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P16_two : 2 • n15P16 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P12_two : 2 • n15P12 = n15P16 := by
  change 2 • (WeierstrassCurve.Affine.Point.some 12 12 _ : N15AuxPoint) =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (n15Aux_y_ne_negY (by norm_num : (12 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX n15AuxCurve 12 12
        (WeierstrassCurve.Affine.slope n15AuxCurve 12 12 12 12))
      (WeierstrassCurve.Affine.addY n15AuxCurve 12 12 12
        (WeierstrassCurve.Affine.slope n15AuxCurve 12 12 12 12)) _ =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [n15P16, n15AuxPointOf, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    n15AuxCurve]

private theorem n15P20_two : 2 • n15P20 = n15P16 := by
  change 2 • (WeierstrassCurve.Affine.Point.some 20 20 _ : N15AuxPoint) =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (n15Aux_y_ne_negY (by norm_num : (20 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX n15AuxCurve 20 20
        (WeierstrassCurve.Affine.slope n15AuxCurve 20 20 20 20))
      (WeierstrassCurve.Affine.addY n15AuxCurve 20 20 20
        (WeierstrassCurve.Affine.slope n15AuxCurve 20 20 20 20)) _ =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [n15P16, n15AuxPointOf, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    n15AuxCurve]

private theorem n15P12_four : 4 • n15P12 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P12_two, n15P16_two]

private theorem n15P20_four : 4 • n15P20 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P20_two, n15P16_two]

private theorem n15_secant_x_square
    {x y t s q d r : ℚ}
    (hxy : N15AuxiliaryEquation x y)
    (hts : N15AuxiliaryEquation t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    WeierstrassCurve.Affine.addX n15AuxCurve x t
        (WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)) =
      ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxt]
  unfold WeierstrassCurve.Affine.addX
  simp only [n15AuxCurve, zero_mul, sub_neg_eq_add]
  unfold N15AuxiliaryEquation at hxy hts
  have hxy' : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    rw [hxy]
    ring
  have hts' : s ^ 2 = t ^ 3 - 31 * t ^ 2 + 240 * t := by
    rw [hts]
    ring
  field_simp [sub_ne_zero.mpr hxt, hd, hq, hr]
  have hxdt : d ^ 2 * q ^ 2 * r ^ 2 = x * t := by
    rw [hx, ht]
    ring
  calc
    ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * d ^ 2 * q ^ 2 * r ^ 2 =
        ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) *
          (d ^ 2 * q ^ 2 * r ^ 2) := by ring
    _ = ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * (x * t) := by
      rw [hxdt]
    _ = (y * t + s * x) ^ 2 := by
      ring_nf
      rw [hxy', hts']
      ring

private theorem n15_exists_half_after_same_squareclass_secant
    {x y t s q d r : ℚ}
    (hxy : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hts : WeierstrassCurve.Affine.Nonsingular n15AuxCurve t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hz0 : WeierstrassCurve.Affine.addX n15AuxCurve x t
      (WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)) ≠ 0) :
    ∃ Q : N15AuxPoint,
      2 • Q = WeierstrassCurve.Affine.Point.some x y hxy -
        WeierstrassCurve.Affine.Point.some t s hts := by
  have hcurve : N15AuxiliaryEquation x y :=
    (n15AuxCurve_equation_iff x y).mp hxy.1
  have htcurve : N15AuxiliaryEquation t s :=
    (n15AuxCurve_equation_iff t s).mp hts.1
  have hneg : WeierstrassCurve.Affine.Nonsingular n15AuxCurve t (-s) := by
    have hn := (WeierstrassCurve.Affine.nonsingular_neg t s).mpr hts
    simpa [n15AuxCurve, WeierstrassCurve.Affine.negY] using hn
  let m := WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)
  let z := WeierstrassCurve.Affine.addX n15AuxCurve x t m
  let w := WeierstrassCurve.Affine.addY n15AuxCurve x t y m
  have hR : WeierstrassCurve.Affine.Nonsingular n15AuxCurve z w :=
    WeierstrassCurve.Affine.nonsingular_add hxy hneg
      (fun hbad => hxt hbad.1)
  have hzsq : z = ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
    exact n15_secant_x_square hcurve htcurve hx ht hxt hd hq hr
  obtain ⟨Q, hQ⟩ := n15_exists_half_of_square_x hR
    (by simpa [z, m] using hz0)
    ⟨(y * t + s * x) / ((x - t) * d * q * r), hzsq⟩
  refine ⟨Q, ?_⟩
  calc
    2 • Q = WeierstrassCurve.Affine.Point.some z w hR := hQ
    _ = WeierstrassCurve.Affine.Point.some x y hxy +
        WeierstrassCurve.Affine.Point.some t (-s) hneg := by
      symm
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxt
    _ = WeierstrassCurve.Affine.Point.some x y hxy -
        WeierstrassCurve.Affine.Point.some t s hts := by
      rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some]
      congr 1
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      simp [n15AuxCurve, WeierstrassCurve.Affine.negY]

private theorem n15_x_eq_twelve_or_twenty_of_y_eq_neg_x
    {x y : ℚ} (h : N15AuxiliaryEquation x y)
    (hx0 : x ≠ 0) (hy : y = -x) : x = 12 ∨ x = 20 := by
  unfold N15AuxiliaryEquation at h
  have hcancel : x = (x - 15) * (x - 16) := by
    apply mul_left_cancel₀ hx0
    calc
      x * x = y ^ 2 := by rw [hy]; ring
      _ = x * (x - 15) * (x - 16) := h
      _ = x * ((x - 15) * (x - 16)) := by ring
  have hfactor : (x - 12) * (x - 20) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h12 | h20
  · left; linarith
  · right; linarith

private theorem n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero
    {x y : ℚ} (h : N15AuxiliaryEquation x y) (hy : y = 0) :
    x = 0 ∨ x = 15 ∨ x = 16 := by
  unfold N15AuxiliaryEquation at h
  rw [hy] at h
  norm_num at h
  rcases h with (hx | h15) | h16
  · exact Or.inl hx
  · right; left; linarith
  · right; right; linarith

private theorem n15_rat_sq_ne_twenty_thirds (q : ℚ) :
    q ^ 2 ≠ 20 / 3 := by
  intro h
  have hs : IsSquare (20 / 3 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_rat_sq_ne_twelve_fifths (q : ℚ) :
    q ^ 2 ≠ 12 / 5 := by
  intro h
  have hs : IsSquare (12 / 5 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_rat_sq_ne_sixteen_fifteenths (q : ℚ) :
    q ^ 2 ≠ 16 / 15 := by
  intro h
  have hs : IsSquare (16 / 15 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_translate_12_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 3 * q ^ 2) (hx12 : x ≠ 12) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 12
      (WeierstrassCurve.Affine.slope n15AuxCurve x 12 y (-12)) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 12 + 12 * x ≠ 0 := by
    intro hnum
    have hy : y = -x := by linarith
    rcases n15_x_eq_twelve_or_twenty_of_y_eq_neg_x h hx0 hy with
      h12 | h20
    · exact hx12 h12
    · apply n15_rat_sq_ne_twenty_thirds q
      rw [h20] at hx
      nlinarith
  have hroot :
      (y * 12 + 12 * x) / ((x - 12) * 3 * q * 2) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx12) (by norm_num)) hq0)
      (by norm_num))
  rw [n15_secant_x_square (q := q) (d := 3) (r := 2) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx12 (by norm_num) hq0 (by norm_num)]
  exact pow_ne_zero 2 hroot

private theorem n15_translate_20_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 5 * q ^ 2) (hx20 : x ≠ 20) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 20
      (WeierstrassCurve.Affine.slope n15AuxCurve x 20 y (-20)) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 20 + 20 * x ≠ 0 := by
    intro hnum
    have hy : y = -x := by linarith
    rcases n15_x_eq_twelve_or_twenty_of_y_eq_neg_x h hx0 hy with
      h12 | h20
    · apply n15_rat_sq_ne_twelve_fifths q
      rw [h12] at hx
      nlinarith
    · exact hx20 h20
  have hroot :
      (y * 20 + 20 * x) / ((x - 20) * 5 * q * 2) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx20) (by norm_num)) hq0)
      (by norm_num))
  rw [n15_secant_x_square (q := q) (d := 5) (r := 2) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx20 (by norm_num) hq0 (by norm_num)]
  exact pow_ne_zero 2 hroot

private theorem n15_translate_15_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 15 * q ^ 2) (hx15 : x ≠ 15) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 15
      (WeierstrassCurve.Affine.slope n15AuxCurve x 15 y 0) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 15 + 0 * x ≠ 0 := by
    intro hnum
    have hy : y = 0 := by linarith
    rcases n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero h hy with
      hzero | h15 | h16
    · exact hx0 hzero
    · exact hx15 h15
    · apply n15_rat_sq_ne_sixteen_fifteenths q
      rw [h16] at hx
      nlinarith
  have hroot :
      (y * 15 + 0 * x) / ((x - 15) * 15 * q * 1) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx15) (by norm_num)) hq0)
      (by norm_num))
  have hz := n15_secant_x_square (t := 15) (s := 0)
    (q := q) (d := 15) (r := 1) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx15 (by norm_num) hq0 (by norm_num)
  rw [show WeierstrassCurve.Affine.addX n15AuxCurve x 15
      (WeierstrassCurve.Affine.slope n15AuxCurve x 15 y 0) =
        ((y * 15 + 0 * x) / ((x - 15) * 15 * q * 1)) ^ 2 by
    simpa only [neg_zero] using hz]
  exact pow_ne_zero 2 hroot

private theorem n15P00_four : 4 • n15P00 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P00_two]
  simp

private theorem n15P15_four : 4 • n15P15 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P15_two]
  simp

private def N15DescentRepresentative (T : N15AuxPoint) : Prop :=
  T = 0 ∨ T = n15P00 ∨ T = n15P12 ∨ T = -n15P12 ∨
    T = n15P20 ∨ T = -n15P20 ∨ T = n15P15

private theorem n15_descent_decomposition (P : N15AuxPoint) :
    ∃ T Q : N15AuxPoint, N15DescentRepresentative T ∧
      4 • T = 0 ∧ P = T + 2 • Q := by
  cases P with
  | zero =>
      refine ⟨0, 0, by simp [N15DescentRepresentative], by simp, ?_⟩
      rfl
  | some x y hxy =>
      have hcurve : N15AuxiliaryEquation x y :=
        (n15AuxCurve_equation_iff x y).mp hxy.1
      by_cases hx0 : x = 0
      · have hy0 : y = 0 := n15Aux_y_zero_of_x_zero hxy hx0
        have hP :
            (WeierstrassCurve.Affine.Point.some x y hxy : N15AuxPoint) =
              n15P00 := by
          change WeierstrassCurve.Affine.Point.some x y hxy =
            WeierstrassCurve.Affine.Point.some 0 0 _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx0, hy0⟩
        refine ⟨n15P00, 0, by simp [N15DescentRepresentative],
          n15P00_four, ?_⟩
        rw [hP]
        simp
      · rcases n15_aux_rational_x_squareclasses hcurve hx0 with
          ⟨q, hsq | hsq | hsq | hsq⟩
        · obtain ⟨Q, hQ⟩ := n15_exists_half_of_square_x hxy hx0 ⟨q, hsq⟩
          refine ⟨0, Q, by simp [N15DescentRepresentative], by simp, ?_⟩
          simpa using hQ.symm
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx12 : x = 12
          · have hycases : y = 12 ∨ y = -12 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx12] at hcurve
              norm_num at hcurve
              have hf : (y - 12) * (y + 12) = 0 := by nlinarith
              rcases mul_eq_zero.mp hf with hp | hn
              · left; linarith
              · right; linarith
            have hrep_four :
                N15DescentRepresentative
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) ∧
                  4 • (WeierstrassCurve.Affine.Point.some x y hxy :
                    N15AuxPoint) = 0 := by
              rcases hycases with hy | hy
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = n15P12 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    WeierstrassCurve.Affine.Point.some 12 12 _
                  rw [WeierstrassCurve.Affine.Point.some.injEq]
                  exact ⟨hx12, hy⟩
                rw [hP]
                exact ⟨by simp [N15DescentRepresentative], n15P12_four⟩
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = -n15P12 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    -(WeierstrassCurve.Affine.Point.some 12 12 _ :
                      N15AuxPoint)
                  rw [WeierstrassCurve.Affine.Point.neg_some,
                    WeierstrassCurve.Affine.Point.some.injEq]
                  simp [n15P12, n15AuxPointOf, n15AuxCurve,
                    WeierstrassCurve.Affine.negY, hx12, hy]
                rw [hP]
                refine ⟨by simp [N15DescentRepresentative], ?_⟩
                simpa using congrArg Neg.neg n15P12_four
            exact ⟨_, 0, hrep_four.1, hrep_four.2, by simp⟩
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 12 12 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 12 12).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 3) (r := 2) hxy ht hsq (by norm_num)
                hx12 (by norm_num) hq0 (by norm_num)
                (n15_translate_12_x_ne_zero hcurve hx0 hsq hx12)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 12 12 ht
            have hT : T = n15P12 := by
              change WeierstrassCurve.Affine.Point.some 12 12 ht =
                WeierstrassCurve.Affine.Point.some 12 12 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P12_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx20 : x = 20
          · have hycases : y = 20 ∨ y = -20 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx20] at hcurve
              norm_num at hcurve
              have hf : (y - 20) * (y + 20) = 0 := by nlinarith
              rcases mul_eq_zero.mp hf with hp | hn
              · left; linarith
              · right; linarith
            have hrep_four :
                N15DescentRepresentative
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) ∧
                  4 • (WeierstrassCurve.Affine.Point.some x y hxy :
                    N15AuxPoint) = 0 := by
              rcases hycases with hy | hy
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = n15P20 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    WeierstrassCurve.Affine.Point.some 20 20 _
                  rw [WeierstrassCurve.Affine.Point.some.injEq]
                  exact ⟨hx20, hy⟩
                rw [hP]
                exact ⟨by simp [N15DescentRepresentative], n15P20_four⟩
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = -n15P20 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    -(WeierstrassCurve.Affine.Point.some 20 20 _ :
                      N15AuxPoint)
                  rw [WeierstrassCurve.Affine.Point.neg_some,
                    WeierstrassCurve.Affine.Point.some.injEq]
                  simp [n15P20, n15AuxPointOf, n15AuxCurve,
                    WeierstrassCurve.Affine.negY, hx20, hy]
                rw [hP]
                refine ⟨by simp [N15DescentRepresentative], ?_⟩
                simpa using congrArg Neg.neg n15P20_four
            exact ⟨_, 0, hrep_four.1, hrep_four.2, by simp⟩
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 20 20 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 20 20).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 5) (r := 2) hxy ht hsq (by norm_num)
                hx20 (by norm_num) hq0 (by norm_num)
                (n15_translate_20_x_ne_zero hcurve hx0 hsq hx20)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 20 20 ht
            have hT : T = n15P20 := by
              change WeierstrassCurve.Affine.Point.some 20 20 ht =
                WeierstrassCurve.Affine.Point.some 20 20 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P20_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx15 : x = 15
          · have hy0 : y = 0 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx15] at hcurve
              norm_num at hcurve
              nlinarith
            have hP :
                (WeierstrassCurve.Affine.Point.some x y hxy :
                  N15AuxPoint) = n15P15 := by
              change WeierstrassCurve.Affine.Point.some x y hxy =
                WeierstrassCurve.Affine.Point.some 15 0 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨hx15, hy0⟩
            refine ⟨n15P15, 0, by simp [N15DescentRepresentative],
              n15P15_four, ?_⟩
            rw [hP]
            simp
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 15 0 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 15 0).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 15) (r := 1) hxy ht hsq (by norm_num)
                hx15 (by norm_num) hq0 (by norm_num)
                (by simpa only [neg_zero] using
                  n15_translate_15_x_ne_zero hcurve hx0 hsq hx15)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 15 0 ht
            have hT : T = n15P15 := by
              change WeierstrassCurve.Affine.Point.some 15 0 ht =
                WeierstrassCurve.Affine.Point.some 15 0 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P15_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel

/-! ## Weak-descent iteration and the good model at two -/

/-- Iterating the Kummer four-coset statement makes `4P` divisible by every
power of two. -/
theorem n15Aux_four_nsmul_two_power_divisible
    (P : N15AuxPoint) (n : ℕ) :
    ∃ Q : N15AuxPoint, 4 • P = (2 ^ n : ℕ) • (4 • Q) := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨T, R, _hrep, hT, hdecomp⟩ := n15_descent_decomposition Q
      refine ⟨R, ?_⟩
      rw [hQ, hdecomp, nsmul_add, hT, zero_add]
      simp only [← mul_nsmul]
      congr 1
      omega

/-- Integral good-reduction model of the N15 auxiliary curve at `2`. -/
def E15Curve : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -5
  a₆ := 2

def OnE15 (x y : ℚ) : Prop :=
  y ^ 2 + x * y + y = x ^ 3 + x ^ 2 - 5 * x + 2

theorem E15Curve_delta : E15Curve.Δ = (225 : ℚ) := by
  norm_num [E15Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E15Curve_isElliptic : E15Curve.IsElliptic where
  isUnit := by rw [E15Curve_delta]; norm_num

@[simp] theorem E15Curve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E15Curve x y ↔ OnE15 x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E15Curve, OnE15, sub_eq_add_neg]

abbrev E15Point := WeierstrassCurve.Affine.Point E15Curve

def E15toAuxChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := -3
  s := -1 / 2
  t := 1

theorem E15toAuxChange_curve :
    E15toAuxChange • E15Curve = n15AuxCurve := by
  ext <;>
    simp [E15toAuxChange, E15Curve, n15AuxCurve,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;>
    norm_num

private noncomputable def curveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

noncomputable def E15AuxAddEquiv : E15Point ≃+ N15AuxPoint :=
  (variableChangePointAddEquiv E15Curve E15toAuxChange).trans
    (curveEqAddEquiv E15toAuxChange_curve)

/-! ## Two-adic separatedness on the good model -/

private theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 2 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.ofNat_zero_le _

private theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by linarith
    have : padicValRat 2 b = padicValRat 2 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

private theorem val_const_mul_ge {a : ℚ} (z : ℤ) (hz : z ≠ 0) (ha : a ≠ 0) :
    padicValRat 2 a ≤ padicValRat 2 ((z : ℚ) * a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hz) ha]
  have hzval := val_int_nonneg z
  omega

private theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    l.sum = 0 ∨ padicValRat 2 q < padicValRat 2 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 2 q < padicValRat 2 a := hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 2 q < padicValRat 2 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

private theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    padicValRat 2 (q + l.sum) = padicValRat 2 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 2 q) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

private theorem zmod2_nonzero_eq_one (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

private theorem rat_unit_sub_one_pos {q : ℚ} (hq : q ≠ 0)
    (hv : padicValRat 2 q = 0) :
    q - 1 = 0 ∨ 0 < padicValRat 2 (q - 1) := by
  by_cases hq1 : q - 1 = 0
  · exact Or.inl hq1
  right
  have hqnonneg : 0 ≤ padicValRat 2 q := by omega
  let z : ℤ_[2] := ratPadicInt q hqnonneg
  have hzcoe : (z : ℚ_[2]) = (q : ℚ_[2]) := rfl
  have hzred0 : PadicInt.toZMod z ≠ 0 := by
    intro hz0
    have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod]
      exact hz0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
      ← PadicInt.norm_lt_one_iff_dvd] at hm
    have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
    have hnorm : ‖(q : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hqcast,
        Padic.valuation_ratCast, hv]
      norm_num
    change ‖(z : ℚ_[2])‖ < 1 at hm
    rw [hzcoe, hnorm] at hm
    exact (lt_irrefl 1 hm)
  have hzred : PadicInt.toZMod z = 1 := zmod2_nonzero_eq_one _ hzred0
  have hdiffnonneg : 0 ≤ padicValRat 2 (q - 1) := by
    have hmin := padicValRat.min_le_padicValRat_add (p := 2)
      (q := q) (r := -1) (by simpa [sub_eq_add_neg] using hq1)
    rw [padicValRat.neg, hv, padicValRat.one, min_self] at hmin
    simpa [sub_eq_add_neg] using hmin
  let d : ℤ_[2] := ratPadicInt (q - 1) hdiffnonneg
  have hdcoe : (d : ℚ_[2]) = ((q - 1 : ℚ) : ℚ_[2]) := rfl
  have hdred : PadicInt.toZMod d = 0 := by
    change PadicInt.toZMod (ratPadicInt (q - 1) hdiffnonneg) = 0
    have hsub : ratPadicInt (q - 1) hdiffnonneg = z - 1 := by
      apply Subtype.ext
      change (((q - 1 : ℚ) : ℚ_[2])) = (z : ℚ_[2]) - 1
      rw [hzcoe]
      norm_cast
    rw [hsub, map_sub, map_one, hzred, sub_self]
  have hm : d ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hdred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  have hdiffcast : (((q - 1 : ℚ) : ℚ_[2])) ≠ 0 := by exact_mod_cast hq1
  change ‖(d : ℚ_[2])‖ < 1 at hm
  rw [hdcoe, Padic.norm_eq_zpow_neg_valuation hdiffcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)] at hm
  have hexp : -padicValRat 2 (q - 1) < (0 : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2)).mp (by simpa using hm)
  omega

def E15DoubleDen (x y : ℚ) : ℚ := 2 * y + x + 1

def E15DoubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + 9 * x ^ 2 - 18 * x + 9

def E15DoubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 + 2 * x ^ 5 - 25 * x ^ 4 + 36 * x ^ 3 - 34 * x ^ 2 +
    27 * x + y * (-x ^ 4 - 4 * x ^ 3 - 14 * x ^ 2 + 36 * x - 18) - 9
private theorem E15_doubleX_formula {x y : ℚ}
    (hd : E15DoubleDen x y ≠ 0) (hE : OnE15 x y) :
    WeierstrassCurve.Affine.addX E15Curve x x
        (WeierstrassCurve.Affine.slope E15Curve x x y y) =
      E15DoubleXNum x / E15DoubleDen x y ^ 2 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E15Curve x y := by
    intro h
    apply hd
    simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E15Curve x x y y =
      (3 * x ^ 2 + 2 * x - 5 - y) / E15DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E15Curve, E15DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addX E15DoubleXNum
  simp only [E15Curve]
  unfold OnE15 at hE
  field_simp [hd]
  unfold E15DoubleDen
  linear_combination
    (-8 * x - 5) * hE

private theorem E15_doubleY_formula {x y : ℚ}
    (hd : E15DoubleDen x y ≠ 0) (hE : OnE15 x y) :
    WeierstrassCurve.Affine.addY E15Curve x x y
        (WeierstrassCurve.Affine.slope E15Curve x x y y) =
      E15DoubleYNum x y / E15DoubleDen x y ^ 3 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E15Curve x y := by
    intro h
    apply hd
    simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at h ⊢
    linarith
  have hslope : WeierstrassCurve.Affine.slope E15Curve x x y y =
      (3 * x ^ 2 + 2 * x - 5 - y) / E15DoubleDen x y := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp [E15Curve, E15DoubleDen, WeierstrassCurve.Affine.negY]
    ring
  rw [hslope]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E15DoubleYNum
  simp [E15Curve]
  unfold OnE15 at hE
  field_simp [hd]
  unfold E15DoubleDen
  linear_combination
    (28 * x ^ 3 + 37 * x ^ 2 - 5 * x - 8 * y ^ 2 - 7 * y - 42) * hE

private theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 2 x + (b : ℤ) * padicValRat 2 y ≤
      padicValRat 2 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow hx, padicValRat.pow hy]
  have hcval := val_int_nonneg c
  omega

private theorem E15DoubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (E15DoubleXNum x) = -8 * k := by
  have hshape : E15DoubleXNum x =
      x ^ 4 + [9 * x ^ 2, -18 * x, (9 : ℚ)].sum := by
    simp [E15DoubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hge := val_monomial_ge hx hy 9 (by norm_num) 2 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-18) (by norm_num) 1 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg 9
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
private theorem E15DoubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (E15DoubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [2 * x ^ 5, -25 * x ^ 4, 36 * x ^ 3, -34 * x ^ 2,
      27 * x, (-1 : ℚ) * x ^ 4 * y, -4 * x ^ 3 * y,
      -14 * x ^ 2 * y, 36 * x * y, -18 * y, (-9 : ℚ)]
  have hshape : E15DoubleYNum x y = x ^ 6 + l.sum := by
    simp [E15DoubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow hx, hvx]
    · have hge := val_monomial_ge hx hy (2) (by norm_num) 5 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-25) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (36) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-34) (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (27) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-4) (by norm_num) 3 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-14) (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (36) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-18) (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-9)
      norm_num at hge ⊢
      omega
/-- A point is in the formal kernel at `2` when its affine coordinates have
the standard valuations `(-2k,-3k)` for some `k>0`. -/
def E15FormalAtTwo : E15Point → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

def E15FormalLevel : E15Point → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

theorem E15FormalAtTwo_iff (P : E15Point) :
    E15FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, E15FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [E15FormalAtTwo, E15FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

/-- On the formal kernel, doubling raises the local-parameter valuation by
at least one.  This is the curve-specific form of
`v₂([2]z) ≥ v₂(z)+1`. -/
theorem E15FormalLevel_double {P : E15Point} {k : ℤ}
    (hP : E15FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ E15FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [E15FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      by_cases hd : E15DoubleDen x y = 0
      · left
        rw [two_nsmul]
        apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
        simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvfirst :
            1 - 3 * k ≤ padicValRat 2 (2 * y + x) := by
          by_cases hfirst : 2 * y + x = 0
          · rw [hfirst, padicValRat.zero]
            omega
          · have hmin := padicValRat.min_le_padicValRat_add (p := 2)
              (q := 2 * y) (r := x) hfirst
            rw [hv2y, hvx, min_eq_left (by omega)] at hmin
            exact hmin
        have hvdenLower :
            1 - 3 * k ≤ padicValRat 2 (E15DoubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y + x) (r := 1)
            (by simpa [E15DoubleDen] using hd)
          rw [padicValRat.one] at hmin
          have hlower : 1 - 3 * k ≤
              min (padicValRat 2 (2 * y + x)) 0 :=
            le_min hvfirst (by omega)
          exact hlower.trans (by simpa [E15DoubleDen] using hmin)
        let k' : ℤ := 4 * k + padicValRat 2 (E15DoubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := E15DoubleXNum_val hx hy hk hvx
        have hvY := E15DoubleYNum_val hx hy hk hvx hvy
        have hN : E15DoubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : E15DoubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE : OnE15 x y := (E15Curve_equation_iff x y).mp h.1
        have hxform := E15_doubleX_formula hd hE
        have hyform := E15_doubleY_formula hd hE
        have hvx2 : padicValRat 2
              (WeierstrassCurve.Affine.addX E15Curve x x
                (WeierstrassCurve.Affine.slope E15Curve x x y y)) =
            -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow hd]
          dsimp [k']
          ring
        have hvy2 : padicValRat 2
              (WeierstrassCurve.Affine.addY E15Curve x x y
                (WeierstrassCurve.Affine.slope E15Curve x x y y)) =
            -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ WeierstrassCurve.Affine.negY E15Curve x y := by
          intro heq
          apply hd
          simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at heq ⊢
          linarith
        rw [two_nsmul,
          WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- Good reduction at two gives the usual dichotomy: an affine rational point
has integral coordinates, or lies in the formal kernel. -/
theorem E15_formal_or_integral (P : E15Point) :
    E15FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE : OnE15 x y := (E15Curve_equation_iff x y).mp h.1
      let vx := padicValRat 2 x
      let vy := padicValRat 2 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [x * y, (1 : ℚ) * y, -(x ^ 3), -(x ^ 2), 5 * x, (-2 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnE15 at hE
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · rw [hx0, zero_mul, padicValRat.zero, hlead]
              omega
            · rw [padicValRat.mul hx0 hy, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · rw [one_mul, hlead]
            dsimp [vy] at hvyneg ⊢
            omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 3 ≠ 0), neg_zero,
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, mul_zero, padicValRat.zero, hlead]
              omega
            · have hge := val_const_mul_ge 5 (by norm_num) hx0
              rw [hlead]
              dsimp [vx] at hxint hge ⊢
              omega
          · have hge := val_int_nonneg (-2)
            rw [hlead]
            norm_num at hge ⊢
            omega
        have hval := val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, x * y, (1 : ℚ) * y, -(x ^ 2), 5 * x, (-2 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnE15 at hE
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · rw [hy0, zero_pow (by norm_num : 2 ≠ 0),
                  padicValRat.zero, hlead]
                omega
              · rw [padicValRat.pow hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · by_cases hy0 : y = 0
              · rw [hy0, mul_zero, padicValRat.zero, hlead]
                omega
              · rw [padicValRat.mul hx hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · rw [one_mul, hlead]
              dsimp [vx, vy] at hvxneg hvxley ⊢
              omega
            · rw [hlead, padicValRat.neg, padicValRat.pow hx]
              dsimp [vx] at hvxneg ⊢
              omega
            · have hge := val_const_mul_ge 5 (by norm_num) hx
              rw [hlead]
              dsimp [vx] at hvxneg hge ⊢
              omega
            · have hge := val_int_nonneg (-2)
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval :=
            val_add_list_eq l (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let lleft : List ℚ := [x * y, (1 : ℚ) * y]
        have hleftshape :
            y ^ 2 + lleft.sum = y ^ 2 + x * y + y := by
          simp [lleft]
          ring
        have hleftgt : ∀ a ∈ lleft,
            padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [lleft, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [padicValRat.pow hy, padicValRat.mul hx hy]
            dsimp [vx, vy] at hvylt ⊢
            omega
          · rw [one_mul, padicValRat.pow hy]
            dsimp [vy] at hvylt ⊢
            omega
        have hvleft0 :=
          val_add_list_eq lleft (pow_ne_zero 2 hy) hleftgt
        have hvleft :
            padicValRat 2 (y ^ 2 + x * y + y) = 2 * vy := by
          rw [← hleftshape, hvleft0, padicValRat.pow hy]
          rfl
        let lright : List ℚ := [x ^ 2, -5 * x, (2 : ℚ)]
        have hrightshape :
            x ^ 3 + lright.sum = x ^ 3 + x ^ 2 - 5 * x + 2 := by
          simp [lright]
          ring
        have hrightgt : ∀ a ∈ lright,
            padicValRat 2 (x ^ 3) < padicValRat 2 a := by
          intro a ha
          simp only [lright, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · rw [padicValRat.pow hx]
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · have hge := val_const_mul_ge (-5) (by norm_num) hx
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · have hge := val_int_nonneg 2
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
        have hvright0 :=
          val_add_list_eq lright (pow_ne_zero 3 hx) hrightgt
        have hvright :
            padicValRat 2 (x ^ 3 + x ^ 2 - 5 * x + 2) = 3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y + y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 + x ^ 2 - 5 * x + 2) := by rw [hE]
            _ = 3 * vx := hvright
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

private theorem ratPadicInt_red_eq_one_of_val_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    PadicInt.toZMod (ratPadicInt q (by omega)) = 1 := by
  apply zmod2_nonzero_eq_one
  intro hz0
  have hm : ratPadicInt q (by omega) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hz0
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖((ratPadicInt q (by omega) : ℤ_[2]) : ℚ_[2])‖ < 1 at hm
  change ‖(q : ℚ_[2])‖ < 1 at hm
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv] at hm
  norm_num at hm

private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 2 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[2])‖ < 1
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
    (by norm_num : (1 : ℝ) < 2)).2 (by omega)

private theorem val_pos_of_rational_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 2 q := by
  by_contra hnot
  have hv0 : padicValRat 2 q = 0 := by omega
  have hone := ratPadicInt_red_eq_one_of_val_zero hq hv0
  have heq : ratPadicInt q hqi = ratPadicInt q (by omega) := by
    apply Subtype.ext
    rfl
  rw [heq, hone] at hred
  norm_num at hred

private theorem val_zero_of_rational_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 2 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 2 q := lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi = ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-! ### Integral points and the exponent-four reduction entry -/

private noncomputable def E15DoubleDenPadic (x y : ℤ_[2]) : ℤ_[2] :=
  2 * y + x + 1

private noncomputable def E15DoubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + 9 * x ^ 2 - 18 * x + 9

private noncomputable def E15DoubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 + 2 * x ^ 5 - 25 * x ^ 4 + 36 * x ^ 3 - 34 * x ^ 2 +
    27 * x + y * (-x ^ 4 - 4 * x ^ 3 - 14 * x ^ 2 + 36 * x - 18) - 9

private theorem E15DoubleDenPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((E15DoubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((E15DoubleDen x y : ℚ) : ℚ_[2]) := by
  change 2 * (y : ℚ_[2]) + (x : ℚ_[2]) + 1 =
    (((2 * y + x + 1 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E15DoubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((E15DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((E15DoubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + 9 * (x : ℚ_[2]) ^ 2 - 18 * (x : ℚ_[2]) + 9 =
    (((x ^ 4 + 9 * x ^ 2 - 18 * x + 9 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E15DoubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((E15DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((E15DoubleYNum x y : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 6 + 2 * (x : ℚ_[2]) ^ 5 - 25 * (x : ℚ_[2]) ^ 4 +
      36 * (x : ℚ_[2]) ^ 3 - 34 * (x : ℚ_[2]) ^ 2 + 27 * (x : ℚ_[2]) +
      (y : ℚ_[2]) * (-(x : ℚ_[2]) ^ 4 - 4 * (x : ℚ_[2]) ^ 3 -
        14 * (x : ℚ_[2]) ^ 2 + 36 * (x : ℚ_[2]) - 18) - 9 =
    (((x ^ 6 + 2 * x ^ 5 - 25 * x ^ 4 + 36 * x ^ 3 - 34 * x ^ 2 +
      27 * x + y * (-x ^ 4 - 4 * x ^ 3 - 14 * x ^ 2 + 36 * x - 18) -
      9 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem E15DoubleDen_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (E15DoubleDen x y) := by
  have hnorm := (E15DoubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((E15DoubleDenPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E15DoubleDenPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E15DoubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (E15DoubleXNum x) := by
  have hnorm := (E15DoubleXNumPadic (ratPadicInt x hx)).2
  change ‖((E15DoubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E15DoubleXNumPadic_coe x hx, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E15DoubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (E15DoubleYNum x y) := by
  have hnorm := (E15DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((E15DoubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [E15DoubleYNumPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem E15_padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE15 x y) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy +
        ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 + (ratPadicInt x hx) ^ 2 -
        5 * ratPadicInt x hx + 2 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) + (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 + (x : ℚ_[2]) ^ 2 - 5 * (x : ℚ_[2]) + 2
  unfold OnE15 at hE
  exact_mod_cast hE

private theorem E15DoubleDenPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E15DoubleDenPadic z w) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [E15DoubleDenPadic, map_add, map_mul, map_ofNat, hz, htwo]

private theorem E15DoubleDenPadic_red_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (E15DoubleDenPadic z w) = 0 := by
  by_cases hw : PadicInt.toZMod w = 0
  · simp [E15DoubleDenPadic, map_add, map_mul, map_ofNat, hz, hw]
    decide
  · have hw1 : PadicInt.toZMod w = 1 :=
      zmod2_nonzero_eq_one _ hw
    simp [E15DoubleDenPadic, map_add, map_mul, map_ofNat, hz, hw1]
    decide

private theorem E15DoubleXNumPadic_red_zero
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E15DoubleXNumPadic z) = 1 := by
  simp [E15DoubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, hz]
  decide

private theorem E15DoubleXNumPadic_red_one
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (E15DoubleXNumPadic z) = 1 := by
  simp [E15DoubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, hz]
  decide

private theorem E15DoubleYNumPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (E15DoubleYNumPadic z w) = 1 := by
  by_cases hw : PadicInt.toZMod w = 0
  · simp [E15DoubleYNumPadic, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, hz, hw]
    decide
  · have hw1 : PadicInt.toZMod w = 1 :=
      zmod2_nonzero_eq_one _ hw
    simp [E15DoubleYNumPadic, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, hz, hw1]
    decide

private theorem E15DoubleYNumPadic_red_one_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (E15DoubleYNumPadic z w) = 1 := by
  simp [E15DoubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, hz, hw]
  decide

private theorem ratPadicInt_E15DoubleDen
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (E15DoubleDen x y) (E15DoubleDen_integral x y hx hy) =
      E15DoubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (E15DoubleDenPadic_coe x y hx hy).symm

private theorem ratPadicInt_E15DoubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (E15DoubleXNum x) (E15DoubleXNum_integral x hx) =
      E15DoubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (E15DoubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_E15DoubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (E15DoubleYNum x y) (E15DoubleYNum_integral x y hx hy) =
      E15DoubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (E15DoubleYNumPadic_coe x y hx hy).symm

private theorem E15_y_red_one_of_x_red_one
    {x y : ℚ} (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : OnE15 x y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx) = 1) :
    PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (E15_padicInt_equation hx hy hE)
  simp [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    hxred] at heq
  by_cases hyred : PadicInt.toZMod (ratPadicInt y hy) = 0
  · rw [hyred] at heq
    norm_num at heq
  · exact zmod2_nonzero_eq_one _ hyred

private theorem rat_ne_zero_of_padic_red_one
    {q : ℚ} (hq : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hq) = 1) :
    q ≠ 0 := by
  intro hzero
  have hz : ratPadicInt q hq = 0 := by
    apply Subtype.ext
    change (q : ℚ_[2]) = 0
    simp [hzero]
  rw [hz, map_zero] at hred
  norm_num at hred

private theorem E15_double_formal_of_integral_x_unit
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E15Curve x y}
    (hxn : x ≠ 0) (hx : padicValRat 2 x = 0)
    (hy : 0 ≤ padicValRat 2 y) :
    E15FormalAtTwo
      (2 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := by omega
  have hE : OnE15 x y := (E15Curve_equation_iff x y).mp h.1
  have hxred := ratPadicInt_red_eq_one_of_val_zero hxn hx
  have hyred := E15_y_red_one_of_x_red_one hx0 hy hE hxred
  have hDi := E15DoubleDen_integral x y hx0 hy
  have hDred : PadicInt.toZMod
      (ratPadicInt (E15DoubleDen x y) hDi) = 0 := by
    rw [ratPadicInt_E15DoubleDen x y hx0 hy]
    exact E15DoubleDenPadic_red_one hxred
  by_cases hd : E15DoubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = WeierstrassCurve.Affine.negY E15Curve x y := by
      simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at hd ⊢
      linarith
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hYeq]
    trivial
  · have hvd : 0 < padicValRat 2 (E15DoubleDen x y) :=
      val_pos_of_rational_padicInt_red_zero hd hDi hDred
    have hNi := E15DoubleXNum_integral x hx0
    have hYi := E15DoubleYNum_integral x y hx0 hy
    have hNred : PadicInt.toZMod
        (ratPadicInt (E15DoubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_E15DoubleXNum x hx0]
      exact E15DoubleXNumPadic_red_one hxred
    have hYred : PadicInt.toZMod
        (ratPadicInt (E15DoubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_E15DoubleYNum x y hx0 hy]
      exact E15DoubleYNumPadic_red_one_one hxred hyred
    have hN : E15DoubleXNum x ≠ 0 :=
      rat_ne_zero_of_padic_red_one hNi hNred
    have hY : E15DoubleYNum x y ≠ 0 :=
      rat_ne_zero_of_padic_red_one hYi hYred
    have hvN : padicValRat 2 (E15DoubleXNum x) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hN hNi (by
        rw [hNred]
        norm_num)
    have hvY : padicValRat 2 (E15DoubleYNum x y) = 0 :=
      val_zero_of_rational_padicInt_red_nonzero hY hYi (by
        rw [hYred]
        norm_num)
    have hneg : y ≠ WeierstrassCurve.Affine.negY E15Curve x y := by
      intro heq
      apply hd
      simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at heq ⊢
      linarith
    rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (E15DoubleDen x y), hvd, ?_, ?_⟩
    · rw [E15_doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN,
        padicValRat.pow hd]
      ring
    · rw [E15_doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY,
        padicValRat.pow hd]
      ring

private theorem E15_four_formal_of_integral_x_red_zero
    {x y : ℚ} {h : WeierstrassCurve.Affine.Nonsingular E15Curve x y}
    (hx0 : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx0) = 0) :
    E15FormalAtTwo
      (4 • WeierstrassCurve.Affine.Point.some x y h) := by
  have hE : OnE15 x y := (E15Curve_equation_iff x y).mp h.1
  have hDi := E15DoubleDen_integral x y hx0 hy
  have hDred : PadicInt.toZMod
      (ratPadicInt (E15DoubleDen x y) hDi) = 1 := by
    rw [ratPadicInt_E15DoubleDen x y hx0 hy]
    exact E15DoubleDenPadic_red_zero hxred
  have hd : E15DoubleDen x y ≠ 0 :=
    rat_ne_zero_of_padic_red_one hDi hDred
  have hvd : padicValRat 2 (E15DoubleDen x y) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hd hDi (by
      rw [hDred]
      norm_num)
  have hNi := E15DoubleXNum_integral x hx0
  have hYi := E15DoubleYNum_integral x y hx0 hy
  have hNred : PadicInt.toZMod
      (ratPadicInt (E15DoubleXNum x) hNi) = 1 := by
    rw [ratPadicInt_E15DoubleXNum x hx0]
    exact E15DoubleXNumPadic_red_zero hxred
  have hYred : PadicInt.toZMod
      (ratPadicInt (E15DoubleYNum x y) hYi) = 1 := by
    rw [ratPadicInt_E15DoubleYNum x y hx0 hy]
    exact E15DoubleYNumPadic_red_zero hxred
  have hN : E15DoubleXNum x ≠ 0 :=
    rat_ne_zero_of_padic_red_one hNi hNred
  have hY : E15DoubleYNum x y ≠ 0 :=
    rat_ne_zero_of_padic_red_one hYi hYred
  have hvN : padicValRat 2 (E15DoubleXNum x) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hN hNi (by
      rw [hNred]
      norm_num)
  have hvY : padicValRat 2 (E15DoubleYNum x y) = 0 :=
    val_zero_of_rational_padicInt_red_nonzero hY hYi (by
      rw [hYred]
      norm_num)
  have hneg : y ≠ WeierstrassCurve.Affine.negY E15Curve x y := by
    intro heq
    apply hd
    simp [E15DoubleDen, E15Curve, WeierstrassCurve.Affine.negY] at heq ⊢
    linarith
  have hfour : 4 • WeierstrassCurve.Affine.Point.some x y h =
      2 • (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) := by
    rw [← two_nsmul]
    norm_num [← mul_nsmul]
  rw [hfour, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
  have hx2ne :
      WeierstrassCurve.Affine.addX E15Curve x x
        (WeierstrassCurve.Affine.slope E15Curve x x y y) ≠ 0 := by
    rw [E15_doubleX_formula hd hE]
    exact div_ne_zero hN (pow_ne_zero 2 hd)
  apply E15_double_formal_of_integral_x_unit
  · exact hx2ne
  · rw [E15_doubleX_formula hd hE,
      padicValRat.div hN (pow_ne_zero 2 hd),
      padicValRat.pow hd, hvN, hvd]
    norm_num
  · rw [E15_doubleY_formula hd hE,
      padicValRat.div hY (pow_ne_zero 3 hd),
      padicValRat.pow hd, hvY, hvd]
    norm_num

/-- Doubling preserves the formal kernel at two. -/
theorem E15FormalAtTwo_double {P : E15Point}
    (hP : E15FormalAtTwo P) : E15FormalAtTwo (2 • P) := by
  rw [E15FormalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases E15FormalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-- Four times every rational point is in the formal kernel at two. -/
theorem E15_four_nsmul_formal (P : E15Point) :
    E15FormalAtTwo (4 • P) := by
  rcases E15_formal_or_integral P with hformal | hintegral
  · have h2 := E15FormalAtTwo_double hformal
    have h4 := E15FormalAtTwo_double h2
    rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]]
    exact h4
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hx, hy⟩
        by_cases hxzero : x = 0
        · have hxred : PadicInt.toZMod (ratPadicInt x hx) = 0 := by
            have hxi : ratPadicInt x hx = 0 := by
              apply Subtype.ext
              change (x : ℚ_[2]) = 0
              simp [hxzero]
            rw [hxi, map_zero]
          exact E15_four_formal_of_integral_x_red_zero hx hy hxred
        · by_cases hxunit : padicValRat 2 x = 0
          · have h2 := E15_double_formal_of_integral_x_unit
              (h := h) hxzero hxunit hy
            have h4 := E15FormalAtTwo_double h2
            rw [show 4 • WeierstrassCurve.Affine.Point.some x y h =
                2 • (2 • WeierstrassCurve.Affine.Point.some x y h) by
                  norm_num [← mul_nsmul]]
            exact h4
          · have hxpos : 0 < padicValRat 2 x :=
              lt_of_le_of_ne hx (Ne.symm hxunit)
            have hxred :=
              ratPadicInt_red_eq_zero_of_val_pos hxzero hxpos
            exact E15_four_formal_of_integral_x_red_zero hx hy hxred

private theorem E15FormalLevel_unique {P : E15Point} {k l : ℤ}
    (hk : E15FormalLevel P k) (hl : E15FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [E15FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Repeated doubling of a nonzero formal point raises its formal level by
at least the number of doublings. -/
theorem E15FormalLevel_two_power {P : E15Point} {k : ℤ}
    (hP : E15FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + (n : ℤ) ≤ k' ∧
        E15FormalLevel ((2 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      right
      exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) • P =
          2 • ((2 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      rcases ih with hzero | ⟨l, hkl, hl⟩
      · left
        rw [hpow, hzero, nsmul_zero]
      · rcases E15FormalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [hpow, hzero]
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rwa [hpow]

/-- The two-adic formal kernel has no nonzero element divisible by every
power of two through points of the formal kernel. -/
theorem E15_formal_separated (P : E15Point)
    (hP : E15FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : E15Point,
      E15FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, E15FormalLevel P k := by
    rw [E15FormalAtTwo_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, E15FormalLevel Q l := by
    rw [E15FormalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => exact (hQ0 rfl).elim
    | some x y h => exact hl.1
  rcases E15FormalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : E15FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := E15FormalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k := by
      exact Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat] at hbound
    omega


/-- Weak descent and two-adic separatedness kill every rational point by four. -/
theorem n15Aux_four_nsmul_eq_zero (P : N15AuxPoint) : 4 • P = 0 := by
  let P0 : E15Point := E15AuxAddEquiv.symm P
  have hP0formal : E15FormalAtTwo (4 • P0) :=
    E15_four_nsmul_formal P0
  have hdiv : ∀ n : ℕ, ∃ Q0 : E15Point,
      E15FormalAtTwo Q0 ∧ 4 • P0 = (2 ^ n : ℕ) • Q0 := by
    intro n
    obtain ⟨Q, hQ⟩ := n15Aux_four_nsmul_two_power_divisible P n
    refine ⟨4 • E15AuxAddEquiv.symm Q,
      E15_four_nsmul_formal (E15AuxAddEquiv.symm Q), ?_⟩
    have hm := congrArg E15AuxAddEquiv.symm hQ
    simpa only [map_nsmul, AddEquiv.symm_apply_apply, P0] using hm
  have hzero : 4 • P0 = 0 :=
    E15_formal_separated (4 • P0) hP0formal hdiv
  have hm := congrArg E15AuxAddEquiv hzero
  simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, P0] using hm

/-! ## Explicit four-torsion exhaustion -/

private theorem n15Aux_y_zero_of_double_zero {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y}
    (h2 : 2 • (WeierstrassCurve.Affine.Point.some x y h : N15AuxPoint) = 0) :
    y = 0 := by
  have hadd : (WeierstrassCurve.Affine.Point.some x y h : N15AuxPoint) +
      WeierstrassCurve.Affine.Point.some x y h = 0 := by
    simpa only [two_nsmul] using h2
  have hneg := eq_neg_of_add_eq_zero_left hadd
  rw [WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hneg
  simp [n15AuxCurve, WeierstrassCurve.Affine.negY] at hneg
  linarith

private theorem n15Aux_doubleX_formula {x y : ℚ}
    (hy : y ≠ 0) (hE : N15AuxiliaryEquation x y) :
    WeierstrassCurve.Affine.addX n15AuxCurve x x
        (WeierstrassCurve.Affine.slope n15AuxCurve x x y y) =
      (x ^ 2 - 240) ^ 2 / (4 * y ^ 2) := by
  rw [n15AuxCurve_slope_self hy, n15AuxCurve_addX_tangent]
  unfold n15TangentX n15AuxTangent
  field_simp [hy]
  unfold N15AuxiliaryEquation at hE
  rw [hE]
  ring

private theorem rat_sq_ne_fifteen (q : ℚ) : q ^ 2 ≠ 15 := by
  intro h
  have hs : IsSquare (15 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem rat_sq_ne_two_forty (q : ℚ) : q ^ 2 ≠ 240 := by
  intro h
  have hs : IsSquare (240 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

/-- The seven affine rational points on the N15 auxiliary cubic. -/
theorem X115_affine_exhaustion {X Y : ℚ} (hcurve : OnX115 X Y) :
    X115AffineCandidate X Y := by
  have hE : N15AuxiliaryEquation X Y := by
    simpa [OnX115, N15AuxiliaryEquation] using hcurve
  have hns : WeierstrassCurve.Affine.Nonsingular n15AuxCurve X Y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15AuxCurve_equation_iff X Y).mpr hE)
  unfold X115AffineCandidate
  by_cases hY : Y = 0
  · rcases n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero hE hY with
      hX0 | hX15 | hX16
    · exact Or.inl ⟨hX0, hY⟩
    · exact Or.inr (Or.inl ⟨hX15, hY⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hX16, hY⟩))
  · let P : N15AuxPoint :=
      WeierstrassCurve.Affine.Point.some X Y hns
    have hfour : 2 • (2 • P) = 0 := by
      have h4 := n15Aux_four_nsmul_eq_zero P
      rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]] at h4
      exact h4
    have hneg : Y ≠ WeierstrassCurve.Affine.negY n15AuxCurve X Y :=
      n15Aux_y_ne_negY hY
    dsimp only [P] at hfour
    simp only [two_nsmul] at hfour
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg] at hfour
    let X2 := WeierstrassCurve.Affine.addX n15AuxCurve X X
      (WeierstrassCurve.Affine.slope n15AuxCurve X X Y Y)
    let Y2 := WeierstrassCurve.Affine.addY n15AuxCurve X X Y
      (WeierstrassCurve.Affine.slope n15AuxCurve X X Y Y)
    have hY2 : Y2 = 0 := by
      apply n15Aux_y_zero_of_double_zero
      simpa only [two_nsmul] using hfour
    have hns2 : WeierstrassCurve.Affine.Nonsingular n15AuxCurve X2 Y2 := by
      dsimp only [X2, Y2]
      exact WeierstrassCurve.Affine.nonsingular_add hns hns
        (fun hbad => hneg hbad.2)
    have hE2 : N15AuxiliaryEquation X2 Y2 :=
      (n15AuxCurve_equation_iff X2 Y2).mp hns2.1
    have hX2cases : X2 = 0 ∨ X2 = 15 ∨ X2 = 16 :=
      n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero hE2 hY2
    have hX2formula : X2 = (X ^ 2 - 240) ^ 2 / (4 * Y ^ 2) := by
      exact n15Aux_doubleX_formula hY hE
    have hX2 : X2 = 16 := by
      rcases hX2cases with h0 | h15 | h16
      · exfalso
        rw [h0] at hX2formula
        have hden : 4 * Y ^ 2 ≠ 0 :=
          mul_ne_zero (by norm_num) (pow_ne_zero 2 hY)
        have hnum : (X ^ 2 - 240) ^ 2 = 0 :=
          ((div_eq_zero_iff).mp hX2formula.symm).resolve_right hden
        apply rat_sq_ne_two_forty X
        nlinarith [sq_nonneg (X ^ 2 - 240)]
      · exfalso
        have hsquare : ((X ^ 2 - 240) / (2 * Y)) ^ 2 = 15 := by
          rw [h15] at hX2formula
          field_simp [hY] at hX2formula ⊢
          nlinarith
        exact rat_sq_ne_fifteen _ hsquare
      · exact h16
    have hnum : (X ^ 2 - 240) ^ 2 = 64 * Y ^ 2 := by
      rw [hX2] at hX2formula
      field_simp [hY] at hX2formula
      nlinarith
    have hfactor : (X - 20) ^ 2 * (X - 12) ^ 2 = 0 := by
      unfold N15AuxiliaryEquation at hE
      rw [hE] at hnum
      nlinarith [hnum]
    rcases mul_eq_zero.mp hfactor with h20sq | h12sq
    · have hX : X = 20 := by
        have : X - 20 = 0 := (sq_eq_zero_iff).mp h20sq
        linarith
      have hYsq : Y ^ 2 = 20 ^ 2 := by
        unfold N15AuxiliaryEquation at hE
        rw [hX] at hE
        norm_num at hE ⊢
        exact hE
      have hYfac : (Y - 20) * (Y + 20) = 0 := by nlinarith
      rcases mul_eq_zero.mp hYfac with hYp | hYm
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hX, by linarith⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨hX, by linarith⟩)))))
    · have hX : X = 12 := by
        have : X - 12 = 0 := (sq_eq_zero_iff).mp h12sq
        linarith
      have hYsq : Y ^ 2 = 12 ^ 2 := by
        unfold N15AuxiliaryEquation at hE
        rw [hX] at hE
        norm_num at hE ⊢
        exact hE
      have hYfac : (Y - 12) * (Y + 12) = 0 := by nlinarith
      rcases mul_eq_zero.mp hYfac with hYp | hYm
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hX, by linarith⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hX, by linarith⟩))))











end


end MazurProof.RationalPointsX115
