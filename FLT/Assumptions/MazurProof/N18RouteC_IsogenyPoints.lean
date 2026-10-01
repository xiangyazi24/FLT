import FLT.Assumptions.MazurProof.N18RouteC_FieldArithmetic
import FLT.Assumptions.MazurProof.N18RouteC_Isogeny

/-!
# Total point maps for the N18 three-isogeny

The rational formulas in `N18RouteC_Isogeny` are extended across their
exceptional fibers.  The source exceptional fiber is the rational kernel
`{O,T,-T}`.  The apparent dual exceptional fiber `xi = -3` has no point over
the totally real cubic field; the norm argument below proves this directly.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.IsogenyPoints

open FieldArithmetic Isogeny

noncomputable section

private theorem residual_eq_zero_of_nonsingular
    {W : WeierstrassCurve L} [W.IsElliptic]
    {x y : L} (h : WeierstrassCurve.Affine.Nonsingular W x y) :
    affineResidual W x y = 0 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simpa [affineResidual] using heq

private theorem nonsingular_of_residual_eq_zero
    {W : WeierstrassCurve L} [W.IsElliptic]
    {x y : L} (h : affineResidual W x y = 0) :
    WeierstrassCurve.Affine.Nonsingular W x y := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff']
  simpa [affineResidual] using h

theorem dualX_ne_zero_of_nonsingular {xi eta : L}
    (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    dualX xi ≠ 0 := by
  intro hX
  have hxi : xi = -3 := by
    unfold dualX at hX
    linear_combination hX
  have hcurve := residual_eq_zero_of_nonsingular h
  have hsquare : (2 * eta + 11) ^ 2 = (-243 : L) := by
    unfold affineResidual Ehat0 at hcurve
    rw [hxi] at hcurve
    linear_combination 4 * hcurve
  have hnorm :
      (Algebra.norm ℚ (2 * eta + 11)) ^ 2 = (-243 : ℚ) ^ 3 := by
    calc
      (Algebra.norm ℚ (2 * eta + 11)) ^ 2 =
          Algebra.norm ℚ ((2 * eta + 11) ^ 2) := by rw [map_pow]
      _ = Algebra.norm ℚ (-243 : L) := by rw [hsquare]
      _ = (-243 : ℚ) ^ Module.finrank ℚ L := by
        simpa only [map_neg, map_ofNat] using
          (Algebra.norm_algebraMap (S := L) (-243 : ℚ))
      _ = (-243 : ℚ) ^ 3 := by rw [finrank_L]
  nlinarith [sq_nonneg (Algebra.norm ℚ (2 * eta + 11))]

noncomputable def phiPoint : E0Point → Ehat0Point
  | .zero => .zero
  | .some x y h =>
      if hu : tateU x = 0 then .zero
      else
        .some (phiXi x) (phiEta x y) <|
          nonsingular_of_residual_eq_zero <|
            phi_preserves_curve (residual_eq_zero_of_nonsingular h) hu

noncomputable def phihatPoint : Ehat0Point → E0Point
  | .zero => .zero
  | .some xi eta h =>
      .some (phihatX0 xi) (phihatY0 xi eta) <|
        nonsingular_of_residual_eq_zero <|
          phihat_preserves_curve (residual_eq_zero_of_nonsingular h)
            (dualX_ne_zero_of_nonsingular h)

@[simp] theorem phiPoint_zero : phiPoint 0 = 0 := rfl

@[simp] theorem phihatPoint_zero : phihatPoint 0 = 0 := rfl

theorem phiPoint_some_of_tateU_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) :
    phiPoint (.some x y h) =
      .some (phiXi x) (phiEta x y)
        (nonsingular_of_residual_eq_zero <|
          phi_preserves_curve (residual_eq_zero_of_nonsingular h) hu) := by
  simp [phiPoint, hu]

theorem phiPoint_some_of_tateU_eq_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x = 0) :
    phiPoint (.some x y h) = 0 := by
  change (if _h : tateU x = 0 then (.zero : Ehat0Point) else _) = 0
  rw [dif_pos hu]
  rfl

theorem phihatPoint_some {xi eta : L}
    (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    phihatPoint (.some xi eta h) =
      .some (phihatX0 xi) (phihatY0 xi eta)
        (nonsingular_of_residual_eq_zero <|
          phihat_preserves_curve (residual_eq_zero_of_nonsingular h)
            (dualX_ne_zero_of_nonsingular h)) := rfl

@[simp] theorem phiPoint_T : phiPoint T = 0 := by
  apply phiPoint_some_of_tateU_eq_zero
  simp [tateU, T]

@[simp] theorem phiPoint_negT : phiPoint negT = 0 := by
  apply phiPoint_some_of_tateU_eq_zero
  simp [tateU, negT]

end

end MazurProof.N18RouteC.IsogenyPoints
