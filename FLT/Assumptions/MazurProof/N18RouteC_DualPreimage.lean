import FLT.Assumptions.MazurProof.N18RouteC_KummerGeometry
import FLT.Assumptions.MazurProof.N18RouteC_TwoAdic

/-!
# Explicit preimages for the dual three-isogeny

For the translated Tate model

`w (w - 3u + 2) = u³`,

the Kummer value away from the tangent point is `w`.  If `w = c³`, the
formulas below give a point on the dual curve whose image is `(u,w)`.  The
only tangent value is `1/2`; the inert valuation above two proves that it is
not a cube.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.DualPreimage

open Isogeny IsogenyPoints KummerGeometry

noncomputable section

def preimageD (u c : L) : L := u - c ^ 2 + c

def preimageXi (u c : L) : L := 9 * c / preimageD u c - 3

def preimageEta (u c : L) : L :=
  27 * (u + c ^ 2) / (2 * preimageD u c) +
    (3 / 2 : L) * preimageXi u c - 1

private theorem nonsingular_of_residual_eq_zero
    {W : WeierstrassCurve L} [W.IsElliptic]
    {x y : L} (h : affineResidual W x y = 0) :
    WeierstrassCurve.Affine.Nonsingular W x y := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff']
  simpa [affineResidual] using h

theorem preimageD_ne_zero {u c : L} (hc : c ≠ 0)
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3) :
    preimageD u c ≠ 0 := by
  intro hd
  have hu : u = c ^ 2 - c := by
    unfold preimageD at hd
    linear_combination hd
  have hc3 : c ^ 3 = 0 := by
    rw [hu] at hcurve
    ring_nf at hcurve ⊢
    linear_combination (1 / 3 : L) * hcurve
  exact hc ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hc3)

@[simp] theorem dualX_preimageXi (u c : L) :
    dualX (preimageXi u c) = 9 * c / preimageD u c := by
  unfold dualX preimageXi
  ring

@[simp] theorem dualZ_preimage (u c : L) :
    dualZ (preimageXi u c) (preimageEta u c) =
      27 * (u + c ^ 2) / (2 * preimageD u c) := by
  unfold dualZ preimageEta
  ring

theorem preimage_residual {u c : L}
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3)
    (hd : preimageD u c ≠ 0) :
    affineResidual Ehat0 (preimageXi u c) (preimageEta u c) = 0 := by
  have hcompleted :
      veluCompletedResidual
          (dualX (preimageXi u c))
          (dualZ (preimageXi u c) (preimageEta u c)) = 0 := by
    rw [dualX_preimageXi, dualZ_preimage]
    unfold veluCompletedResidual
    field_simp [hd]
    unfold preimageD at *
    ring_nf at hcurve ⊢
    linear_combination -3888 * hcurve
  have hid := velu_completed_change_identity
    (preimageXi u c) (preimageEta u c)
  rw [hcompleted] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left (by norm_num)

theorem preimage_u {u c : L} (hc : c ≠ 0)
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3)
    (hd : preimageD u c ≠ 0) :
    phihatU (preimageXi u c) = u := by
  unfold phihatU U
  rw [dualX_preimageXi]
  field_simp [hc, hd]
  unfold preimageD at *
  ring_nf at hcurve ⊢
  linear_combination 243 * hcurve

theorem preimage_x {u c : L} (hc : c ≠ 0)
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3)
    (hd : preimageD u c ≠ 0) :
    phihatX0 (preimageXi u c) = u + 1 := by
  unfold phihatX0
  rw [preimage_u hc hcurve hd]

theorem preimage_completedY {u c : L} (hc : c ≠ 0)
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3)
    (hd : preimageD u c ≠ 0) :
    phihatCompletedY (preimageXi u c) (preimageEta u c) =
      c ^ 3 - (3 / 2 : L) * u + 1 := by
  unfold phihatCompletedY V
  rw [dualX_preimageXi, dualZ_preimage]
  field_simp [hc, hd]
  unfold preimageD at *
  ring_nf at hcurve ⊢
  linear_combination
    243 * (4 * c ^ 2 - 3 * c - 2 * u) * hcurve

theorem preimage_y {u c : L} (hc : c ≠ 0)
    (hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3)
    (hd : preimageD u c ≠ 0) :
    phihatY0 (preimageXi u c) (preimageEta u c) = c ^ 3 - 2 * u := by
  unfold phihatY0
  rw [preimage_completedY hc hcurve hd, preimage_u hc hcurve hd]
  ring

/-- A cube dual Kummer value gives an actual preimage under the dual
three-isogeny.  This is the geometric half of the weak descent. -/
theorem exists_phihat_preimage_of_kappa_cube (P : E0Point)
    (hcube : ∃ c : L, c ^ 3 = kappa P) :
    ∃ Q : Ehat0Point, phihatPoint Q = P := by
  rcases hcube with ⟨c, hcub⟩
  cases P with
  | zero =>
      exact ⟨0, phihatPoint_zero⟩
  | some x y h =>
      by_cases hT : x = 1 ∧ y = 0
      · exfalso
        apply TwoAdic.half_not_cube c
        simpa [kappa, hT] using hcub
      · have hwcube : c ^ 3 = tateW x y := by
          simpa [kappa_some_of_ne_T h hT] using hcub
        have hc : c ≠ 0 := by
          intro hc0
          apply kappa_ne_zero (.some x y h)
          rw [← hcub, hc0]
          norm_num
        let u : L := tateU x
        have hcurve : c ^ 3 * (c ^ 3 - 3 * u + 2) = u ^ 3 := by
          have hraw := translated_curve_equation h
          rw [← hwcube] at hraw
          exact hraw
        have hd : preimageD u c ≠ 0 := preimageD_ne_zero hc hcurve
        let xi : L := preimageXi u c
        let eta : L := preimageEta u c
        have hres : affineResidual Ehat0 xi eta = 0 := by
          exact preimage_residual hcurve hd
        let hQ : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta :=
          nonsingular_of_residual_eq_zero hres
        refine ⟨.some xi eta hQ, ?_⟩
        rw [phihatPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · calc
            phihatX0 xi = u + 1 := preimage_x hc hcurve hd
            _ = x := by simp [u, tateU]
        · calc
            phihatY0 xi eta = c ^ 3 - 2 * u := preimage_y hc hcurve hd
            _ = y := by rw [hwcube]; simp [u, tateU, tateW]; ring

end

end MazurProof.N18RouteC.DualPreimage
