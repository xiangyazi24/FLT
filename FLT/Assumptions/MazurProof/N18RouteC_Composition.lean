import FLT.Assumptions.MazurProof.N18RouteC_DualPreimage

/-!
# Composition of the explicit three-isogenies

The proof is pointwise; no bundled morphism or additivity API is needed.  We
complete the square on the source only for the calculation.  Thus

`Y = 2y + x + 1` and `Y² = 4x³ - 3x² - 18x + 21`.

In these coordinates the ordinary tangent-and-chord formulas have no linear
`Y` term, so the generic composition is a fixed rational-function identity
modulo this one equation.  The `Y = 0` branch is the two-torsion branch and is
checked separately.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.Composition

open Isogeny IsogenyPoints KummerGeometry

noncomputable section

def completedY (x y : L) : L := 2 * y + x + 1

def completedCubic (x : L) : L :=
  4 * x ^ 3 - 3 * x ^ 2 - 18 * x + 21

def completedTangent (x Y : L) : L :=
  3 * (2 * x ^ 2 - x - 3) / Y

def completedDoubleX (x Y : L) : L :=
  (completedTangent x Y ^ 2 + 3) / 4 - 2 * x

def completedDoubleY (x Y : L) : L :=
  -(completedTangent x Y * (completedDoubleX x Y - x) + Y)

def completedTripleSlope (x Y : L) : L :=
  (completedDoubleY x Y - Y) / (completedDoubleX x Y - x)

def completedTripleX (x Y : L) : L :=
  (completedTripleSlope x Y ^ 2 + 3) / 4 -
    completedDoubleX x Y - x

def completedTripleY (x Y : L) : L :=
  -(completedTripleSlope x Y *
      (completedTripleX x Y - completedDoubleX x Y) +
    completedDoubleY x Y)

def fromCompletedY (x Y : L) : L := (Y - x - 1) / 2

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

theorem completed_curve_equation {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y) :
    completedY x y ^ 2 = completedCubic x := by
  have hres := residual_eq_zero_of_nonsingular h
  unfold completedY completedCubic affineResidual E0 at *
  linear_combination 4 * hres

theorem fromCompletedY_completedY (x y : L) :
    fromCompletedY x (completedY x y) = y := by
  unfold fromCompletedY completedY
  ring

theorem dualX_phiXi {x : L} (hu : tateU x ≠ 0) :
    dualX (phiXi x) =
      (tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4) /
        tateU x ^ 2 := by
  unfold dualX phiXi C
  field_simp [hu]
  ring

private theorem dualX_phiXi_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) :
    dualX (phiXi x) ≠ 0 := by
  apply dualX_ne_zero_of_nonsingular
  apply nonsingular_of_residual_eq_zero
  exact phi_preserves_curve (residual_eq_zero_of_nonsingular h) hu

private theorem completedDoubleX_sub_identity {x Y : L}
    (hY : Y ≠ 0) (hcurve : Y ^ 2 = completedCubic x) :
    Y ^ 2 * (completedDoubleX x Y - x) =
      -3 * (x - 1) * (x ^ 3 - 9 * x + 12) := by
  unfold completedDoubleX completedTangent completedCubic at *
  field_simp [hY]
  ring_nf at hcurve ⊢
  linear_combination -3 * (4 * x - 1) * hcurve

private theorem completedDoubleX_ne_self {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) (hY : completedY x y ≠ 0) :
    completedDoubleX x (completedY x y) ≠ x := by
  have hcurve := completed_curve_equation h
  have hid := completedDoubleX_sub_identity hY hcurve
  have hx1 : x - 1 ≠ 0 := by simpa [tateU] using hu
  have hdual := dualX_phiXi_ne_zero h hu
  have hfac : x ^ 3 - 9 * x + 12 ≠ 0 := by
    intro hzero
    apply hdual
    rw [dualX_phiXi hu]
    have hnum :
        tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 =
          x ^ 3 - 9 * x + 12 := by
      unfold tateU
      ring
    rw [hnum, hzero, zero_div]
  intro hxx
  rw [hxx, sub_self, mul_zero] at hid
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hx1) hfac) hid.symm

def tripleG (x : L) : L := x ^ 3 - 9 * x + 12

def completedTripleSlopeSimple (x Y : L) : L :=
  -completedTangent x Y +
    2 * Y ^ 3 / (3 * (x - 1) * tripleG x)

private theorem tripleG_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hu : tateU x ≠ 0) : tripleG x ≠ 0 := by
  have hdual := dualX_phiXi_ne_zero h hu
  intro hg
  apply hdual
  rw [dualX_phiXi hu]
  have hnum :
      tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
    unfold tateU tripleG
    ring
  rw [hnum, hg, zero_div]

private theorem completedTripleSlope_eq_simple {x Y : L}
    (hx1 : x - 1 ≠ 0) (hY : Y ≠ 0) (hg : tripleG x ≠ 0)
    (hxx : completedDoubleX x Y ≠ x)
    (hcurve : Y ^ 2 = completedCubic x) :
    completedTripleSlope x Y = completedTripleSlopeSimple x Y := by
  unfold completedTripleSlope
  apply (div_eq_iff (sub_ne_zero.mpr hxx)).2
  unfold completedTripleSlopeSimple completedDoubleY
  unfold completedDoubleX completedTangent at *
  field_simp [hx1, hY, hg]
  have hY4 : Y ^ 4 = completedCubic x ^ 2 := by
    calc Y ^ 4 = (Y ^ 2) ^ 2 := by ring
         _ = completedCubic x ^ 2 := by rw [hcurve]
  have hY6 : Y ^ 6 = completedCubic x ^ 3 := by
    calc Y ^ 6 = (Y ^ 2) ^ 3 := by ring
         _ = completedCubic x ^ 3 := by rw [hcurve]
  unfold tripleG
  ring_nf
  simp only [hcurve, hY4, hY6]
  unfold completedCubic
  ring

private theorem completed_power_reductions {x Y : L}
    (h : Y ^ 2 = completedCubic x) :
    Y ^ 3 = Y * completedCubic x ∧
    Y ^ 4 = completedCubic x ^ 2 ∧
    Y ^ 5 = Y * completedCubic x ^ 2 ∧
    Y ^ 6 = completedCubic x ^ 3 ∧
    Y ^ 7 = Y * completedCubic x ^ 3 ∧
    Y ^ 8 = completedCubic x ^ 4 ∧
    Y ^ 9 = Y * completedCubic x ^ 4 := by
  constructor
  · calc Y ^ 3 = Y * Y ^ 2 := by ring
         _ = Y * completedCubic x := by rw [h]
  constructor
  · calc Y ^ 4 = (Y ^ 2) ^ 2 := by ring
         _ = completedCubic x ^ 2 := by rw [h]
  constructor
  · calc Y ^ 5 = Y * (Y ^ 2) ^ 2 := by ring
         _ = Y * completedCubic x ^ 2 := by rw [h]
  constructor
  · calc Y ^ 6 = (Y ^ 2) ^ 3 := by ring
         _ = completedCubic x ^ 3 := by rw [h]
  constructor
  · calc Y ^ 7 = Y * (Y ^ 2) ^ 3 := by ring
         _ = Y * completedCubic x ^ 3 := by rw [h]
  constructor
  · calc Y ^ 8 = (Y ^ 2) ^ 4 := by ring
         _ = completedCubic x ^ 4 := by rw [h]
  · calc Y ^ 9 = Y * (Y ^ 2) ^ 4 := by ring
         _ = Y * completedCubic x ^ 4 := by rw [h]

set_option maxHeartbeats 0 in
private theorem generic_composition_x {x Y : L}
    (hu : tateU x ≠ 0) (hY : Y ≠ 0)
    (hdual : dualX (phiXi x) ≠ 0)
    (hxx : completedDoubleX x Y ≠ x)
    (hcurve : Y ^ 2 = completedCubic x) :
    phihatX0 (phiXi x) = completedTripleX x Y := by
  have hx1 : x - 1 ≠ 0 := by simpa [tateU] using hu
  have hg : tripleG x ≠ 0 := by
    intro hg0
    apply hdual
    rw [dualX_phiXi hu]
    have hnum :
        tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
      unfold tateU tripleG
      ring
    rw [hnum, hg0, zero_div]
  rcases completed_power_reductions hcurve with
    ⟨hY3, hY4, hY5, hY6, hY7, hY8, hY9⟩
  unfold completedTripleX
  rw [completedTripleSlope_eq_simple hx1 hY hg hxx hcurve]
  unfold phihatX0 phihatU U
  rw [dualX_phiXi hu]
  have hnum :
      tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
    unfold tateU tripleG
    ring
  rw [hnum]
  unfold completedTripleSlopeSimple completedDoubleX completedTangent tateU
  field_simp [hx1, hY, hg]
  unfold tripleG
  ring_nf
  simp only [hcurve, hY3, hY4, hY5, hY6, hY7, hY8, hY9]
  unfold completedCubic
  ring

set_option maxHeartbeats 0 in
private theorem generic_composition_completedY {x Y : L}
    (hu : tateU x ≠ 0) (hY : Y ≠ 0)
    (hdual : dualX (phiXi x) ≠ 0)
    (hxx : completedDoubleX x Y ≠ x)
    (hcurve : Y ^ 2 = completedCubic x) :
    2 * phihatY0 (phiXi x) (phiEta x (fromCompletedY x Y)) +
        phihatX0 (phiXi x) + 1 = completedTripleY x Y := by
  have hx1 : x - 1 ≠ 0 := by simpa [tateU] using hu
  have hg : tripleG x ≠ 0 := by
    intro hg0
    apply hdual
    rw [dualX_phiXi hu]
    have hnum :
        tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
      unfold tateU tripleG
      ring
    rw [hnum, hg0, zero_div]
  rcases completed_power_reductions hcurve with
    ⟨hY3, hY4, hY5, hY6, hY7, hY8, hY9⟩
  have hY10 : Y ^ 10 = completedCubic x ^ 5 := by
    calc Y ^ 10 = (Y ^ 2) ^ 5 := by ring
         _ = completedCubic x ^ 5 := by rw [hcurve]
  have hY11 : Y ^ 11 = Y * completedCubic x ^ 5 := by
    calc Y ^ 11 = Y * (Y ^ 2) ^ 5 := by ring
         _ = Y * completedCubic x ^ 5 := by rw [hcurve]
  have hY12 : Y ^ 12 = completedCubic x ^ 6 := by
    calc Y ^ 12 = (Y ^ 2) ^ 6 := by ring
         _ = completedCubic x ^ 6 := by rw [hcurve]
  unfold completedTripleY completedTripleX
  rw [completedTripleSlope_eq_simple hx1 hY hg hxx hcurve]
  unfold phihatY0 phihatX0 phihatCompletedY phihatU V U
  rw [dualX_phiXi hu]
  have hnum :
      tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
    unfold tateU tripleG
    ring
  rw [hnum]
  unfold dualZ
  unfold phiXi phiEta C N A B tateU tateW fromCompletedY
  unfold completedTripleSlopeSimple
    completedDoubleY completedDoubleX completedTangent
  field_simp [hx1, hY, hg]
  unfold tripleG
  ring_nf
  simp only [hcurve, hY3, hY4, hY5, hY6, hY7, hY8, hY9,
    hY10, hY11, hY12]
  unfold completedCubic
  ring

private theorem two_torsion_composition_x {x Y : L}
    (hu : tateU x ≠ 0)
    (hdual : dualX (phiXi x) ≠ 0)
    (hY : Y = 0) (hcurve : Y ^ 2 = completedCubic x) :
    phihatX0 (phiXi x) = x := by
  have hx1 : x - 1 ≠ 0 := by simpa [tateU] using hu
  have hg : tripleG x ≠ 0 := by
    intro hg0
    apply hdual
    rw [dualX_phiXi hu]
    have hnum :
        tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
      unfold tateU tripleG
      ring
    rw [hnum, hg0, zero_div]
  have hcubic : completedCubic x = 0 := by rw [← hcurve, hY]; norm_num
  unfold phihatX0 phihatU U
  rw [dualX_phiXi hu]
  have hnum :
      tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
    unfold tateU tripleG
    ring
  rw [hnum]
  unfold tateU
  field_simp [hx1, hg]
  unfold tripleG
  unfold completedCubic at hcubic
  ring_nf at hcubic ⊢
  linear_combination
    (-2 * x ^ 6 + 3 * x ^ 5 + 45 * x ^ 4 - 210 * x ^ 3 +
      360 * x ^ 2 - 297 * x + 117) * hcubic

private theorem two_torsion_composition_completedY {x Y : L}
    (hu : tateU x ≠ 0)
    (hdual : dualX (phiXi x) ≠ 0)
    (hY : Y = 0) :
    2 * phihatY0 (phiXi x) (phiEta x (fromCompletedY x Y)) +
        phihatX0 (phiXi x) + 1 = 0 := by
  have hx1 : x - 1 ≠ 0 := by simpa [tateU] using hu
  have hg : tripleG x ≠ 0 := by
    intro hg0
    apply hdual
    rw [dualX_phiXi hu]
    have hnum :
        tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
      unfold tateU tripleG
      ring
    rw [hnum, hg0, zero_div]
  subst Y
  unfold phihatY0 phihatX0 phihatCompletedY phihatU V U
  rw [dualX_phiXi hu]
  have hnum :
      tateU x ^ 3 + 3 * tateU x ^ 2 - 6 * tateU x + 4 = tripleG x := by
    unfold tateU tripleG
    ring
  rw [hnum]
  unfold dualZ
  unfold phiXi phiEta C N A B tateU tateW fromCompletedY
  field_simp [hx1, hg]
  unfold tripleG
  ring

@[simp] theorem E0_negY (x y : L) :
    WeierstrassCurve.Affine.negY E0 x y = -y - x - 1 := by
  simp [WeierstrassCurve.Affine.negY, E0]

private theorem E0_slope_self {x y : L} (hY : completedY x y ≠ 0) :
    WeierstrassCurve.Affine.slope E0 x x y y =
      (completedTangent x (completedY x y) - 1) / 2 := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E0 x y := by
    rw [E0_negY]
    intro heq
    apply hY
    unfold completedY
    linear_combination heq
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg, E0_negY]
  have hY' : 2 * y + x + 1 ≠ 0 := by simpa [completedY] using hY
  dsimp [E0, completedTangent, completedY]
  have hden : 1 + x + y * 2 ≠ 0 := by
    intro hd
    apply hY'
    linear_combination hd
  have hdeneq : y - (-y - x - 1) = 1 + x + y * 2 := by ring
  rw [hdeneq]
  apply (div_eq_iff hden).2
  field_simp [hden]
  ring

private theorem E0_addX_tangent (x y : L) :
    WeierstrassCurve.Affine.addX E0 x x
        ((completedTangent x (completedY x y) - 1) / 2) =
      completedDoubleX x (completedY x y) := by
  unfold WeierstrassCurve.Affine.addX E0 completedDoubleX
  ring

private theorem E0_addY_tangent (x y : L) :
    WeierstrassCurve.Affine.addY E0 x x y
        ((completedTangent x (completedY x y) - 1) / 2) =
      fromCompletedY (completedDoubleX x (completedY x y))
        (completedDoubleY x (completedY x y)) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX E0
  unfold fromCompletedY completedDoubleY completedDoubleX completedY
  ring

private theorem E0_slope_double {x Y : L}
    (hxx : completedDoubleX x Y ≠ x) :
    WeierstrassCurve.Affine.slope E0
        (completedDoubleX x Y) x
        (fromCompletedY (completedDoubleX x Y) (completedDoubleY x Y))
        (fromCompletedY x Y) =
      (completedTripleSlope x Y - 1) / 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxx]
  unfold fromCompletedY completedTripleSlope
  field_simp [sub_ne_zero.mpr hxx]
  ring

private theorem E0_slope_double_original {x y : L}
    (hxx : completedDoubleX x (completedY x y) ≠ x) :
    WeierstrassCurve.Affine.slope E0
        (completedDoubleX x (completedY x y)) x
        (fromCompletedY (completedDoubleX x (completedY x y))
          (completedDoubleY x (completedY x y))) y =
      (completedTripleSlope x (completedY x y) - 1) / 2 := by
  simpa only [fromCompletedY_completedY] using E0_slope_double hxx

private theorem E0_addX_double (x Y : L) :
    WeierstrassCurve.Affine.addX E0 (completedDoubleX x Y) x
        ((completedTripleSlope x Y - 1) / 2) =
      completedTripleX x Y := by
  unfold WeierstrassCurve.Affine.addX E0 completedTripleX
  ring

private theorem E0_addY_double (x Y : L) :
    WeierstrassCurve.Affine.addY E0 (completedDoubleX x Y) x
        (fromCompletedY (completedDoubleX x Y) (completedDoubleY x Y))
        ((completedTripleSlope x Y - 1) / 2) =
      fromCompletedY (completedTripleX x Y) (completedTripleY x Y) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX E0
  unfold fromCompletedY completedTripleY completedTripleX
  ring

/-- The two explicit degree-three maps compose pointwise to multiplication
by three, including the rational kernel and the two-torsion branch. -/
theorem phihat_phi_point (P : E0Point) :
    phihatPoint (phiPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hu : tateU x = 0
      · rw [phiPoint_some_of_tateU_eq_zero h hu, phihatPoint_zero]
        have hx : x = 1 := by
          unfold tateU at hu
          linear_combination hu
        have hcases :
            (WeierstrassCurve.Affine.Point.some x y h : E0Point) = T ∨
              (WeierstrassCurve.Affine.Point.some x y h : E0Point) = negT := by
          have heq := h.1
          rw [WeierstrassCurve.Affine.equation_iff] at heq
          have hy : y * (y + 2) = 0 := by
            simp only [E0] at heq
            rw [hx] at heq
            linear_combination heq
          rcases mul_eq_zero.mp hy with hy | hy
          · left
            rw [T, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hx, hy⟩
          · right
            rw [negT, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hx, by linear_combination hy⟩
        rcases hcases with hPT | hPnT
        · rw [hPT]
          exact three_nsmul_T.symm
        · rw [hPnT, ← neg_T]
          calc
            0 = -(3 • T) := by simp [three_nsmul_T]
            _ = 3 • (-T) := by
              rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul,
                two_nsmul, one_nsmul]
              abel
      · rw [phiPoint_some_of_tateU_ne_zero h hu]
        have hdual := dualX_phiXi_ne_zero h hu
        rw [phihatPoint_some]
        let Y : L := completedY x y
        have hcurve : Y ^ 2 = completedCubic x := completed_curve_equation h
        by_cases hY : Y = 0
        · have hcompX := two_torsion_composition_x hu hdual hY hcurve
          have hcompY := two_torsion_composition_completedY hu hdual hY
          have hyfrom : fromCompletedY x Y = y := by
            exact fromCompletedY_completedY x y
          have hphiY : phiEta x y = phiEta x (fromCompletedY x Y) := by
            rw [hyfrom]
          rw [← hphiY] at hcompY
          have hneg : y = WeierstrassCurve.Affine.negY E0 x y := by
            rw [E0_negY]
            unfold Y completedY at hY
            field_simp
            linear_combination hY
          rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
            two_nsmul, WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hneg]
          refine Eq.trans ?_
            (zero_add
              (WeierstrassCurve.Affine.Point.some x y h : E0Point)).symm
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          refine ⟨hcompX, ?_⟩
          rw [hcompX] at hcompY
          unfold fromCompletedY at hyfrom
          linear_combination
            (1 / 2 : L) * hcompY + hyfrom - (1 / 2 : L) * hY
        · have hxx := completedDoubleX_ne_self h hu hY
          have hcompX := generic_composition_x hu hY hdual hxx hcurve
          have hcompY :=
            generic_composition_completedY hu hY hdual hxx hcurve
          have hyfrom : fromCompletedY x Y = y :=
            fromCompletedY_completedY x y
          rw [hyfrom] at hcompY
          rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
            two_nsmul]
          have hneg : y ≠ WeierstrassCurve.Affine.negY E0 x y := by
            rw [E0_negY]
            intro heq
            apply hY
            unfold Y completedY
            linear_combination heq
          rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
          rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by
            rw [E0_slope_self hY, E0_addX_tangent]
            exact hxx)]
          change WeierstrassCurve.Affine.Point.some
              (phihatX0 (phiXi x))
              (phihatY0 (phiXi x) (phiEta x y)) _ = _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor
          · rw [E0_slope_self hY, E0_addX_tangent, E0_addY_tangent,
              E0_slope_double_original hxx, E0_addX_double]
            exact hcompX
          · rw [E0_slope_self hY, E0_addX_tangent, E0_addY_tangent,
              E0_slope_double_original hxx, E0_addY_double]
            unfold fromCompletedY
            rw [← hcompX]
            linear_combination (1 / 2 : L) * hcompY

end

end MazurProof.N18RouteC.Composition
