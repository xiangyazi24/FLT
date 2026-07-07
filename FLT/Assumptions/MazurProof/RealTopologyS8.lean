import FLT.Assumptions.MazurProof.RealTopologyS6
import FLT.Assumptions.MazurProof.RealTopologyS7

/-!
# Real topology route, S8: local defect derivatives

This file starts the local additivity step for the theta candidate.  S7 proves
that the post-addition theta lift has derivative `1 / y` on a smooth signed
branch.  Here we record the matching input-branch derivatives and the resulting
zero derivative for the real-valued local defect lift.
-/

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology

namespace MazurProof.RealTopology

noncomputable section

theorem sqrt_shortCubic_eq_y_of_y_pos
    {A B x y : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hypos : 0 < y) :
    √(shortCubic A B x) = y := by
  rcases y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic hy with h | h
  · exact h.symm
  · exfalso
    have hsqrt_nonneg : 0 ≤ √(shortCubic A B x) := sqrt_nonneg _
    have hynonpos : y ≤ 0 := by
      rw [h]
      exact neg_nonpos.mpr hsqrt_nonneg
    linarith

theorem sqrt_shortCubic_eq_neg_y_of_y_neg
    {A B x y : ℝ}
    (hy : y ^ 2 = shortCubic A B x)
    (hyneg : y < 0) :
    √(shortCubic A B x) = -y := by
  rcases y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic hy with h | h
  · have hynonneg : 0 ≤ y := by
      rw [h]
      exact sqrt_nonneg _
    linarith
  · rw [h]
    ring

theorem hasDerivAt_neg_sigma_of_y_pos
    {A B e x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (hy : y ^ 2 = shortCubic A B x)
    (hypos : 0 < y) :
    HasDerivAt (fun t : ℝ => -sigma A B t) (1 / y) x := by
  have hsqrt : √(shortCubic A B x) = y :=
    sqrt_shortCubic_eq_y_of_y_pos (A := A) (B := B) (x := x) (y := y) hy hypos
  have hderiv_eq : rightIntegrand A B x = 1 / y := by
    unfold rightIntegrand
    rw [hsqrt]
    field_simp [hypos.ne']
  exact (neg_sigma_hasDerivAt_of_right hroot hderiv hposRight hx).congr_deriv hderiv_eq

theorem hasDerivAt_sigma_of_y_neg
    {A B e x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (hy : y ^ 2 = shortCubic A B x)
    (hyneg : y < 0) :
    HasDerivAt (sigma A B) (1 / y) x := by
  have hsqrt : √(shortCubic A B x) = -y :=
    sqrt_shortCubic_eq_neg_y_of_y_neg (A := A) (B := B) (x := x) (y := y) hy hyneg
  have hy0 : y ≠ 0 := ne_of_lt hyneg
  have hderiv_eq : -(rightIntegrand A B x) = 1 / y := by
    unfold rightIntegrand
    rw [hsqrt]
    field_simp [hy0]
  exact (sigma_hasDerivAt_of_right hroot hderiv hposRight hx).congr_deriv hderiv_eq

theorem hasDerivAt_neg_sqrt_shortCubic_of_pos
    {A B x : ℝ}
    (hxpos : 0 < shortCubic A B x) :
    HasDerivAt (fun t : ℝ => -√(shortCubic A B t))
      (shortCubicDeriv A B x / (2 * (-√(shortCubic A B x)))) x := by
  have hsqrt0 : √(shortCubic A B x) ≠ 0 :=
    (sqrt_pos.mpr hxpos).ne'
  have hderiv_eq :
      -(shortCubicDeriv A B x / (2 * √(shortCubic A B x))) =
        shortCubicDeriv A B x / (2 * (-√(shortCubic A B x))) := by
    field_simp [hsqrt0]
  exact (sqrt_shortCubic_hasDerivAt_of_pos hxpos).neg.congr_deriv hderiv_eq

theorem shortW_point_add_eq_chord
    {A B x y a b : ℝ}
    {hP : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    {hR : WeierstrassCurve.Affine.Nonsingular
        (shortW A B) (chordX A x y a b) (chordY A x y a b)}
    (hD : x - a ≠ 0) :
    WeierstrassCurve.Affine.Point.some x y hP +
        WeierstrassCurve.Affine.Point.some a b hQ =
      WeierstrassCurve.Affine.Point.some
        (chordX A x y a b) (chordY A x y a b) hR := by
  have hxy :
      ¬(x = a ∧ y = WeierstrassCurve.Affine.negY (shortW A B) a b) := by
    intro h
    exact hD (sub_eq_zero.mpr h.1)
  rw [WeierstrassCurve.Affine.Point.add_some (W := shortW A B) hxy]
  exact point_some_ext
    (A := A) (B := B)
    (shortW_addX_eq_chordX (A := A) (B := B) (x := x) (y := y)
      (a := a) (b := b) hD)
    (shortW_addY_eq_chordY (A := A) (B := B) (x := x) (y := y)
      (a := a) (b := b) hD)

theorem upperRightPoint_add_eq_upperRightPoint_of_chordY_pos
    {A B e x a b : ℝ}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (√(shortCubic A B x)) a b) :
    upperRightPoint (A := A) (B := B) (e := e) hposRight x hx +
        WeierstrassCurve.Affine.Point.some a b hQ =
      upperRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (√(shortCubic A B x)) a b) hx3 := by
  let y := √(shortCubic A B x)
  let x3 := chordX A x y a b
  let y3 := chordY A x y a b
  have hy : y ^ 2 = shortCubic A B x := sq_sqrt (hposRight hx).le
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hcurve3 : y3 ^ 2 = shortCubic A B x3 := by
    simpa [x3, y3, y] using
      chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD
  have hR : WeierstrassCurve.Affine.Nonsingular (shortW A B) x3 y3 :=
    shortW_nonsingular_of_sq_eq_of_y_ne_zero hcurve3
      (show y3 ≠ 0 from (by simpa [y3, y] using hy3pos.ne'))
  have hsum := shortW_point_add_eq_chord
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
    (hP := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx))
    (hQ := hQ) (hR := hR) hD
  have hsqrt3 : √(shortCubic A B x3) = y3 := by
    simpa [x3, y3, y] using
      sqrt_shortCubic_chordX_eq_chordY_of_chordY_pos
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD hy3pos
  rw [upperRightPoint]
  calc
    WeierstrassCurve.Affine.Point.some x y
          (shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx)) +
        WeierstrassCurve.Affine.Point.some a b hQ
        = WeierstrassCurve.Affine.Point.some x3 y3 hR := hsum
    _ = WeierstrassCurve.Affine.Point.some x3 (√(shortCubic A B x3))
          (shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x3) (hposRight hx3)) :=
        point_some_ext (A := A) (B := B) rfl hsqrt3.symm

theorem upperRightPoint_add_eq_lowerRightPoint_of_chordY_neg
    {A B e x a b : ℝ}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (√(shortCubic A B x)) a b < 0) :
    upperRightPoint (A := A) (B := B) (e := e) hposRight x hx +
        WeierstrassCurve.Affine.Point.some a b hQ =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (√(shortCubic A B x)) a b) hx3 := by
  let y := √(shortCubic A B x)
  let x3 := chordX A x y a b
  let y3 := chordY A x y a b
  have hy : y ^ 2 = shortCubic A B x := sq_sqrt (hposRight hx).le
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hcurve3 : y3 ^ 2 = shortCubic A B x3 := by
    simpa [x3, y3, y] using
      chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD
  have hR : WeierstrassCurve.Affine.Nonsingular (shortW A B) x3 y3 :=
    shortW_nonsingular_of_sq_eq_of_y_ne_zero hcurve3
      (show y3 ≠ 0 from (by simpa [y3, y] using hy3neg.ne))
  have hsum := shortW_point_add_eq_chord
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
    (hP := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx))
    (hQ := hQ) (hR := hR) hD
  have hsqrt3 : √(shortCubic A B x3) = -y3 := by
    simpa [x3, y3, y] using
      sqrt_shortCubic_chordX_eq_neg_chordY_of_chordY_neg
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD hy3neg
  rw [upperRightPoint, lowerRightPoint]
  calc
    WeierstrassCurve.Affine.Point.some x y
          (shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx)) +
        WeierstrassCurve.Affine.Point.some a b hQ
        = WeierstrassCurve.Affine.Point.some x3 y3 hR := hsum
    _ = WeierstrassCurve.Affine.Point.some x3 (-√(shortCubic A B x3))
          (shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := x3) (hposRight hx3)) :=
        point_some_ext (A := A) (B := B) rfl (by linarith)

theorem lowerRightPoint_add_eq_upperRightPoint_of_chordY_pos
    {A B e x a b : ℝ}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (-√(shortCubic A B x)) a b) :
    lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx +
        WeierstrassCurve.Affine.Point.some a b hQ =
      upperRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (-√(shortCubic A B x)) a b) hx3 := by
  let y := -√(shortCubic A B x)
  let x3 := chordX A x y a b
  let y3 := chordY A x y a b
  have hy : y ^ 2 = shortCubic A B x := by
    rw [neg_sq]
    exact sq_sqrt (hposRight hx).le
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hcurve3 : y3 ^ 2 = shortCubic A B x3 := by
    simpa [x3, y3, y] using
      chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD
  have hR : WeierstrassCurve.Affine.Nonsingular (shortW A B) x3 y3 :=
    shortW_nonsingular_of_sq_eq_of_y_ne_zero hcurve3
      (show y3 ≠ 0 from (by simpa [y3, y] using hy3pos.ne'))
  have hsum := shortW_point_add_eq_chord
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
    (hP := shortW_nonsingular_neg_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    (hQ := hQ) (hR := hR) hD
  have hsqrt3 : √(shortCubic A B x3) = y3 := by
    simpa [x3, y3, y] using
      sqrt_shortCubic_chordX_eq_chordY_of_chordY_pos
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD hy3pos
  rw [lowerRightPoint, upperRightPoint]
  calc
    WeierstrassCurve.Affine.Point.some x y
          (shortW_nonsingular_neg_sqrt_of_pos
            (A := A) (B := B) (x := x) (hposRight hx)) +
        WeierstrassCurve.Affine.Point.some a b hQ
        = WeierstrassCurve.Affine.Point.some x3 y3 hR := hsum
    _ = WeierstrassCurve.Affine.Point.some x3 (√(shortCubic A B x3))
          (shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x3) (hposRight hx3)) :=
        point_some_ext (A := A) (B := B) rfl hsqrt3.symm

theorem lowerRightPoint_add_eq_lowerRightPoint_of_chordY_neg
    {A B e x a b : ℝ}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (-√(shortCubic A B x)) a b < 0) :
    lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx +
        WeierstrassCurve.Affine.Point.some a b hQ =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (-√(shortCubic A B x)) a b) hx3 := by
  let y := -√(shortCubic A B x)
  let x3 := chordX A x y a b
  let y3 := chordY A x y a b
  have hy : y ^ 2 = shortCubic A B x := by
    rw [neg_sq]
    exact sq_sqrt (hposRight hx).le
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hcurve3 : y3 ^ 2 = shortCubic A B x3 := by
    simpa [x3, y3, y] using
      chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD
  have hR : WeierstrassCurve.Affine.Nonsingular (shortW A B) x3 y3 :=
    shortW_nonsingular_of_sq_eq_of_y_ne_zero hcurve3
      (show y3 ≠ 0 from (by simpa [y3, y] using hy3neg.ne))
  have hsum := shortW_point_add_eq_chord
    (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
    (hP := shortW_nonsingular_neg_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    (hQ := hQ) (hR := hR) hD
  have hsqrt3 : √(shortCubic A B x3) = -y3 := by
    simpa [x3, y3, y] using
      sqrt_shortCubic_chordX_eq_neg_chordY_of_chordY_neg
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hQcurve hD hy3neg
  rw [lowerRightPoint]
  calc
    WeierstrassCurve.Affine.Point.some x y
          (shortW_nonsingular_neg_sqrt_of_pos
            (A := A) (B := B) (x := x) (hposRight hx)) +
        WeierstrassCurve.Affine.Point.some a b hQ
        = WeierstrassCurve.Affine.Point.some x3 y3 hR := hsum
    _ = WeierstrassCurve.Affine.Point.some x3 (-√(shortCubic A B x3))
          (shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := x3) (hposRight hx3)) :=
        point_some_ext (A := A) (B := B) rfl (by linarith)

theorem thetaCandidate_upperRight_add_some_of_chordY_pos
    {A B e x a b : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (√(shortCubic A B x)) a b) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q) =
      ((-sigma A B (chordX A x (√(shortCubic A B x)) a b) : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  have hker :
      upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q =
        upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (chordX A x (√(shortCubic A B x)) a b) hx3 := by
    apply Subtype.ext
    change upperRightPoint (A := A) (B := B) (e := e) hposRight x hx + Q.1 =
      upperRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (√(shortCubic A B x)) a b) hx3
    rw [hQeq]
    exact upperRightPoint_add_eq_upperRightPoint_of_chordY_pos
      (A := A) (B := B) (e := e) hposRight hx hD hx3 hy3pos
  rw [hker]
  exact thetaCandidate_upperRightKerPoint
    (A := A) (B := B) (e := e) hposRight hx3

theorem thetaCandidate_upperRight_add_some_of_chordY_neg
    {A B e x a b : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (√(shortCubic A B x)) a b < 0) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q) =
      ((sigma A B (chordX A x (√(shortCubic A B x)) a b) : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  have hker :
      upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q =
        lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (chordX A x (√(shortCubic A B x)) a b) hx3 := by
    apply Subtype.ext
    change upperRightPoint (A := A) (B := B) (e := e) hposRight x hx + Q.1 =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (√(shortCubic A B x)) a b) hx3
    rw [hQeq]
    exact upperRightPoint_add_eq_lowerRightPoint_of_chordY_neg
      (A := A) (B := B) (e := e) hposRight hx hD hx3 hy3neg
  rw [hker]
  exact thetaCandidate_lowerRightKerPoint
    (A := A) (B := B) (e := e) hposRight hx3

theorem thetaCandidate_lowerRight_add_some_of_chordY_pos
    {A B e x a b : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (-√(shortCubic A B x)) a b) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q) =
      ((-sigma A B (chordX A x (-√(shortCubic A B x)) a b) : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  have hker :
      lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q =
        upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (chordX A x (-√(shortCubic A B x)) a b) hx3 := by
    apply Subtype.ext
    change lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx + Q.1 =
      upperRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (-√(shortCubic A B x)) a b) hx3
    rw [hQeq]
    exact lowerRightPoint_add_eq_upperRightPoint_of_chordY_pos
      (A := A) (B := B) (e := e) hposRight hx hD hx3 hy3pos
  rw [hker]
  exact thetaCandidate_upperRightKerPoint
    (A := A) (B := B) (e := e) hposRight hx3

theorem thetaCandidate_lowerRight_add_some_of_chordY_neg
    {A B e x a b : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (-√(shortCubic A B x)) a b < 0) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q) =
      ((sigma A B (chordX A x (-√(shortCubic A B x)) a b) : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  have hker :
      lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx + Q =
        lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (chordX A x (-√(shortCubic A B x)) a b) hx3 := by
    apply Subtype.ext
    change lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx + Q.1 =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight
        (chordX A x (-√(shortCubic A B x)) a b) hx3
    rw [hQeq]
    exact lowerRightPoint_add_eq_lowerRightPoint_of_chordY_neg
      (A := A) (B := B) (e := e) hposRight hx hD hx3 hy3neg
  rw [hker]
  exact thetaCandidate_lowerRightKerPoint
    (A := A) (B := B) (e := e) hposRight hx3

theorem thetaDefect_upperRight_some_of_chordY_pos
    {A B e x a b qtheta : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (√(shortCubic A B x)) a b) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q =
      ((-sigma A B (chordX A x (√(shortCubic A B x)) a b) -
          (-sigma A B x) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) := by
  rw [thetaDefect]
  rw [thetaCandidate_upperRight_add_some_of_chordY_pos
    (A := A) (B := B) (e := e) hposRight Q hQeq hx hD hx3 hy3pos]
  rw [thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight hx]
  rw [hQtheta]
  rfl

theorem thetaDefect_upperRight_some_of_chordY_neg
    {A B e x a b qtheta : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (√(shortCubic A B x)) a b < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q =
      ((sigma A B (chordX A x (√(shortCubic A B x)) a b) -
          (-sigma A B x) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) := by
  rw [thetaDefect]
  rw [thetaCandidate_upperRight_add_some_of_chordY_neg
    (A := A) (B := B) (e := e) hposRight Q hQeq hx hD hx3 hy3neg]
  rw [thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight hx]
  rw [hQtheta]
  rfl

theorem thetaDefect_lowerRight_some_of_chordY_pos
    {A B e x a b qtheta : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3pos : 0 < chordY A x (-√(shortCubic A B x)) a b) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q =
      ((-sigma A B (chordX A x (-√(shortCubic A B x)) a b) -
          sigma A B x - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) := by
  rw [thetaDefect]
  rw [thetaCandidate_lowerRight_add_some_of_chordY_pos
    (A := A) (B := B) (e := e) hposRight Q hQeq hx hD hx3 hy3pos]
  rw [thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight hx]
  rw [hQtheta]
  rfl

theorem thetaDefect_lowerRight_some_of_chordY_neg
    {A B e x a b qtheta : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hx : e < x)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a b)
    (hy3neg : chordY A x (-√(shortCubic A B x)) a b < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q =
      ((sigma A B (chordX A x (-√(shortCubic A B x)) a b) -
          sigma A B x - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) := by
  rw [thetaDefect]
  rw [thetaCandidate_lowerRight_add_some_of_chordY_neg
    (A := A) (B := B) (e := e) hposRight Q hQeq hx hD hx3 hy3neg]
  rw [thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight hx]
  rw [hQtheta]
  rfl

theorem thetaDefect_upperRight_upperRight_of_chordY_pos
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a (√(shortCubic A B a)))
    (hy3pos : 0 < chordY A x (√(shortCubic A B x)) a (√(shortCubic A B a))) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((-sigma A B (chordX A x (√(shortCubic A B x)) a (√(shortCubic A B a))) -
          (-sigma A B x) - (-sigma A B a) : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_upperRight_some_of_chordY_pos
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := √(shortCubic A B a)) (qtheta := -sigma A B a)
    hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3pos

theorem thetaDefect_upperRight_upperRight_of_chordY_neg
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a (√(shortCubic A B a)))
    (hy3neg : chordY A x (√(shortCubic A B x)) a (√(shortCubic A B a)) < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((sigma A B (chordX A x (√(shortCubic A B x)) a (√(shortCubic A B a))) -
          (-sigma A B x) - (-sigma A B a) : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_upperRight_some_of_chordY_neg
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := √(shortCubic A B a)) (qtheta := -sigma A B a)
    hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3neg

theorem thetaDefect_upperRight_lowerRight_of_chordY_pos
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a (-√(shortCubic A B a)))
    (hy3pos : 0 < chordY A x (√(shortCubic A B x)) a (-√(shortCubic A B a))) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((-sigma A B (chordX A x (√(shortCubic A B x)) a (-√(shortCubic A B a))) -
          (-sigma A B x) - sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_upperRight_some_of_chordY_pos
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := -√(shortCubic A B a)) (qtheta := sigma A B a)
    hposRight
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3pos

theorem thetaDefect_upperRight_lowerRight_of_chordY_neg
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (√(shortCubic A B x)) a (-√(shortCubic A B a)))
    (hy3neg : chordY A x (√(shortCubic A B x)) a (-√(shortCubic A B a)) < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((sigma A B (chordX A x (√(shortCubic A B x)) a (-√(shortCubic A B a))) -
          (-sigma A B x) - sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_upperRight_some_of_chordY_neg
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := -√(shortCubic A B a)) (qtheta := sigma A B a)
    hposRight
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3neg

theorem thetaDefect_lowerRight_upperRight_of_chordY_pos
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a)))
    (hy3pos : 0 < chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a))) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((-sigma A B (chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a))) -
          sigma A B x - (-sigma A B a) : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_lowerRight_some_of_chordY_pos
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := √(shortCubic A B a)) (qtheta := -sigma A B a)
    hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3pos

theorem thetaDefect_lowerRight_upperRight_of_chordY_neg
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a)))
    (hy3neg : chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((sigma A B (chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a))) -
          sigma A B x - (-sigma A B a) : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_lowerRight_some_of_chordY_neg
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := √(shortCubic A B a)) (qtheta := -sigma A B a)
    hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3neg

theorem thetaDefect_lowerRight_lowerRight_of_chordY_pos
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a (-√(shortCubic A B a)))
    (hy3pos : 0 < chordY A x (-√(shortCubic A B x)) a (-√(shortCubic A B a))) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((-sigma A B (chordX A x (-√(shortCubic A B x)) a (-√(shortCubic A B a))) -
          sigma A B x - sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_lowerRight_some_of_chordY_pos
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := -√(shortCubic A B a)) (qtheta := sigma A B a)
    hposRight
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3pos

theorem thetaDefect_lowerRight_lowerRight_of_chordY_neg
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hx3 : e < chordX A x (-√(shortCubic A B x)) a (-√(shortCubic A B a)))
    (hy3neg : chordY A x (-√(shortCubic A B x)) a (-√(shortCubic A B a)) < 0) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      ((sigma A B (chordX A x (-√(shortCubic A B x)) a (-√(shortCubic A B a))) -
          sigma A B x - sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)) := by
  exact thetaDefect_lowerRight_some_of_chordY_neg
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (b := -√(shortCubic A B a)) (qtheta := sigma A B a)
    hposRight
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_lowerRightKerPoint (A := A) (B := B) (e := e) hposRight ha)
    hx hD hx3 hy3neg

theorem hasDerivAt_real_theta_defect_lift_zero
    {F G : ℝ → ℝ} {x y c : ℝ}
    (hF : HasDerivAt F (1 / y) x)
    (hG : HasDerivAt G (1 / y) x) :
    HasDerivAt (fun t : ℝ => F t - G t - c) 0 x := by
  simpa using (hF.sub hG).sub_const c

theorem hasDerivAt_thetaDefectLift_upper_upper
    {u : ℝ → ℝ} {A B e a b x y c : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hypos : 0 < y)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3pos : 0 < chordY A x y a b) :
    HasDerivAt
      (fun t : ℝ =>
        -sigma A B (chordX A t (u t) a b) - (-sigma A B t) - c)
      0 x := by
  have hpost := hasDerivAt_neg_sigma_comp_chordX_signed_of_chordY_pos
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hypos.ne' hD huval hu hx3 hy3pos
  have hinput := hasDerivAt_neg_sigma_of_y_pos
    (A := A) (B := B) (e := e) (x := x) (y := y)
    hroot hderiv hposRight hx hy hypos
  exact hasDerivAt_real_theta_defect_lift_zero (c := c) hpost hinput

theorem hasDerivAt_thetaDefectLift_upper_lower
    {u : ℝ → ℝ} {A B e a b x y c : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hypos : 0 < y)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3neg : chordY A x y a b < 0) :
    HasDerivAt
      (fun t : ℝ =>
        sigma A B (chordX A t (u t) a b) - (-sigma A B t) - c)
      0 x := by
  have hpost := hasDerivAt_sigma_comp_chordX_signed_of_chordY_neg
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hypos.ne' hD huval hu hx3 hy3neg
  have hinput := hasDerivAt_neg_sigma_of_y_pos
    (A := A) (B := B) (e := e) (x := x) (y := y)
    hroot hderiv hposRight hx hy hypos
  exact hasDerivAt_real_theta_defect_lift_zero (c := c) hpost hinput

theorem hasDerivAt_thetaDefectLift_lower_upper
    {u : ℝ → ℝ} {A B e a b x y c : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hyneg : y < 0)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3pos : 0 < chordY A x y a b) :
    HasDerivAt
      (fun t : ℝ =>
        -sigma A B (chordX A t (u t) a b) - sigma A B t - c)
      0 x := by
  have hy0 : y ≠ 0 := ne_of_lt hyneg
  have hpost := hasDerivAt_neg_sigma_comp_chordX_signed_of_chordY_pos
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hy0 hD huval hu hx3 hy3pos
  have hinput := hasDerivAt_sigma_of_y_neg
    (A := A) (B := B) (e := e) (x := x) (y := y)
    hroot hderiv hposRight hx hy hyneg
  exact hasDerivAt_real_theta_defect_lift_zero (c := c) hpost hinput

theorem hasDerivAt_thetaDefectLift_lower_lower
    {u : ℝ → ℝ} {A B e a b x y c : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hy : y ^ 2 = shortCubic A B x)
    (hyneg : y < 0)
    (hx : e < x)
    (hD : x - a ≠ 0)
    (huval : u x = y)
    (hu : HasDerivAt u (shortCubicDeriv A B x / (2 * y)) x)
    (hx3 : e < chordX A x y a b)
    (hy3neg : chordY A x y a b < 0) :
    HasDerivAt
      (fun t : ℝ =>
        sigma A B (chordX A t (u t) a b) - sigma A B t - c)
      0 x := by
  have hy0 : y ≠ 0 := ne_of_lt hyneg
  have hpost := hasDerivAt_sigma_comp_chordX_signed_of_chordY_neg
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := x) (y := y)
    hroot hderiv hposRight hQ hy hy0 hD huval hu hx3 hy3neg
  have hinput := hasDerivAt_sigma_of_y_neg
    (A := A) (B := B) (e := e) (x := x) (y := y)
    hroot hderiv hposRight hx hy hyneg
  exact hasDerivAt_real_theta_defect_lift_zero (c := c) hpost hinput

theorem eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected
    {s : Set ℝ} {f : ℝ → ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hf : ∀ x ∈ s, HasDerivAt f 0 x)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y := by
  have hdiff : DifferentiableOn ℝ f s := by
    intro z hz
    exact (hf z hz).differentiableAt.differentiableWithinAt
  have hderiv : s.EqOn (deriv f) (fun _ : ℝ => 0) := by
    intro z hz
    simpa using (hf z hz).deriv
  exact hsopen.is_const_of_deriv_eq_zero hspre hdiff hderiv hx hy

theorem thetaDefectLift_upper_upper_const_on
    {u : ℝ → ℝ} {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hcurve : ∀ z ∈ s, (u z) ^ 2 = shortCubic A B z)
    (hupos : ∀ z ∈ s, 0 < u z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hu : ∀ z ∈ s, HasDerivAt u (shortCubicDeriv A B z / (2 * u z)) z)
    (hx3 : ∀ z ∈ s, e < chordX A z (u z) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (u z) a b)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    -sigma A B (chordX A x (u x) a b) - (-sigma A B x) - c =
      -sigma A B (chordX A y (u y) a b) - (-sigma A B y) - c := by
  apply eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected hsopen hspre ?_ hx hy
  intro z hz
  exact hasDerivAt_thetaDefectLift_upper_upper
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := z) (y := u z)
    (u := u) (c := c) hroot hderiv hposRight hQ (hcurve z hz)
    (hupos z hz) (hxright z hz) (hD z hz) rfl (hu z hz) (hx3 z hz)
    (hy3pos z hz)

theorem thetaDefectLift_upper_lower_const_on
    {u : ℝ → ℝ} {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hcurve : ∀ z ∈ s, (u z) ^ 2 = shortCubic A B z)
    (hupos : ∀ z ∈ s, 0 < u z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hu : ∀ z ∈ s, HasDerivAt u (shortCubicDeriv A B z / (2 * u z)) z)
    (hx3 : ∀ z ∈ s, e < chordX A z (u z) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (u z) a b < 0)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    sigma A B (chordX A x (u x) a b) - (-sigma A B x) - c =
      sigma A B (chordX A y (u y) a b) - (-sigma A B y) - c := by
  apply eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected hsopen hspre ?_ hx hy
  intro z hz
  exact hasDerivAt_thetaDefectLift_upper_lower
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := z) (y := u z)
    (u := u) (c := c) hroot hderiv hposRight hQ (hcurve z hz)
    (hupos z hz) (hxright z hz) (hD z hz) rfl (hu z hz) (hx3 z hz)
    (hy3neg z hz)

theorem thetaDefectLift_lower_upper_const_on
    {u : ℝ → ℝ} {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hcurve : ∀ z ∈ s, (u z) ^ 2 = shortCubic A B z)
    (huneg : ∀ z ∈ s, u z < 0)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hu : ∀ z ∈ s, HasDerivAt u (shortCubicDeriv A B z / (2 * u z)) z)
    (hx3 : ∀ z ∈ s, e < chordX A z (u z) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (u z) a b)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    -sigma A B (chordX A x (u x) a b) - sigma A B x - c =
      -sigma A B (chordX A y (u y) a b) - sigma A B y - c := by
  apply eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected hsopen hspre ?_ hx hy
  intro z hz
  exact hasDerivAt_thetaDefectLift_lower_upper
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := z) (y := u z)
    (u := u) (c := c) hroot hderiv hposRight hQ (hcurve z hz)
    (huneg z hz) (hxright z hz) (hD z hz) rfl (hu z hz) (hx3 z hz)
    (hy3pos z hz)

theorem thetaDefectLift_lower_lower_const_on
    {u : ℝ → ℝ} {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hcurve : ∀ z ∈ s, (u z) ^ 2 = shortCubic A B z)
    (huneg : ∀ z ∈ s, u z < 0)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hu : ∀ z ∈ s, HasDerivAt u (shortCubicDeriv A B z / (2 * u z)) z)
    (hx3 : ∀ z ∈ s, e < chordX A z (u z) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (u z) a b < 0)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    sigma A B (chordX A x (u x) a b) - sigma A B x - c =
      sigma A B (chordX A y (u y) a b) - sigma A B y - c := by
  apply eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected hsopen hspre ?_ hx hy
  intro z hz
  exact hasDerivAt_thetaDefectLift_lower_lower
    (A := A) (B := B) (e := e) (a := a) (b := b) (x := z) (y := u z)
    (u := u) (c := c) hroot hderiv hposRight hQ (hcurve z hz)
    (huneg z hz) (hxright z hz) (hD z hz) rfl (hu z hz) (hx3 z hz)
    (hy3neg z hz)

theorem thetaDefectLift_upperSqrt_upper_const_on
    {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hpos : ∀ z ∈ s, 0 < shortCubic A B z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (√(shortCubic A B z)) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (√(shortCubic A B z)) a b)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    -sigma A B (chordX A x (√(shortCubic A B x)) a b) - (-sigma A B x) - c =
      -sigma A B (chordX A y (√(shortCubic A B y)) a b) - (-sigma A B y) - c := by
  exact thetaDefectLift_upper_upper_const_on
    (u := fun z : ℝ => √(shortCubic A B z)) (A := A) (B := B) (e := e)
    (a := a) (b := b) (c := c) (s := s) hsopen hspre hroot hderiv hposRight hQ
    (fun z hz => sq_sqrt (hpos z hz).le)
    (fun z hz => sqrt_pos.mpr (hpos z hz))
    hxright hD
    (fun z hz => sqrt_shortCubic_hasDerivAt_of_pos (hpos z hz))
    hx3 hy3pos hx hy

theorem thetaDefectLift_upperSqrt_lower_const_on
    {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hpos : ∀ z ∈ s, 0 < shortCubic A B z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (√(shortCubic A B z)) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (√(shortCubic A B z)) a b < 0)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    sigma A B (chordX A x (√(shortCubic A B x)) a b) - (-sigma A B x) - c =
      sigma A B (chordX A y (√(shortCubic A B y)) a b) - (-sigma A B y) - c := by
  exact thetaDefectLift_upper_lower_const_on
    (u := fun z : ℝ => √(shortCubic A B z)) (A := A) (B := B) (e := e)
    (a := a) (b := b) (c := c) (s := s) hsopen hspre hroot hderiv hposRight hQ
    (fun z hz => sq_sqrt (hpos z hz).le)
    (fun z hz => sqrt_pos.mpr (hpos z hz))
    hxright hD
    (fun z hz => sqrt_shortCubic_hasDerivAt_of_pos (hpos z hz))
    hx3 hy3neg hx hy

theorem thetaDefectLift_lowerSqrt_upper_const_on
    {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hpos : ∀ z ∈ s, 0 < shortCubic A B z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (-√(shortCubic A B z)) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (-√(shortCubic A B z)) a b)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    -sigma A B (chordX A x (-√(shortCubic A B x)) a b) - sigma A B x - c =
      -sigma A B (chordX A y (-√(shortCubic A B y)) a b) - sigma A B y - c := by
  exact thetaDefectLift_lower_upper_const_on
    (u := fun z : ℝ => -√(shortCubic A B z)) (A := A) (B := B) (e := e)
    (a := a) (b := b) (c := c) (s := s) hsopen hspre hroot hderiv hposRight hQ
    (fun z hz => by
      rw [neg_sq]
      exact sq_sqrt (hpos z hz).le)
    (fun z hz => neg_lt_zero.mpr (sqrt_pos.mpr (hpos z hz)))
    hxright hD
    (fun z hz => hasDerivAt_neg_sqrt_shortCubic_of_pos (hpos z hz))
    hx3 hy3pos hx hy

theorem thetaDefectLift_lowerSqrt_lower_const_on
    {A B e a b c : ℝ} {s : Set ℝ}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (hQ : b ^ 2 = shortCubic A B a)
    (hpos : ∀ z ∈ s, 0 < shortCubic A B z)
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (-√(shortCubic A B z)) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (-√(shortCubic A B z)) a b < 0)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    sigma A B (chordX A x (-√(shortCubic A B x)) a b) - sigma A B x - c =
      sigma A B (chordX A y (-√(shortCubic A B y)) a b) - sigma A B y - c := by
  exact thetaDefectLift_lower_lower_const_on
    (u := fun z : ℝ => -√(shortCubic A B z)) (A := A) (B := B) (e := e)
    (a := a) (b := b) (c := c) (s := s) hsopen hspre hroot hderiv hposRight hQ
    (fun z hz => by
      rw [neg_sq]
      exact sq_sqrt (hpos z hz).le)
    (fun z hz => neg_lt_zero.mpr (sqrt_pos.mpr (hpos z hz)))
    hxright hD
    (fun z hz => hasDerivAt_neg_sqrt_shortCubic_of_pos (hpos z hz))
    hx3 hy3neg hx hy

theorem thetaDefect_upperRight_some_const_on_of_chordY_pos
    {A B e a b qtheta : ℝ} {s : Set ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (√(shortCubic A B z)) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (√(shortCubic A B z)) a b)
    {x y : ℝ} (hxs : x ∈ s) (hys : y ∈ s) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q =
      thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q := by
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hlift := thetaDefectLift_upperSqrt_upper_const_on
    (A := A) (B := B) (e := e) (a := a) (b := b) (c := qtheta) (s := s)
    hsopen hspre hroot hderiv hposRight hQcurve
    (fun z hz => hposRight (hxright z hz)) hxright hD hx3 hy3pos hxs hys
  calc
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q
        = ((-sigma A B (chordX A x (√(shortCubic A B x)) a b) -
            (-sigma A B x) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          thetaDefect_upperRight_some_of_chordY_pos
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright x hxs) (hD x hxs) (hx3 x hxs) (hy3pos x hxs)
    _ = ((-sigma A B (chordX A y (√(shortCubic A B y)) a b) -
            (-sigma A B y) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          congrArg (fun t : ℝ => ((t : ℝ) : AddCircle (thetaPeriod A B e))) hlift
    _ = thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q :=
          (thetaDefect_upperRight_some_of_chordY_pos
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright y hys) (hD y hys) (hx3 y hys) (hy3pos y hys)).symm

theorem thetaDefect_upperRight_some_const_on_of_chordY_neg
    {A B e a b qtheta : ℝ} {s : Set ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (√(shortCubic A B z)) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (√(shortCubic A B z)) a b < 0)
    {x y : ℝ} (hxs : x ∈ s) (hys : y ∈ s) :
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q =
      thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q := by
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hlift := thetaDefectLift_upperSqrt_lower_const_on
    (A := A) (B := B) (e := e) (a := a) (b := b) (c := qtheta) (s := s)
    hsopen hspre hroot hderiv hposRight hQcurve
    (fun z hz => hposRight (hxright z hz)) hxright hD hx3 hy3neg hxs hys
  calc
    thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q
        = ((sigma A B (chordX A x (√(shortCubic A B x)) a b) -
            (-sigma A B x) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          thetaDefect_upperRight_some_of_chordY_neg
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright x hxs) (hD x hxs) (hx3 x hxs) (hy3neg x hxs)
    _ = ((sigma A B (chordX A y (√(shortCubic A B y)) a b) -
            (-sigma A B y) - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          congrArg (fun t : ℝ => ((t : ℝ) : AddCircle (thetaPeriod A B e))) hlift
    _ = thetaDefect (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q :=
          (thetaDefect_upperRight_some_of_chordY_neg
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright y hys) (hD y hys) (hx3 y hys) (hy3neg y hys)).symm

theorem thetaDefect_lowerRight_some_const_on_of_chordY_pos
    {A B e a b qtheta : ℝ} {s : Set ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (-√(shortCubic A B z)) a b)
    (hy3pos : ∀ z ∈ s, 0 < chordY A z (-√(shortCubic A B z)) a b)
    {x y : ℝ} (hxs : x ∈ s) (hys : y ∈ s) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q =
      thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q := by
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hlift := thetaDefectLift_lowerSqrt_upper_const_on
    (A := A) (B := B) (e := e) (a := a) (b := b) (c := qtheta) (s := s)
    hsopen hspre hroot hderiv hposRight hQcurve
    (fun z hz => hposRight (hxright z hz)) hxright hD hx3 hy3pos hxs hys
  calc
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q
        = ((-sigma A B (chordX A x (-√(shortCubic A B x)) a b) -
            sigma A B x - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          thetaDefect_lowerRight_some_of_chordY_pos
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright x hxs) (hD x hxs) (hx3 x hxs) (hy3pos x hxs)
    _ = ((-sigma A B (chordX A y (-√(shortCubic A B y)) a b) -
            sigma A B y - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          congrArg (fun t : ℝ => ((t : ℝ) : AddCircle (thetaPeriod A B e))) hlift
    _ = thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q :=
          (thetaDefect_lowerRight_some_of_chordY_pos
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright y hys) (hD y hys) (hx3 y hys) (hy3pos y hys)).symm

theorem thetaDefect_lowerRight_some_const_on_of_chordY_neg
    {A B e a b qtheta : ℝ} {s : Set ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hsopen : IsOpen s)
    (hspre : IsPreconnected s)
    (hposRight : ∀ ⦃v : ℝ⦄, e < v → 0 < shortCubic A B v)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    {hQ : WeierstrassCurve.Affine.Nonsingular (shortW A B) a b}
    (hQeq : Q.1 = WeierstrassCurve.Affine.Point.some a b hQ)
    (hQtheta :
      thetaCandidate (A := A) (B := B) (e := e) Q =
        ((qtheta : ℝ) : AddCircle (thetaPeriod A B e)))
    (hxright : ∀ z ∈ s, e < z)
    (hD : ∀ z ∈ s, z - a ≠ 0)
    (hx3 : ∀ z ∈ s, e < chordX A z (-√(shortCubic A B z)) a b)
    (hy3neg : ∀ z ∈ s, chordY A z (-√(shortCubic A B z)) a b < 0)
    {x y : ℝ} (hxs : x ∈ s) (hys : y ∈ s) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q =
      thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q := by
  have hQcurve : b ^ 2 = shortCubic A B a := shortW_equation_iff.mp hQ.1
  have hlift := thetaDefectLift_lowerSqrt_lower_const_on
    (A := A) (B := B) (e := e) (a := a) (b := b) (c := qtheta) (s := s)
    hsopen hspre hroot hderiv hposRight hQcurve
    (fun z hz => hposRight (hxright z hz)) hxright hD hx3 hy3neg hxs hys
  calc
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x (hxright x hxs)) Q
        = ((sigma A B (chordX A x (-√(shortCubic A B x)) a b) -
            sigma A B x - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          thetaDefect_lowerRight_some_of_chordY_neg
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright x hxs) (hD x hxs) (hx3 x hxs) (hy3neg x hxs)
    _ = ((sigma A B (chordX A y (-√(shortCubic A B y)) a b) -
            sigma A B y - qtheta : ℝ) : AddCircle (thetaPeriod A B e)) :=
          congrArg (fun t : ℝ => ((t : ℝ) : AddCircle (thetaPeriod A B e))) hlift
    _ = thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y (hxright y hys)) Q :=
          (thetaDefect_lowerRight_some_of_chordY_neg
            (A := A) (B := B) (e := e) hposRight Q hQeq hQtheta
            (hxright y hys) (hD y hys) (hx3 y hys) (hy3neg y hys)).symm

end

end MazurProof.RealTopology
