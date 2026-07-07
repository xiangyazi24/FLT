import FLT.Assumptions.MazurProof.RealTopologyS8
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Real topology route, S9: branch-defect global glue

This file packages the branch defect as functions on the open ray `Set.Ioi e`.
The finite-bad-set and asymptotic arguments will use these wrappers rather than
threading proof-irrelevance terms through every statement.
-/

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

/-- Upper-branch theta defect as a function on the open ray `x > e`. -/
def upperThetaDefectOnIoi
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    Set.Ioi e → AddCircle (thetaPeriod A B e) :=
  fun x =>
    thetaDefect (A := A) (B := B) (e := e)
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x.1 x.2) Q

/-- Lower-branch theta defect as a function on the open ray `x > e`. -/
def lowerThetaDefectOnIoi
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    Set.Ioi e → AddCircle (thetaPeriod A B e) :=
  fun x =>
    thetaDefect (A := A) (B := B) (e := e)
      (lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x.1 x.2) Q

/-- Total upper-branch theta defect wrapper for `atTop` statements. -/
def upperThetaDefectAtX
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (x : ℝ) : AddCircle (thetaPeriod A B e) :=
  if hx : e < x then
    thetaDefect (A := A) (B := B) (e := e)
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q
  else
    0

/-- Total lower-branch theta defect wrapper for `atTop` statements. -/
def lowerThetaDefectAtX
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (x : ℝ) : AddCircle (thetaPeriod A B e) :=
  if hx : e < x then
    thetaDefect (A := A) (B := B) (e := e)
      (lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx) Q
  else
    0

theorem upperThetaDefectOnIoi_eq_of_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (upperThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (x y : Set.Ioi e) :
    upperThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x =
      upperThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q y := by
  haveI : PreconnectedSpace (Set.Ioi e) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  exact hloc.apply_eq_of_preconnectedSpace x y

theorem lowerThetaDefectOnIoi_eq_of_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (x y : Set.Ioi e) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x =
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q y := by
  haveI : PreconnectedSpace (Set.Ioi e) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  exact hloc.apply_eq_of_preconnectedSpace x y

theorem tendsto_upperThetaDefectAtX_atTop_const_of_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (upperThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (x₀ : Set.Ioi e) :
    Tendsto
      (upperThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q)
      atTop
      (𝓝 (upperThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x₀)) := by
  have heq :
      upperThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q =ᶠ[atTop]
        fun _ : ℝ =>
          upperThetaDefectOnIoi (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight Q x₀ := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hconst := upperThetaDefectOnIoi_eq_of_isLocallyConstant
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      (hposRight := hposRight) (Q := Q) hloc ⟨x, hx⟩ x₀
    simpa [upperThetaDefectAtX, upperThetaDefectOnIoi, hx] using hconst
  exact Tendsto.congr' heq.symm tendsto_const_nhds

theorem tendsto_lowerThetaDefectAtX_atTop_const_of_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (x₀ : Set.Ioi e) :
    Tendsto
      (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q)
      atTop
      (𝓝 (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x₀)) := by
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q =ᶠ[atTop]
        fun _ : ℝ =>
          lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight Q x₀ := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hconst := lowerThetaDefectOnIoi_eq_of_isLocallyConstant
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      (hposRight := hposRight) (Q := Q) hloc ⟨x, hx⟩ x₀
    simpa [lowerThetaDefectAtX, lowerThetaDefectOnIoi, hx] using hconst
  exact Tendsto.congr' heq.symm tendsto_const_nhds

theorem upperThetaDefectOnIoi_eq_zero_of_isLocallyConstant_of_tendsto_atTop_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (upperThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (hlim : Tendsto
      (upperThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q)
      atTop (𝓝 0)) :
    ∀ x : Set.Ioi e,
      upperThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x = 0 := by
  intro x
  exact tendsto_nhds_unique
    (tendsto_upperThetaDefectAtX_atTop_const_of_isLocallyConstant
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      (hposRight := hposRight) (Q := Q) hloc x)
    hlim

theorem lowerThetaDefectOnIoi_eq_zero_of_isLocallyConstant_of_tendsto_atTop_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv}
    (hloc : IsLocallyConstant (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q))
    (hlim : Tendsto
      (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q)
      atTop (𝓝 0)) :
    ∀ x : Set.Ioi e,
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q x = 0 := by
  intro x
  exact tendsto_nhds_unique
    (tendsto_lowerThetaDefectAtX_atTop_const_of_isLocallyConstant
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      (hposRight := hposRight) (Q := Q) hloc x)
    hlim

end

end MazurProof.RealTopology
