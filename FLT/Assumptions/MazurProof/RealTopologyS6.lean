import FLT.Assumptions.MazurProof.RealTopologyS5

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

/-- The period used by the S5 theta candidate. -/
abbrev thetaPeriod (A B e : ℝ) : ℝ :=
  2 * halfPeriod A B e

theorem shortW_nonsingular_of_sq_eq_of_y_ne_zero
    {A B x y : ℝ}
    (hcurve : y ^ 2 = shortCubic A B x)
    (hy : y ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular (shortW A B) x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · exact shortW_equation_iff.mpr hcurve
  · right
    simpa [shortW] using hy

theorem shortW_nonsingular_sqrt_of_pos
    {A B x : ℝ}
    (hpos : 0 < shortCubic A B x) :
    WeierstrassCurve.Affine.Nonsingular (shortW A B) x
      (√(shortCubic A B x)) := by
  apply shortW_nonsingular_of_sq_eq_of_y_ne_zero
  · exact Real.sq_sqrt hpos.le
  · exact (Real.sqrt_pos.mpr hpos).ne'

theorem shortW_nonsingular_neg_sqrt_of_pos
    {A B x : ℝ}
    (hpos : 0 < shortCubic A B x) :
    WeierstrassCurve.Affine.Nonsingular (shortW A B) x
      (-√(shortCubic A B x)) := by
  apply shortW_nonsingular_of_sq_eq_of_y_ne_zero
  · rw [neg_sq]
    exact Real.sq_sqrt hpos.le
  · exact neg_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'

theorem shortW_nonsingular_root_of_deriv_pos
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    WeierstrassCurve.Affine.Nonsingular (shortW A B) e 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  constructor
  · exact shortW_equation_iff.mpr (by simpa using hroot.symm)
  · left
    intro hzero
    apply hderiv.ne'
    simp [shortW, shortCubicDeriv] at hzero ⊢
    linarith

/-- The branch point `(e,0)` as a point of `shortW`. -/
def rootPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    WeierstrassCurve.Affine.Point (shortW A B) :=
  WeierstrassCurve.Affine.Point.some e 0
    (shortW_nonsingular_root_of_deriv_pos (A := A) (B := B) (e := e) hroot hderiv)

@[simp]
theorem componentBit_rootPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    componentBit (A := A) (B := B) e (rootPoint hroot hderiv) = 0 := by
  simp [rootPoint, componentBit, sideBit]

/-- The branch point `(e,0)` as an element of the component kernel. -/
def rootKerPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
  ⟨rootPoint hroot hderiv, componentBit_rootPoint hroot hderiv⟩

@[simp]
theorem thetaCandidate_rootKerPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      ((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)) := by
  simpa [thetaPeriod, rootKerPoint, rootPoint] using
    thetaCandidate_some_root (A := A) (B := B) (e := e)
      (x := e) (y := 0)
      (P := rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
      rfl rfl

/-- Upper real branch point `(x, +√f(x))` on the right component. -/
def upperRightPoint
    {A B e : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : ℝ) (hx : e < x) :
    WeierstrassCurve.Affine.Point (shortW A B) :=
  WeierstrassCurve.Affine.Point.some x (√(shortCubic A B x))
    (shortW_nonsingular_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx))

/-- Lower real branch point `(x, -√f(x))` on the right component. -/
def lowerRightPoint
    {A B e : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : ℝ) (hx : e < x) :
    WeierstrassCurve.Affine.Point (shortW A B) :=
  WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
    (shortW_nonsingular_neg_sqrt_of_pos (A := A) (B := B) (x := x) (hposRight hx))

@[simp]
theorem componentBit_upperRightPoint
    {A B e : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    {x : ℝ} (hx : e < x) :
    componentBit (A := A) (B := B) e (upperRightPoint hposRight x hx) = 0 := by
  simp [upperRightPoint, componentBit, sideBit, not_lt_of_gt hx]

@[simp]
theorem componentBit_lowerRightPoint
    {A B e : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    {x : ℝ} (hx : e < x) :
    componentBit (A := A) (B := B) e (lowerRightPoint hposRight x hx) = 0 := by
  simp [lowerRightPoint, componentBit, sideBit, not_lt_of_gt hx]

/-- Upper branch point as an element of the component kernel. -/
def upperRightKerPoint
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : ℝ) (hx : e < x) :
    ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
  ⟨upperRightPoint hposRight x hx, componentBit_upperRightPoint hposRight hx⟩

/-- Lower branch point as an element of the component kernel. -/
def lowerRightKerPoint
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : ℝ) (hx : e < x) :
    ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
  ⟨lowerRightPoint hposRight x hx, componentBit_lowerRightPoint hposRight hx⟩

@[simp]
theorem thetaCandidate_upperRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) =
      ((-sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)) := by
  have hnonneg : 0 ≤ √(shortCubic A B x) :=
    Real.sqrt_nonneg _
  simpa [thetaPeriod, upperRightKerPoint, upperRightPoint] using
    thetaCandidate_some_upper_eq_neg_sigma (A := A) (B := B) (e := e)
      (x := x) (y := √(shortCubic A B x))
      (P := upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx)
      rfl hx hnonneg

@[simp]
theorem thetaCandidate_lowerRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) =
      ((sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)) := by
  have hneg : -√(shortCubic A B x) < 0 :=
    neg_lt_zero.mpr (Real.sqrt_pos.mpr (hposRight hx))
  simpa [thetaPeriod, lowerRightKerPoint, lowerRightPoint] using
    thetaCandidate_some_lower (A := A) (B := B) (e := e)
      (x := x) (y := -√(shortCubic A B x))
      (P := lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx)
      rfl hx hneg

theorem tendsto_addCircle_sigma_nhdsGT_root
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (fun x : ℝ => ((sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)))
      (𝓝[>] e)
      (𝓝 (((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)))) := by
  exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto
    (halfPeriod A B e) |>.comp
      (tendsto_sigma_nhdsGT_root (A := A) (B := B) (e := e)
        hroot hderiv hposRight)

theorem tendsto_addCircle_neg_sigma_nhdsGT_root
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (fun x : ℝ => ((-sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)))
      (𝓝[>] e)
      (𝓝 (((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)))) := by
  have hneg :
      Tendsto (fun x : ℝ => -sigma A B x) (𝓝[>] e) (𝓝 (-halfPeriod A B e)) :=
    (tendsto_sigma_nhdsGT_root (A := A) (B := B) (e := e)
      hroot hderiv hposRight).neg
  have hcoe :
      Tendsto
        (fun x : ℝ => ((-sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)))
        (𝓝[>] e)
        (𝓝 (((-halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)))) :=
    (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto
      (-halfPeriod A B e) |>.comp hneg
  have hroot_eq :
      (((-halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e))) =
        (((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e))) := by
    simpa [thetaPeriod] using
      (addCircle_halfPeriod_eq_neg (A := A) (B := B) (e := e)).symm
  simpa only [hroot_eq] using hcoe

theorem tendsto_thetaCandidate_upperRightKerPoint_nhdsGT_root
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (fun x : ℝ =>
        if hx : e < x then
          thetaCandidate (A := A) (B := B) (e := e)
            (upperRightKerPoint (A := A) (B := B) (e := e)
              (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        else
          thetaCandidate (A := A) (B := B) (e := e)
            (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))
      (𝓝[>] e)
      (𝓝 (thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))) := by
  have hformula := tendsto_addCircle_neg_sigma_nhdsGT_root
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv) hposRight
  have heq :
      (fun x : ℝ => ((-sigma A B x : ℝ) : AddCircle (thetaPeriod A B e))) =ᶠ[𝓝[>] e]
        fun x : ℝ =>
          if hx : e < x then
            thetaCandidate (A := A) (B := B) (e := e)
              (upperRightKerPoint (A := A) (B := B) (e := e)
                (hroot := hroot) (hderiv := hderiv) hposRight x hx)
          else
            thetaCandidate (A := A) (B := B) (e := e)
              (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxe : e < x := hx
    simp [hxe]
  refine Tendsto.congr' heq ?_
  simpa [thetaPeriod, thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv]
    using hformula

theorem tendsto_thetaCandidate_lowerRightKerPoint_nhdsGT_root
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (fun x : ℝ =>
        if hx : e < x then
          thetaCandidate (A := A) (B := B) (e := e)
            (lowerRightKerPoint (A := A) (B := B) (e := e)
              (hroot := hroot) (hderiv := hderiv) hposRight x hx)
        else
          thetaCandidate (A := A) (B := B) (e := e)
            (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))
      (𝓝[>] e)
      (𝓝 (thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))) := by
  have hformula := tendsto_addCircle_sigma_nhdsGT_root
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv) hposRight
  have heq :
      (fun x : ℝ => ((sigma A B x : ℝ) : AddCircle (thetaPeriod A B e))) =ᶠ[𝓝[>] e]
        fun x : ℝ =>
          if hx : e < x then
            thetaCandidate (A := A) (B := B) (e := e)
              (lowerRightKerPoint (A := A) (B := B) (e := e)
                (hroot := hroot) (hderiv := hderiv) hposRight x hx)
          else
            thetaCandidate (A := A) (B := B) (e := e)
              (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxe : e < x := hx
    simp [hxe]
  refine Tendsto.congr' heq ?_
  simpa [thetaPeriod, thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv]
    using hformula

theorem componentKer_eq_rootKerPoint_of_some_x_eq_root
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hxe : x = e) :
    P = rootKerPoint (A := A) (B := B) (e := e) hroot hderiv := by
  apply Subtype.ext
  have hy0 := componentKer_some_y_eq_zero_of_x_eq_root
    (A := A) (B := B) (e := e) (x := x) (y := y) (h := h) P hP hxe
  rw [hP]
  change WeierstrassCurve.Affine.Point.some x y h =
    WeierstrassCurve.Affine.Point.some e 0
      (shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
  exact point_some_ext (A := A) (B := B) (h := h)
    (h' := shortW_nonsingular_root_of_deriv_pos
      (A := A) (B := B) (e := e) hroot hderiv)
    hxe hy0

theorem componentKer_eq_upperRightKerPoint_of_some_nonneg
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hx : e < x)
    (hy : 0 ≤ y) :
    P = upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx := by
  apply Subtype.ext
  have hysqrt := componentKer_some_y_eq_sqrt_of_gt_of_nonneg
    (A := A) (B := B) (e := e) (x := x) (y := y) (h := h)
    hposRight P hP hx hy
  rw [hP]
  change WeierstrassCurve.Affine.Point.some x y h =
    WeierstrassCurve.Affine.Point.some x (√(shortCubic A B x))
      (shortW_nonsingular_sqrt_of_pos
        (A := A) (B := B) (x := x) (hposRight hx))
  exact point_some_ext (A := A) (B := B) (h := h)
    (h' := shortW_nonsingular_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    rfl hysqrt

theorem componentKer_eq_lowerRightKerPoint_of_some_neg
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hx : e < x)
    (hy : y < 0) :
    P = lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx := by
  apply Subtype.ext
  have hysqrt := componentKer_some_y_eq_neg_sqrt_of_gt_of_neg
    (A := A) (B := B) (e := e) (x := x) (y := y) (h := h)
    hposRight P hP hx hy
  rw [hP]
  change WeierstrassCurve.Affine.Point.some x y h =
    WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
      (shortW_nonsingular_neg_sqrt_of_pos
        (A := A) (B := B) (x := x) (hposRight hx))
  exact point_some_ext (A := A) (B := B) (h := h)
    (h' := shortW_nonsingular_neg_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    rfl hysqrt

theorem neg_upperRightPoint_eq_lowerRightPoint
    {A B e x : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    -upperRightPoint (A := A) (B := B) (e := e) hposRight x hx =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx := by
  rw [upperRightPoint, lowerRightPoint, WeierstrassCurve.Affine.Point.neg_some]
  exact point_some_ext (A := A) (B := B)
    (x := x) (y := WeierstrassCurve.Affine.negY (shortW A B) x
      (√(shortCubic A B x)))
    (x' := x) (y' := -√(shortCubic A B x))
    rfl (by simp [shortW])

theorem neg_lowerRightPoint_eq_upperRightPoint
    {A B e x : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    -lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx =
      upperRightPoint (A := A) (B := B) (e := e) hposRight x hx := by
  rw [lowerRightPoint, upperRightPoint, WeierstrassCurve.Affine.Point.neg_some]
  exact point_some_ext (A := A) (B := B)
    (x := x) (y := WeierstrassCurve.Affine.negY (shortW A B) x
      (-√(shortCubic A B x)))
    (x' := x) (y' := √(shortCubic A B x))
    rfl (by simp [shortW])

theorem neg_upperRightKerPoint_eq_lowerRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    -upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx =
      lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx := by
  apply Subtype.ext
  exact neg_upperRightPoint_eq_lowerRightPoint
    (A := A) (B := B) (e := e) hposRight hx

theorem neg_lowerRightKerPoint_eq_upperRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    -lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx =
      upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx := by
  apply Subtype.ext
  exact neg_lowerRightPoint_eq_upperRightPoint
    (A := A) (B := B) (e := e) hposRight hx

theorem thetaCandidate_lowerRightKerPoint_eq_neg_upper
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) =
      -thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) := by
  simp [thetaPeriod]

/-- Pointwise additivity of the S5 theta candidate.  This is the S6-S8 target. -/
def ThetaCandidateAdditive
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} : Prop :=
  ∀ P Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv,
    thetaCandidate (A := A) (B := B) (e := e) (P + Q) =
      thetaCandidate (A := A) (B := B) (e := e) P +
        thetaCandidate (A := A) (B := B) (e := e) Q

/-- The AddCircle defect of the S5 theta candidate. -/
def thetaDefect
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    AddCircle (thetaPeriod A B e) :=
  thetaCandidate (A := A) (B := B) (e := e) (P + Q) -
    thetaCandidate (A := A) (B := B) (e := e) P -
      thetaCandidate (A := A) (B := B) (e := e) Q

@[simp]
theorem thetaDefect_zero_left
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaDefect (A := A) (B := B) (e := e)
      (0 : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) P = 0 := by
  simp [thetaDefect, thetaPeriod]

@[simp]
theorem thetaDefect_zero_right
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaDefect (A := A) (B := B) (e := e) P
      (0 : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) = 0 := by
  simp [thetaDefect, thetaPeriod]

theorem thetaDefect_eq_zero_iff
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaDefect (A := A) (B := B) (e := e) P Q = 0 ↔
      thetaCandidate (A := A) (B := B) (e := e) (P + Q) =
        thetaCandidate (A := A) (B := B) (e := e) P +
          thetaCandidate (A := A) (B := B) (e := e) Q := by
  constructor
  · intro h
    have h' :
        thetaCandidate (A := A) (B := B) (e := e) (P + Q) -
            (thetaCandidate (A := A) (B := B) (e := e) P +
              thetaCandidate (A := A) (B := B) (e := e) Q) = 0 := by
      simpa [thetaDefect, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    exact sub_eq_zero.mp h'
  · intro h
    have h' :
        thetaCandidate (A := A) (B := B) (e := e) (P + Q) -
            (thetaCandidate (A := A) (B := B) (e := e) P +
              thetaCandidate (A := A) (B := B) (e := e) Q) = 0 :=
      sub_eq_zero.mpr h
    simpa [thetaDefect, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'

theorem thetaCandidateAdditive_iff_defect_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} :
    ThetaCandidateAdditive (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) ↔
      ∀ P Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv,
        thetaDefect (A := A) (B := B) (e := e) P Q = 0 := by
  constructor
  · intro hadd P Q
    exact (thetaDefect_eq_zero_iff (A := A) (B := B) (e := e) P Q).2 (hadd P Q)
  · intro hdef P Q
    exact (thetaDefect_eq_zero_iff (A := A) (B := B) (e := e) P Q).1 (hdef P Q)

/-- Package the S5 theta candidate as an additive hom once S6-S8 prove additivity. -/
def thetaCandidateHom
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hadd : ThetaCandidateAdditive (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv)) :
    ComponentKer (A := A) (B := B) (e := e) hroot hderiv →+
      AddCircle (thetaPeriod A B e) where
  toFun := thetaCandidate (A := A) (B := B) (e := e)
  map_zero' := thetaCandidate_zero (A := A) (B := B) (e := e)
  map_add' := hadd

@[simp]
theorem thetaCandidateHom_apply
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hadd : ThetaCandidateAdditive (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv))
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaCandidateHom (A := A) (B := B) (e := e) hadd P =
      thetaCandidate (A := A) (B := B) (e := e) P :=
  rfl

theorem thetaCandidateHom_injective
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hadd : ThetaCandidateAdditive (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv)) :
    Function.Injective (thetaCandidateHom (A := A) (B := B) (e := e) hadd) := by
  simpa [thetaCandidateHom] using
    thetaCandidate_injective (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight

theorem exists_injective_thetaHom_of_thetaCandidate_additive
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hadd : ThetaCandidateAdditive (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv)) :
    ∃ T : ℝ,
      ∃ theta :
        (componentBitHom (A := A) (B := B) (e := e) hroot hderiv).ker →+
          AddCircle T,
        Function.Injective theta := by
  exact ⟨thetaPeriod A B e,
    thetaCandidateHom (A := A) (B := B) (e := e) hadd,
    thetaCandidateHom_injective (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight hadd⟩

end

end MazurProof.RealTopology
