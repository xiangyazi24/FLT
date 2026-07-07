import FLT.Assumptions.MazurProof.RealTopologyS9

/-!
# Real topology route, S10: translation by the real 2-torsion point

For the branch point `T₂ = (e, 0)`, the chord formula simplifies enough that
there are no bad points on the ray `e < x`.  The S8 branch constancy lemmas
therefore apply on all of `Set.Ioi e`; the S9 atTop glue then normalizes the
defect to zero.
-/

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

private theorem componentKer_branch_exhaustion
    {A B e : ℝ} {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    P = 0 ∨ P = rootKerPoint hroot hderiv ∨
      (∃ x hx, P = upperRightKerPoint hposRight x hx) ∨
        (∃ x hx, P = lowerRightKerPoint hposRight x hx) := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero => exact Or.inl (Subtype.ext rfl)
  | some x y h =>
      right
      let Ps : ComponentKer (A := A) (B := B) (e := e) hroot hderiv := ⟨_, hP⟩
      change Ps = rootKerPoint hroot hderiv ∨
        (∃ x hx, Ps = upperRightKerPoint hposRight x hx) ∨
          (∃ x hx, Ps = lowerRightKerPoint hposRight x hx)
      rcases componentKer_some_eq_or_gt Ps rfl with hxe | hx
      · exact Or.inl (componentKer_eq_rootKerPoint_of_some_x_eq_root Ps rfl hxe)
      · right
        by_cases hy : 0 ≤ y
        · exact Or.inl
            ⟨x, hx, componentKer_eq_upperRightKerPoint_of_some_nonneg
              hposRight Ps rfl hx hy⟩
        · exact Or.inr
            ⟨x, hx, componentKer_eq_lowerRightKerPoint_of_some_neg
              hposRight Ps rfl hx (not_le.mp hy)⟩

private theorem t2_chordX_sub_root_eq
    {A B e x y : ℝ}
    (hroot : shortCubic A B e = 0)
    (hy : y ^ 2 = shortCubic A B x)
    (hD : x - e ≠ 0) :
    chordX A x y e 0 - e = shortCubicDeriv A B e / (x - e) := by
  unfold chordX chordM shortCubic shortCubicDeriv at *
  field_simp [hD]
  ring_nf at hroot hy ⊢
  nlinarith

private theorem t2_chordX_gt_root
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hx : e < x)
    (hy : y ^ 2 = shortCubic A B x) :
    e < chordX A x y e 0 := by
  have hD : x - e ≠ 0 := by linarith
  have hxD : 0 < x - e := by linarith
  have hsub := t2_chordX_sub_root_eq (A := A) (B := B) (e := e)
    (x := x) (y := y) hroot hy hD
  have hpos : 0 < chordX A x y e 0 - e := by
    rw [hsub]
    exact div_pos hderiv hxD
  linarith

private theorem t2_chordY_eq
    {A x y e : ℝ}
    (hD : x - e ≠ 0) :
    chordY A x y e 0 =
      -y * ((chordX A x y e 0 - e) / (x - e)) := by
  unfold chordY chordM
  field_simp [hD]
  ring

private theorem t2_chordY_upper_neg
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    chordY A x (√(shortCubic A B x)) e 0 < 0 := by
  have hD : x - e ≠ 0 := by linarith
  have hxD : 0 < x - e := by linarith
  have hy : (√(shortCubic A B x)) ^ 2 = shortCubic A B x :=
    sq_sqrt (hposRight hx).le
  have hx3 : e < chordX A x (√(shortCubic A B x)) e 0 :=
    t2_chordX_gt_root (A := A) (B := B) (e := e) (hroot := hroot)
      hderiv hx hy
  have hratio :
      0 < (chordX A x (√(shortCubic A B x)) e 0 - e) / (x - e) :=
    div_pos (by linarith) hxD
  have hypos : 0 < √(shortCubic A B x) :=
    sqrt_pos.mpr (hposRight hx)
  rw [t2_chordY_eq (A := A) (x := x) (y := √(shortCubic A B x)) (e := e) hD]
  nlinarith [mul_pos hypos hratio]

private theorem t2_chordY_lower_pos
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    0 < chordY A x (-√(shortCubic A B x)) e 0 := by
  have hD : x - e ≠ 0 := by linarith
  have hxD : 0 < x - e := by linarith
  have hy : (-√(shortCubic A B x)) ^ 2 = shortCubic A B x := by
    rw [neg_sq]
    exact sq_sqrt (hposRight hx).le
  have hx3 : e < chordX A x (-√(shortCubic A B x)) e 0 :=
    t2_chordX_gt_root (A := A) (B := B) (e := e) (hroot := hroot)
      hderiv hx hy
  have hratio :
      0 < (chordX A x (-√(shortCubic A B x)) e 0 - e) / (x - e) :=
    div_pos (by linarith) hxD
  have hypos : 0 < √(shortCubic A B x) :=
    sqrt_pos.mpr (hposRight hx)
  rw [t2_chordY_eq (A := A) (x := x) (y := -√(shortCubic A B x)) (e := e) hD]
  nlinarith [mul_pos hypos hratio]

private theorem t2_chordX_upper_gt_root
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    e < chordX A x (√(shortCubic A B x)) e 0 := by
  exact t2_chordX_gt_root (A := A) (B := B) (e := e) (hroot := hroot)
    hderiv hx (sq_sqrt (hposRight hx).le)

private theorem t2_chordX_lower_gt_root
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    e < chordX A x (-√(shortCubic A B x)) e 0 := by
  have hy : (-√(shortCubic A B x)) ^ 2 = shortCubic A B x := by
    rw [neg_sq]
    exact sq_sqrt (hposRight hx).le
  exact t2_chordX_gt_root (A := A) (B := B) (e := e) (hroot := hroot)
    hderiv hx hy

theorem upperRightKerPoint_add_rootKerPoint_eq_lowerRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx +
      rootKerPoint (A := A) (B := B) (e := e) hroot hderiv =
    lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (chordX A x (√(shortCubic A B x)) e 0)
      (t2_chordX_upper_gt_root (A := A) (B := B) (e := e)
        (hroot := hroot) hderiv hposRight hx) := by
  apply Subtype.ext
  have hD : x - e ≠ 0 := by linarith
  have hx3 := t2_chordX_upper_gt_root (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx
  have hy3 := t2_chordY_upper_neg (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx
  simpa [upperRightKerPoint, lowerRightKerPoint, rootKerPoint, rootPoint]
    using upperRightPoint_add_eq_lowerRightPoint_of_chordY_neg
      (A := A) (B := B) (e := e) hposRight hx
      (hQ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      hD hx3 hy3

theorem lowerRightKerPoint_add_rootKerPoint_eq_upperRightKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx +
      rootKerPoint (A := A) (B := B) (e := e) hroot hderiv =
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (chordX A x (-√(shortCubic A B x)) e 0)
      (t2_chordX_lower_gt_root (A := A) (B := B) (e := e)
        (hroot := hroot) hderiv hposRight hx) := by
  apply Subtype.ext
  have hD : x - e ≠ 0 := by linarith
  have hx3 := t2_chordX_lower_gt_root (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx
  have hy3 := t2_chordY_lower_pos (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx
  simpa [lowerRightKerPoint, upperRightKerPoint, rootKerPoint, rootPoint]
    using lowerRightPoint_add_eq_upperRightPoint_of_chordY_pos
      (A := A) (B := B) (e := e) hposRight hx
      (hQ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      hD hx3 hy3

private theorem upperT2Defect_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    IsLocallyConstant
      (upperThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)) := by
  apply IsLocallyConstant.of_constant
  intro x y
  exact thetaDefect_upperRight_some_const_on_of_chordY_neg
    (A := A) (B := B) (e := e) (a := e) (b := 0)
    (qtheta := halfPeriod A B e) (s := Set.Ioi e)
    isOpen_Ioi isPreconnected_Ioi hposRight
    (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (hQ := shortW_nonsingular_root_of_deriv_pos
      (A := A) (B := B) (e := e) hroot hderiv)
    (by rfl)
    (thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (fun z hz => hz)
    (fun z hz => sub_ne_zero.mpr (ne_of_gt (show e < z from hz)))
    (fun z hz => t2_chordX_upper_gt_root (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hz)
    (fun z hz => t2_chordY_upper_neg (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hz)
    x.2 y.2

private theorem lowerT2Defect_isLocallyConstant
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    IsLocallyConstant
      (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)) := by
  apply IsLocallyConstant.of_constant
  intro x y
  exact thetaDefect_lowerRight_some_const_on_of_chordY_pos
    (A := A) (B := B) (e := e) (a := e) (b := 0)
    (qtheta := halfPeriod A B e) (s := Set.Ioi e)
    isOpen_Ioi isPreconnected_Ioi hposRight
    (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (hQ := shortW_nonsingular_root_of_deriv_pos
      (A := A) (B := B) (e := e) hroot hderiv)
    (by rfl)
    (thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (fun z hz => hz)
    (fun z hz => sub_ne_zero.mpr (ne_of_gt (show e < z from hz)))
    (fun z hz => t2_chordX_lower_gt_root (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hz)
    (fun z hz => t2_chordY_lower_pos (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hz)
    x.2 y.2

private theorem tendsto_t2_chordX_upper_atTop_nhds
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (fun x : ℝ => chordX A x (√(shortCubic A B x)) e 0) atTop (𝓝 e) := by
  have hden : Tendsto (fun x : ℝ => x - e) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-e) (tendsto_id : Tendsto id atTop atTop)
  have hfrac :
      Tendsto (fun x : ℝ => shortCubicDeriv A B e / (x - e)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have htarget :
      Tendsto (fun x : ℝ => e + shortCubicDeriv A B e / (x - e))
        atTop (𝓝 e) := by
    simpa using tendsto_const_nhds.add hfrac
  have heq :
      (fun x : ℝ => chordX A x (√(shortCubic A B x)) e 0) =ᶠ[atTop]
        fun x : ℝ => e + shortCubicDeriv A B e / (x - e) := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hD : x - e ≠ 0 := by linarith
    have hy : (√(shortCubic A B x)) ^ 2 = shortCubic A B x :=
      sq_sqrt (hposRight hx).le
    have hsub := t2_chordX_sub_root_eq (A := A) (B := B) (e := e)
      (x := x) (y := √(shortCubic A B x)) hroot hy hD
    linarith
  exact Tendsto.congr' heq.symm htarget

private theorem tendsto_t2_chordX_lower_atTop_nhds
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (fun x : ℝ => chordX A x (-√(shortCubic A B x)) e 0) atTop (𝓝 e) := by
  have hden : Tendsto (fun x : ℝ => x - e) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-e) (tendsto_id : Tendsto id atTop atTop)
  have hfrac :
      Tendsto (fun x : ℝ => shortCubicDeriv A B e / (x - e)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have htarget :
      Tendsto (fun x : ℝ => e + shortCubicDeriv A B e / (x - e))
        atTop (𝓝 e) := by
    simpa using tendsto_const_nhds.add hfrac
  have heq :
      (fun x : ℝ => chordX A x (-√(shortCubic A B x)) e 0) =ᶠ[atTop]
        fun x : ℝ => e + shortCubicDeriv A B e / (x - e) := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hD : x - e ≠ 0 := by linarith
    have hy : (-√(shortCubic A B x)) ^ 2 = shortCubic A B x := by
      rw [neg_sq]
      exact sq_sqrt (hposRight hx).le
    have hsub := t2_chordX_sub_root_eq (A := A) (B := B) (e := e)
      (x := x) (y := -√(shortCubic A B x)) hroot hy hD
    linarith
  exact Tendsto.congr' heq.symm htarget

private theorem tendsto_t2_chordX_upper_atTop_nhdsGT
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (fun x : ℝ => chordX A x (√(shortCubic A B x)) e 0)
      atTop (𝓝[>] e) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨
    tendsto_t2_chordX_upper_atTop_nhds (A := A) (B := B) (e := e)
      (hroot := hroot) hposRight, ?_⟩
  filter_upwards [eventually_gt_atTop e] with x hx
  exact t2_chordX_upper_gt_root (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx

private theorem tendsto_t2_chordX_lower_atTop_nhdsGT
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (fun x : ℝ => chordX A x (-√(shortCubic A B x)) e 0)
      atTop (𝓝[>] e) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨
    tendsto_t2_chordX_lower_atTop_nhds (A := A) (B := B) (e := e)
      (hroot := hroot) hposRight, ?_⟩
  filter_upwards [eventually_gt_atTop e] with x hx
  exact t2_chordX_lower_gt_root (A := A) (B := B) (e := e)
    (hroot := hroot) hderiv hposRight hx

private theorem upperT2Defect_tendsto_atTop_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (upperThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))
      atTop (𝓝 0) := by
  have hsig3 :
      Tendsto
        (fun x : ℝ => sigma A B (chordX A x (√(shortCubic A B x)) e 0))
        atTop (𝓝 (halfPeriod A B e)) :=
    (tendsto_sigma_nhdsGT_root (A := A) (B := B) (e := e)
      hroot hderiv hposRight).comp
      (tendsto_t2_chordX_upper_atTop_nhdsGT (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight)
  have hsx : Tendsto (sigma A B) atTop (𝓝 0) :=
    tendsto_sigma_atTop (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hreal :
      Tendsto
        (fun x : ℝ =>
          sigma A B (chordX A x (√(shortCubic A B x)) e 0) -
            (-sigma A B x) - halfPeriod A B e)
        atTop (𝓝 (halfPeriod A B e - (-0) - halfPeriod A B e)) :=
    (hsig3.sub hsx.neg).sub tendsto_const_nhds
  have hcircle :
      Tendsto
        (fun x : ℝ =>
          ((sigma A B (chordX A x (√(shortCubic A B x)) e 0) -
              (-sigma A B x) - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)))
        atTop
        (𝓝 (((halfPeriod A B e - (-0) - halfPeriod A B e : ℝ) :
          AddCircle (thetaPeriod A B e)))) :=
    (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto
      (halfPeriod A B e - (-0) - halfPeriod A B e) |>.comp hreal
  have hlim :
      Tendsto
        (fun x : ℝ =>
          ((sigma A B (chordX A x (√(shortCubic A B x)) e 0) -
              (-sigma A B x) - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)))
        atTop (𝓝 0) := by
    simpa using hcircle
  have heq :
      upperThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
        =ᶠ[atTop]
        fun x : ℝ =>
          ((sigma A B (chordX A x (√(shortCubic A B x)) e 0) -
              (-sigma A B x) - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)) := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hD : x - e ≠ 0 := by linarith
    have hx3 := t2_chordX_upper_gt_root (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hx
    have hy3 := t2_chordY_upper_neg (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hx
    have hformula := thetaDefect_upperRight_some_of_chordY_neg
      (A := A) (B := B) (e := e) hposRight
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
      (hQ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      (by rfl)
      (thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
      hx hD hx3 hy3
    simpa [upperThetaDefectAtX, hx] using hformula
  exact Tendsto.congr' heq.symm hlim

private theorem lower_limit_coe_eq_zero
    {A B e : ℝ} :
    (((-halfPeriod A B e - 0 - halfPeriod A B e : ℝ) :
      AddCircle (thetaPeriod A B e))) = 0 := by
  rw [show -halfPeriod A B e - 0 - halfPeriod A B e =
      -thetaPeriod A B e by simp [thetaPeriod]; ring]
  change -(((thetaPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e))) = 0
  simp

private theorem lowerT2Defect_tendsto_atTop_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto
      (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))
      atTop (𝓝 0) := by
  have hsig3 :
      Tendsto
        (fun x : ℝ => sigma A B (chordX A x (-√(shortCubic A B x)) e 0))
        atTop (𝓝 (halfPeriod A B e)) :=
    (tendsto_sigma_nhdsGT_root (A := A) (B := B) (e := e)
      hroot hderiv hposRight).comp
      (tendsto_t2_chordX_lower_atTop_nhdsGT (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight)
  have hsx : Tendsto (sigma A B) atTop (𝓝 0) :=
    tendsto_sigma_atTop (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hreal :
      Tendsto
        (fun x : ℝ =>
          -sigma A B (chordX A x (-√(shortCubic A B x)) e 0) -
            sigma A B x - halfPeriod A B e)
        atTop (𝓝 (-halfPeriod A B e - 0 - halfPeriod A B e)) :=
    (hsig3.neg.sub hsx).sub tendsto_const_nhds
  have hcircle :
      Tendsto
        (fun x : ℝ =>
          ((-sigma A B (chordX A x (-√(shortCubic A B x)) e 0) -
              sigma A B x - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)))
        atTop
        (𝓝 (((-halfPeriod A B e - 0 - halfPeriod A B e : ℝ) :
          AddCircle (thetaPeriod A B e)))) :=
    (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto
      (-halfPeriod A B e - 0 - halfPeriod A B e) |>.comp hreal
  have hlim :
      Tendsto
        (fun x : ℝ =>
          ((-sigma A B (chordX A x (-√(shortCubic A B x)) e 0) -
              sigma A B x - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)))
        atTop (𝓝 0) := by
    rw [lower_limit_coe_eq_zero (A := A) (B := B) (e := e)] at hcircle
    exact hcircle
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
        =ᶠ[atTop]
        fun x : ℝ =>
          ((-sigma A B (chordX A x (-√(shortCubic A B x)) e 0) -
              sigma A B x - halfPeriod A B e : ℝ) :
            AddCircle (thetaPeriod A B e)) := by
    filter_upwards [eventually_gt_atTop e] with x hx
    have hD : x - e ≠ 0 := by linarith
    have hx3 := t2_chordX_lower_gt_root (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hx
    have hy3 := t2_chordY_lower_pos (A := A) (B := B) (e := e)
      (hroot := hroot) hderiv hposRight hx
    have hformula := thetaDefect_lowerRight_some_of_chordY_pos
      (A := A) (B := B) (e := e) hposRight
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
      (hQ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      (by rfl)
      (thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
      hx hD hx3 hy3
    simpa [lowerThetaDefectAtX, hx] using hformula
  exact Tendsto.congr' heq.symm hlim

private theorem upperT2DefectOnIoi_eq_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : Set.Ioi e) :
    upperThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) x = 0 := by
  exact upperThetaDefectOnIoi_eq_zero_of_isLocallyConstant_of_tendsto_atTop_zero
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    (hposRight := hposRight)
    (Q := rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (upperT2Defect_isLocallyConstant (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight)
    (upperT2Defect_tendsto_atTop_zero (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight)
    x

private theorem lowerT2DefectOnIoi_eq_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (x : Set.Ioi e) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) x = 0 := by
  exact lowerThetaDefectOnIoi_eq_zero_of_isLocallyConstant_of_tendsto_atTop_zero
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    (hposRight := hposRight)
    (Q := rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)
    (lowerT2Defect_isLocallyConstant (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight)
    (lowerT2Defect_tendsto_atTop_zero (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight)
    x

theorem thetaCandidate_upperRight_add_rootKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
  have hdef := upperT2DefectOnIoi_eq_zero (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight ⟨x, hx⟩
  exact (thetaDefect_eq_zero_iff (A := A) (B := B) (e := e)
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx)
    (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)).1 hdef

theorem thetaCandidate_lowerRight_add_rootKerPoint
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
  have hdef := lowerT2DefectOnIoi_eq_zero (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight ⟨x, hx⟩
  exact (thetaDefect_eq_zero_iff (A := A) (B := B) (e := e)
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx)
    (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv)).1 hdef

theorem rootKerPoint_add_rootKerPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    rootKerPoint (A := A) (B := B) (e := e) hroot hderiv +
      rootKerPoint (A := A) (B := B) (e := e) hroot hderiv = 0 := by
  apply Subtype.ext
  simpa [rootKerPoint, rootPoint, shortW_negY] using
    WeierstrassCurve.Affine.Point.add_of_Y_eq (W := shortW A B)
      (x₁ := e) (x₂ := e)
      (y₁ := 0) (y₂ := 0)
      (h₁ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      (h₂ := shortW_nonsingular_root_of_deriv_pos
        (A := A) (B := B) (e := e) hroot hderiv)
      rfl (by simp [shortW, WeierstrassCurve.Affine.negY])

private theorem thetaCandidate_rootKerPoint_add_rootKerPoint
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} :
    thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv +
          rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
  rw [rootKerPoint_add_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv]
  rw [thetaCandidate_zero]
  have hsum :
      thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
        0 := by
    rw [thetaCandidate_rootKerPoint (A := A) (B := B) (e := e) hroot hderiv]
    change (((halfPeriod A B e + halfPeriod A B e : ℝ) :
      AddCircle (thetaPeriod A B e))) = 0
    rw [show halfPeriod A B e + halfPeriod A B e = thetaPeriod A B e by
      rw [thetaPeriod]
      ring]
    exact AddCircle.coe_period (thetaPeriod A B e)
  rw [hsum]

theorem thetaCandidate_T2_translation
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaCandidate (A := A) (B := B) (e := e)
        (P + rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      thetaCandidate (A := A) (B := B) (e := e) P +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
  rcases componentKer_branch_exhaustion
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight P with hzero | hrest
  · subst P
    simp
  rcases hrest with hrootP | hbranches
  · rw [hrootP]
    exact thetaCandidate_rootKerPoint_add_rootKerPoint
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
  rcases hbranches with hupper | hlower
  · rcases hupper with ⟨x, hx, rfl⟩
    exact thetaCandidate_upperRight_add_rootKerPoint
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx
  · rcases hlower with ⟨x, hx, rfl⟩
    exact thetaCandidate_lowerRight_add_rootKerPoint
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx

end

end MazurProof.RealTopology
