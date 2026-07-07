import FLT.Assumptions.MazurProof.RealTopologyS9

/-!
# Real topology route, S10 mixed branch

This file targets the mixed lower/upper branch additivity statement.
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

theorem continuousAt_lower_upper_chordX
    {A B x a : ℝ}
    (hD : x - a ≠ 0) :
    ContinuousAt
      (fun z : ℝ => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) x := by
  unfold chordX chordM shortCubic
  fun_prop

theorem continuousAt_lower_upper_chordY
    {A B x a : ℝ}
    (hD : x - a ≠ 0) :
    ContinuousAt
      (fun z : ℝ => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) x := by
  unfold chordY chordX chordM shortCubic
  fun_prop

theorem tendsto_lower_upper_chordX_vertical_atTop
    {A B e a : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    Tendsto
      (fun z : ℝ => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a)))
      (𝓝[≠] a) atTop := by
  let b : ℝ := √(shortCubic A B a)
  let num : ℝ → ℝ := fun z => -√(shortCubic A B z) - b
  let invDenNorm : ℝ → ℝ := fun z => ‖z - a‖⁻¹
  have hbpos : 0 < b := by
    dsimp [b]
    exact sqrt_pos.mpr (hposRight ha)
  have hsqrt_tend :
      Tendsto (fun z : ℝ => √(shortCubic A B z)) (𝓝[≠] a) (𝓝 b) := by
    have hcont : ContinuousAt (fun z : ℝ => √(shortCubic A B z)) a := by
      unfold shortCubic
      fun_prop
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnum_tend : Tendsto num (𝓝[≠] a) (𝓝 (-2 * b)) := by
    have hbconst : Tendsto (fun _ : ℝ => b) (𝓝[≠] a) (𝓝 b) := tendsto_const_nhds
    have h := hsqrt_tend.neg.sub hbconst
    simpa [num, sub_eq_add_neg, two_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hnum_norm_tend :
      Tendsto (fun z : ℝ => ‖num z‖) (𝓝[≠] a) (𝓝 (2 * b)) := by
    have h := hnum_tend.norm
    simpa [Real.norm_eq_abs, abs_of_nonneg hbpos.le] using h
  have hnum_ge : ∀ᶠ z : ℝ in 𝓝[≠] a, b ≤ ‖num z‖ := by
    filter_upwards [hnum_norm_tend (Ioi_mem_nhds (by nlinarith [hbpos] : b < 2 * b))]
      with z hz
    exact le_of_lt hz
  have hinvDenNorm_atTop : Tendsto invDenNorm (𝓝[≠] a) atTop := by
    change Tendsto (fun z : ℝ => (‖z - a‖)⁻¹) (𝓝[≠] a) atTop
    exact (tendsto_norm_sub_self_nhdsNE (a := a)).inv_tendsto_nhdsGT_zero
  have hinvDenNorm_sq_atTop :
      Tendsto (fun z : ℝ => invDenNorm z ^ 2) (𝓝[≠] a) atTop := by
    simpa [pow_two] using
      hinvDenNorm_atTop.atTop_mul_atTop₀ hinvDenNorm_atTop
  have hmodel_atTop :
      Tendsto (fun z : ℝ => b ^ 2 * invDenNorm z ^ 2) (𝓝[≠] a) atTop :=
    hinvDenNorm_sq_atTop.const_mul_atTop' (sq_pos_of_pos hbpos)
  have hm_sq_atTop :
      Tendsto
        (fun z : ℝ => (chordM z (-√(shortCubic A B z)) a b) ^ 2)
        (𝓝[≠] a) atTop := by
    refine tendsto_atTop_mono' _ ?_ hmodel_atTop
    filter_upwards [self_mem_nhdsWithin, hnum_ge] with z hz_ne hnum_bound
    have hz_ne' : z ≠ a := by simpa using hz_ne
    have hden : z - a ≠ 0 := sub_ne_zero.mpr hz_ne'
    have hb_nonneg : 0 ≤ b := hbpos.le
    have hsq_num : b ^ 2 ≤ (num z) ^ 2 := by
      have habs : |b| ≤ |num z| := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hb_nonneg] using hnum_bound
      simpa [sq_abs] using (sq_le_sq.mpr habs)
    calc
      b ^ 2 * invDenNorm z ^ 2 ≤ (num z) ^ 2 * invDenNorm z ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_num (sq_nonneg (invDenNorm z))
      _ = (chordM z (-√(shortCubic A B z)) a b) ^ 2 := by
        dsimp [num, invDenNorm, chordM]
        rw [inv_pow, sq_abs]
        field_simp [hden]
  have hz_le : ∀ᶠ z : ℝ in 𝓝[≠] a, z ≤ a + 1 := by
    have hz_tend : Tendsto (fun z : ℝ => z) (𝓝[≠] a) (𝓝 a) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    filter_upwards [hz_tend (Iio_mem_nhds (by linarith : a < a + 1))] with z hz
    exact le_of_lt hz
  have hshift_atTop :
      Tendsto
        (fun z : ℝ =>
          (chordM z (-√(shortCubic A B z)) a b) ^ 2 + (-A - (a + 1) - a))
        (𝓝[≠] a) atTop := by
    simpa using
      tendsto_atTop_add_const_right _ (-A - (a + 1) - a) hm_sq_atTop
  refine tendsto_atTop_mono' _ ?_ hshift_atTop
  filter_upwards [hz_le] with z hz
  dsimp [b, chordX]
  nlinarith

theorem eventually_lower_upper_chordY_ne_zero_vertical
    {A B e a : ℝ}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    ∀ᶠ z : ℝ in 𝓝[≠] a,
      chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
  let x3f : ℝ → ℝ :=
    fun z => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let y3f : ℝ → ℝ :=
    fun z => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  have hcx_atTop : Tendsto x3f (𝓝[≠] a) atTop := by
    simpa [x3f] using
      tendsto_lower_upper_chordX_vertical_atTop
        (A := A) (B := B) (e := e) hposRight ha
  filter_upwards
    [self_mem_nhdsWithin,
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id : Tendsto (fun z : ℝ => z)
        (𝓝[≠] a) (𝓝 a)) (Ioi_mem_nhds ha),
      hcx_atTop.eventually_gt_atTop e]
    with z hz_ne hzright hx3 hy0
  have hz_ne' : z ≠ a := by simpa using hz_ne
  have hD : z - a ≠ 0 := sub_ne_zero.mpr hz_ne'
  have hy : (-√(shortCubic A B z)) ^ 2 = shortCubic A B z := by
    rw [neg_sq]
    exact sq_sqrt (hposRight hzright).le
  have hb : (√(shortCubic A B a)) ^ 2 = shortCubic A B a :=
    sq_sqrt (hposRight ha).le
  have hcurve := chordY_sq_eq_shortCubic_chordX
    (A := A) (B := B) (x := z) (y := -√(shortCubic A B z))
    (a := a) (b := √(shortCubic A B a)) hy hb hD
  have hzero : shortCubic A B (x3f z) = 0 := by
    simpa [x3f, y3f, hy0] using hcurve.symm
  have hpos := hposRight hx3
  linarith

theorem tendsto_lowerThetaDefectAtX_upperRight_vertical_nhdsNE
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    Tendsto
      (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha))
      (𝓝[≠] a) (𝓝 0) := by
  let x3f : ℝ → ℝ :=
    fun z => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let y3f : ℝ → ℝ :=
    fun z => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let posExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => ((-sigma A B (x3f z) - sigma A B z - (-sigma A B a) : ℝ) :
      AddCircle (thetaPeriod A B e))
  let negExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => ((sigma A B (x3f z) - sigma A B z - (-sigma A B a) : ℝ) :
      AddCircle (thetaPeriod A B e))
  let branchExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => if 0 ≤ y3f z then posExpr z else negExpr z
  have hcx_atTop : Tendsto x3f (𝓝[≠] a) atTop := by
    simpa [x3f] using
      tendsto_lower_upper_chordX_vertical_atTop
        (A := A) (B := B) (e := e) hposRight ha
  have hsigma_x3 : Tendsto (fun z : ℝ => sigma A B (x3f z)) (𝓝[≠] a) (𝓝 0) :=
    (tendsto_sigma_atTop (A := A) (B := B) (e := e)
      hroot hderiv hposRight).comp hcx_atTop
  have hsigma_z : Tendsto (fun z : ℝ => sigma A B z) (𝓝[≠] a) (𝓝 (sigma A B a)) := by
    exact (sigma_hasDerivAt_of_right
      (A := A) (B := B) (e := e) hroot hderiv hposRight ha).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds
  have hposExpr : Tendsto posExpr (𝓝[≠] a) (𝓝 0) := by
    have hx3_mk :
        Tendsto (fun z : ℝ => ((sigma A B (x3f z) : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a) (𝓝 0) := by
      change Tendsto
        ((QuotientAddGroup.mk : ℝ → AddCircle (thetaPeriod A B e)) ∘
          fun z : ℝ => sigma A B (x3f z)) (𝓝[≠] a) (𝓝 0)
      exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto (0 : ℝ)
        |>.comp hsigma_x3
    have hz_mk :
        Tendsto (fun z : ℝ => ((sigma A B z : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a)
          (𝓝 (((sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)))) := by
      exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto (sigma A B a)
        |>.comp hsigma_z
    have hconst :
        Tendsto (fun _ : ℝ => ((sigma A B a : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a)
          (𝓝 (((sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)))) :=
      tendsto_const_nhds
    simpa [posExpr, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (hx3_mk.neg.sub hz_mk).add hconst
  have hnegExpr : Tendsto negExpr (𝓝[≠] a) (𝓝 0) := by
    have hx3_mk :
        Tendsto (fun z : ℝ => ((sigma A B (x3f z) : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a) (𝓝 0) := by
      change Tendsto
        ((QuotientAddGroup.mk : ℝ → AddCircle (thetaPeriod A B e)) ∘
          fun z : ℝ => sigma A B (x3f z)) (𝓝[≠] a) (𝓝 0)
      exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto (0 : ℝ)
        |>.comp hsigma_x3
    have hz_mk :
        Tendsto (fun z : ℝ => ((sigma A B z : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a)
          (𝓝 (((sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)))) := by
      exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto (sigma A B a)
        |>.comp hsigma_z
    have hconst :
        Tendsto (fun _ : ℝ => ((sigma A B a : ℝ) :
          AddCircle (thetaPeriod A B e))) (𝓝[≠] a)
          (𝓝 (((sigma A B a : ℝ) : AddCircle (thetaPeriod A B e)))) :=
      tendsto_const_nhds
    simpa [negExpr, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (hx3_mk.sub hz_mk).add hconst
  have hbranch : Tendsto branchExpr (𝓝[≠] a) (𝓝 0) := by
    intro U hU
    have hpU := hposExpr hU
    have hnU := hnegExpr hU
    change {z : ℝ | posExpr z ∈ U} ∈ 𝓝[≠] a at hpU
    change {z : ℝ | negExpr z ∈ U} ∈ 𝓝[≠] a at hnU
    change {z : ℝ | branchExpr z ∈ U} ∈ 𝓝[≠] a
    filter_upwards [hpU, hnU] with z hzpos hzneg
    by_cases hsign : 0 ≤ y3f z
    · simpa [branchExpr, hsign] using hzpos
    · simpa [branchExpr, hsign] using hzneg
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =ᶠ[𝓝[≠] a]
        branchExpr := by
    filter_upwards
      [self_mem_nhdsWithin,
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id : Tendsto (fun z : ℝ => z)
          (𝓝[≠] a) (𝓝 a)) (Ioi_mem_nhds ha),
        hcx_atTop.eventually_gt_atTop e]
      with z hz_ne hzright hx3
    have hz_ne' : z ≠ a := by simpa using hz_ne
    have hD : z - a ≠ 0 := sub_ne_zero.mpr hz_ne'
    have hy : (-√(shortCubic A B z)) ^ 2 = shortCubic A B z := by
      rw [neg_sq]
      exact sq_sqrt (hposRight hzright).le
    have hb : (√(shortCubic A B a)) ^ 2 = shortCubic A B a :=
      sq_sqrt (hposRight ha).le
    have hy3_ne : y3f z ≠ 0 := by
      intro hy0
      have hcurve := chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := z) (y := -√(shortCubic A B z))
        (a := a) (b := √(shortCubic A B a)) hy hb hD
      have hzero : shortCubic A B (x3f z) = 0 := by
        simpa [x3f, y3f, hy0] using hcurve.symm
      have hpos := hposRight hx3
      linarith
    by_cases hsign : 0 ≤ y3f z
    · have hypos : 0 < y3f z := lt_of_le_of_ne hsign hy3_ne.symm
      have hformula := thetaDefect_lowerRight_upperRight_of_chordY_pos
        (A := A) (B := B) (e := e) (x := z) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hzright ha hD
        (by simpa [x3f] using hx3)
        (by simpa [y3f] using hypos)
      rw [lowerThetaDefectAtX, dif_pos (show e < z from hzright)]
      simpa [lowerThetaDefectAtX, hzright, branchExpr, posExpr, x3f, y3f, hsign] using
        hformula
    · have hyneg : y3f z < 0 := not_le.mp hsign
      have hformula := thetaDefect_lowerRight_upperRight_of_chordY_neg
        (A := A) (B := B) (e := e) (x := z) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hzright ha hD
        (by simpa [x3f] using hx3)
        (by simpa [y3f] using hyneg)
      rw [lowerThetaDefectAtX, dif_pos (show e < z from hzright)]
      simpa [lowerThetaDefectAtX, hzright, branchExpr, negExpr, x3f, y3f, hsign] using
        hformula
  exact Tendsto.congr' heq.symm hbranch

theorem lower_upper_chordX_gt_root_of_chordY_ne_zero
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3_ne :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) ≠ 0) :
    e < chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) := by
  let y : ℝ := -√(shortCubic A B x)
  let b : ℝ := √(shortCubic A B a)
  let x3 : ℝ := chordX A x y a b
  let y3 : ℝ := chordY A x y a b
  have hy : y ^ 2 = shortCubic A B x := by
    dsimp [y]
    rw [neg_sq]
    exact sq_sqrt (hposRight hx).le
  have hb : b ^ 2 = shortCubic A B a := by
    dsimp [b]
    exact sq_sqrt (hposRight ha).le
  have hy3_ne' : y3 ≠ 0 := by
    simpa [y3, y, b] using hy3_ne
  have hcurve3 : y3 ^ 2 = shortCubic A B x3 := by
    simpa [x3, y3] using
      chordY_sq_eq_shortCubic_chordX
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        hy hb hD
  have hR : WeierstrassCurve.Affine.Nonsingular (shortW A B) x3 y3 :=
    shortW_nonsingular_of_sq_eq_of_y_ne_zero hcurve3 hy3_ne'
  let P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha
  let R : ComponentKer (A := A) (B := B) (e := e) hroot hderiv := P + Q
  have hsumPoint :
      lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx +
          upperRightPoint (A := A) (B := B) (e := e) hposRight a ha =
        WeierstrassCurve.Affine.Point.some x3 y3 hR := by
    rw [lowerRightPoint, upperRightPoint]
    simpa [y, b, x3, y3] using
      shortW_point_add_eq_chord
        (A := A) (B := B) (x := x) (y := y) (a := a) (b := b)
        (hP := shortW_nonsingular_neg_sqrt_of_pos
          (A := A) (B := B) (x := x) (hposRight hx))
        (hQ := shortW_nonsingular_sqrt_of_pos
          (A := A) (B := B) (x := a) (hposRight ha))
        (hR := hR) hD
  have hReq : R.1 = WeierstrassCurve.Affine.Point.some x3 y3 hR := by
    change P.1 + Q.1 = WeierstrassCurve.Affine.Point.some x3 y3 hR
    simpa [P, Q, lowerRightKerPoint, upperRightKerPoint] using hsumPoint
  have hx3ne : x3 ≠ e := by
    intro hxe
    have hy0 := componentKer_some_y_eq_zero_of_x_eq_root
      (A := A) (B := B) (e := e) (x := x3) (y := y3) (h := hR)
      R hReq hxe
    exact hy3_ne' hy0
  simpa [x3, y, b] using
    componentKer_some_gt_of_ne
      (A := A) (B := B) (e := e) (x := x3) (y := y3) (h := hR)
      R hReq hx3ne

theorem lowerRightKerPoint_add_upperRightKerPoint_eq_root_of_chordY_zero
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0) :
    lowerRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight x hx +
      upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha =
    rootKerPoint (A := A) (B := B) (e := e) hroot hderiv := by
  let P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha
  have hxy :
      ¬(x = a ∧
        -√(shortCubic A B x) =
          WeierstrassCurve.Affine.negY (shortW A B) a (√(shortCubic A B a))) := by
    intro h
    exact hD (sub_eq_zero.mpr h.1)
  have hsum := WeierstrassCurve.Affine.Point.add_some
    (W := shortW A B) (x₁ := x) (x₂ := a)
    (y₁ := -√(shortCubic A B x)) (y₂ := √(shortCubic A B a)) hxy
    (h₁ := shortW_nonsingular_neg_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    (h₂ := shortW_nonsingular_sqrt_of_pos
      (A := A) (B := B) (x := a) (hposRight ha))
  rcases componentKer_branch_exhaustion (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight (P + Q) with
    hzero | hrootcase | hupper | hlower
  · have hzeroPoint : (P + Q).1 = 0 := congrArg Subtype.val hzero
    have hzeroConcrete :
        WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
            (shortW_nonsingular_neg_sqrt_of_pos
              (A := A) (B := B) (x := x) (hposRight hx)) +
          WeierstrassCurve.Affine.Point.some a (√(shortCubic A B a))
            (shortW_nonsingular_sqrt_of_pos
              (A := A) (B := B) (x := a) (hposRight ha)) = 0 := by
      simpa [P, Q, lowerRightKerPoint, upperRightKerPoint,
        lowerRightPoint, upperRightPoint] using hzeroPoint
    rw [hzeroConcrete] at hsum
    cases hsum
  · simpa [P, Q] using hrootcase
  · rcases hupper with ⟨u, hu, hbranch⟩
    have hbranchPoint : (P + Q).1 =
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight u hu).1 :=
      congrArg Subtype.val hbranch
    have hbranchConcrete :
        WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
            (shortW_nonsingular_neg_sqrt_of_pos
              (A := A) (B := B) (x := x) (hposRight hx)) +
          WeierstrassCurve.Affine.Point.some a (√(shortCubic A B a))
            (shortW_nonsingular_sqrt_of_pos
              (A := A) (B := B) (x := a) (hposRight ha)) =
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight u hu).1 := by
      simpa [P, Q, lowerRightKerPoint, upperRightKerPoint,
        lowerRightPoint, upperRightPoint] using hbranchPoint
    have heqPoint := hbranchConcrete.symm.trans hsum
    change
      WeierstrassCurve.Affine.Point.some u (√(shortCubic A B u))
          (shortW_nonsingular_sqrt_of_pos
            (A := A) (B := B) (x := u) (hposRight hu)) =
        _ at heqPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq] at heqPoint
    have hycoord := heqPoint.2
    have hyadd := shortW_addY_eq_chordY
      (A := A) (B := B) (x := x) (y := -√(shortCubic A B x))
      (a := a) (b := √(shortCubic A B a)) hD
    rw [hyadd, hy3zero] at hycoord
    have hsqrtpos : 0 < √(shortCubic A B u) := sqrt_pos.mpr (hposRight hu)
    linarith
  · rcases hlower with ⟨u, hu, hbranch⟩
    have hbranchPoint : (P + Q).1 =
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight u hu).1 :=
      congrArg Subtype.val hbranch
    have hbranchConcrete :
        WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
            (shortW_nonsingular_neg_sqrt_of_pos
              (A := A) (B := B) (x := x) (hposRight hx)) +
          WeierstrassCurve.Affine.Point.some a (√(shortCubic A B a))
            (shortW_nonsingular_sqrt_of_pos
              (A := A) (B := B) (x := a) (hposRight ha)) =
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight u hu).1 := by
      simpa [P, Q, lowerRightKerPoint, upperRightKerPoint,
        lowerRightPoint, upperRightPoint] using hbranchPoint
    have heqPoint := hbranchConcrete.symm.trans hsum
    change
      WeierstrassCurve.Affine.Point.some u (-√(shortCubic A B u))
          (shortW_nonsingular_neg_sqrt_of_pos
            (A := A) (B := B) (x := u) (hposRight hu)) =
        _ at heqPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq] at heqPoint
    have hycoord := heqPoint.2
    have hyadd := shortW_addY_eq_chordY
      (A := A) (B := B) (x := x) (y := -√(shortCubic A B x))
      (a := a) (b := √(shortCubic A B a)) hD
    rw [hyadd, hy3zero] at hycoord
    have hsqrtpos : 0 < √(shortCubic A B u) := sqrt_pos.mpr (hposRight hu)
    linarith

theorem lowerRightKerPoint_injective_x
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (hy : e < y)
    (h :
      lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx =
        lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight y hy) :
    x = y := by
  have hp := congrArg Subtype.val h
  change
    lowerRightPoint (A := A) (B := B) (e := e) hposRight x hx =
      lowerRightPoint (A := A) (B := B) (e := e) hposRight y hy at hp
  rw [lowerRightPoint, lowerRightPoint, WeierstrassCurve.Affine.Point.some.injEq] at hp
  exact hp.1

theorem lower_upper_chordY_zero_unique
    {A B e x z a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (hz : e < z)
    (ha : e < a)
    (hDx : x - a ≠ 0)
    (hDz : z - a ≠ 0)
    (hyx :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0)
    (hyz :
      chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) = 0) :
    z = x := by
  have hxroot := lowerRightKerPoint_add_upperRightKerPoint_eq_root_of_chordY_zero
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (hroot := hroot) (hderiv := hderiv) hposRight hx ha hDx hyx
  have hzroot := lowerRightKerPoint_add_upperRightKerPoint_eq_root_of_chordY_zero
    (A := A) (B := B) (e := e) (x := z) (a := a)
    (hroot := hroot) (hderiv := hderiv) hposRight hz ha hDz hyz
  have hcancel :
      lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight z hz =
        lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx := by
    apply add_right_cancel
      (b := upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    exact hzroot.trans hxroot.symm
  exact lowerRightKerPoint_injective_x
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    hposRight hz hx hcancel

theorem lower_upper_chordX_eq_root_of_chordY_zero
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0) :
    chordX A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = e := by
  let P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha
  have hrootsum := lowerRightKerPoint_add_upperRightKerPoint_eq_root_of_chordY_zero
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
  have hxy :
      ¬(x = a ∧
        -√(shortCubic A B x) =
          WeierstrassCurve.Affine.negY (shortW A B) a (√(shortCubic A B a))) := by
    intro h
    exact hD (sub_eq_zero.mpr h.1)
  have hsum := WeierstrassCurve.Affine.Point.add_some
    (W := shortW A B) (x₁ := x) (x₂ := a)
    (y₁ := -√(shortCubic A B x)) (y₂ := √(shortCubic A B a)) hxy
    (h₁ := shortW_nonsingular_neg_sqrt_of_pos
      (A := A) (B := B) (x := x) (hposRight hx))
    (h₂ := shortW_nonsingular_sqrt_of_pos
      (A := A) (B := B) (x := a) (hposRight ha))
  have hrootPoint :
      WeierstrassCurve.Affine.Point.some x (-√(shortCubic A B x))
          (shortW_nonsingular_neg_sqrt_of_pos
            (A := A) (B := B) (x := x) (hposRight hx)) +
        WeierstrassCurve.Affine.Point.some a (√(shortCubic A B a))
          (shortW_nonsingular_sqrt_of_pos
            (A := A) (B := B) (x := a) (hposRight ha)) =
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv).1 := by
    simpa [P, Q, lowerRightKerPoint, upperRightKerPoint,
      lowerRightPoint, upperRightPoint] using congrArg Subtype.val hrootsum
  have heqPoint := hrootPoint.symm.trans hsum
  change
    WeierstrassCurve.Affine.Point.some e 0
        (shortW_nonsingular_root_of_deriv_pos
          (A := A) (B := B) (e := e) hroot hderiv) =
      _ at heqPoint
  rw [WeierstrassCurve.Affine.Point.some.injEq] at heqPoint
  have hxcoord := heqPoint.1
  have hxadd := shortW_addX_eq_chordX
    (A := A) (B := B) (x := x) (y := -√(shortCubic A B x))
    (a := a) (b := √(shortCubic A B a)) hD
  rw [hxadd] at hxcoord
  exact hxcoord.symm

theorem eventually_lower_upper_chordY_ne_zero_t2
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0) :
    ∀ᶠ z : ℝ in 𝓝[≠] x,
      chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
  have hneA : {z : ℝ | z - a ≠ 0} ∈ 𝓝[≠] x := by
    exact nhdsWithin_le_nhds
      (by
        filter_upwards [eventually_ne_nhds (sub_ne_zero.mp hD)] with z hz
        exact sub_ne_zero.mpr hz)
  filter_upwards
    [self_mem_nhdsWithin,
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id : Tendsto (fun z : ℝ => z)
        (𝓝[≠] x) (𝓝 x)) (Ioi_mem_nhds hx),
      hneA]
    with z hz_ne hzright hzD hyz
  have hzx : z ≠ x := by simpa using hz_ne
  have huniq := lower_upper_chordY_zero_unique
    (A := A) (B := B) (e := e) (x := x) (z := z) (a := a)
    (hroot := hroot) (hderiv := hderiv) hposRight hx hzright ha hD hzD hy3zero hyz
  exact hzx huniq

theorem tendsto_lowerThetaDefectAtX_upperRight_t2_nhdsNE
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0) :
    Tendsto
      (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha))
      (𝓝[≠] x)
      (𝓝 (lowerThetaDefectAtX (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) x)) := by
  let x3f : ℝ → ℝ :=
    fun z => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let y3f : ℝ → ℝ :=
    fun z => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let T : AddCircle (thetaPeriod A B e) :=
    ((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e))
  let qtheta : AddCircle (thetaPeriod A B e) :=
    ((-sigma A B a : ℝ) : AddCircle (thetaPeriod A B e))
  let targetExpr : AddCircle (thetaPeriod A B e) :=
    T - ((sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)) - qtheta
  let posExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => ((-sigma A B (x3f z) - sigma A B z - (-sigma A B a) : ℝ) :
      AddCircle (thetaPeriod A B e))
  let negExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => ((sigma A B (x3f z) - sigma A B z - (-sigma A B a) : ℝ) :
      AddCircle (thetaPeriod A B e))
  let branchExpr : ℝ → AddCircle (thetaPeriod A B e) :=
    fun z => if 0 ≤ y3f z then posExpr z else negExpr z
  have hx3eq : x3f x = e := by
    simpa [x3f] using
      lower_upper_chordX_eq_root_of_chordY_zero
        (A := A) (B := B) (e := e) (x := x) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
  have hcx_nhds : Tendsto x3f (𝓝[≠] x) (𝓝 e) := by
    have hcont := continuousAt_lower_upper_chordX
      (A := A) (B := B) (x := x) (a := a) hD
    simpa [x3f, hx3eq] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hy_ne_event : ∀ᶠ z : ℝ in 𝓝[≠] x, y3f z ≠ 0 := by
    simpa [y3f] using
      eventually_lower_upper_chordY_ne_zero_t2
        (A := A) (B := B) (e := e) (x := x) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
  have hzright_event : {z : ℝ | e < z} ∈ 𝓝[≠] x :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id : Tendsto (fun z : ℝ => z)
      (𝓝[≠] x) (𝓝 x)) (Ioi_mem_nhds hx)
  have hzD_event : {z : ℝ | z - a ≠ 0} ∈ 𝓝[≠] x := by
    exact nhdsWithin_le_nhds
      (by
        filter_upwards [eventually_ne_nhds (sub_ne_zero.mp hD)] with z hz
        exact sub_ne_zero.mpr hz)
  have hx3gt_event : ∀ᶠ z : ℝ in 𝓝[≠] x, e < x3f z := by
    filter_upwards [hy_ne_event, hzright_event, hzD_event] with z hyne hzright hzD
    exact lower_upper_chordX_gt_root_of_chordY_ne_zero
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hzright ha hzD (by simpa [x3f, y3f] using hyne)
  have hcx_within : Tendsto x3f (𝓝[≠] x) (𝓝[>] e) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcx_nhds, hx3gt_event⟩
  have hx3_pos_mk :
      Tendsto (fun z : ℝ => ((sigma A B (x3f z) : ℝ) :
        AddCircle (thetaPeriod A B e))) (𝓝[≠] x) (𝓝 T) := by
    change Tendsto
      ((fun u : ℝ => ((sigma A B u : ℝ) : AddCircle (thetaPeriod A B e))) ∘ x3f)
        (𝓝[≠] x) (𝓝 T)
    simpa [T] using
      (tendsto_addCircle_sigma_nhdsGT_root
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight).comp hcx_within
  have hx3_neg_mk :
      Tendsto (fun z : ℝ => ((-sigma A B (x3f z) : ℝ) :
        AddCircle (thetaPeriod A B e))) (𝓝[≠] x) (𝓝 T) := by
    change Tendsto
      ((fun u : ℝ => ((-sigma A B u : ℝ) : AddCircle (thetaPeriod A B e))) ∘ x3f)
        (𝓝[≠] x) (𝓝 T)
    simpa [T] using
      (tendsto_addCircle_neg_sigma_nhdsGT_root
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight).comp hcx_within
  have hsigma_z : Tendsto (fun z : ℝ => sigma A B z) (𝓝[≠] x) (𝓝 (sigma A B x)) := by
    exact (sigma_hasDerivAt_of_right
      (A := A) (B := B) (e := e) hroot hderiv hposRight hx).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds
  have hz_mk :
      Tendsto (fun z : ℝ => ((sigma A B z : ℝ) :
        AddCircle (thetaPeriod A B e))) (𝓝[≠] x)
        (𝓝 (((sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)))) := by
    exact (AddCircle.continuous_mk' (thetaPeriod A B e)).tendsto (sigma A B x)
      |>.comp hsigma_z
  have hqconst : Tendsto (fun _ : ℝ => qtheta) (𝓝[≠] x) (𝓝 qtheta) :=
    tendsto_const_nhds
  have hposExpr : Tendsto posExpr (𝓝[≠] x) (𝓝 targetExpr) := by
    simpa [posExpr, targetExpr, T, qtheta, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using
      (hx3_neg_mk.sub hz_mk).sub hqconst
  have hnegExpr : Tendsto negExpr (𝓝[≠] x) (𝓝 targetExpr) := by
    simpa [negExpr, targetExpr, T, qtheta, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using
      (hx3_pos_mk.sub hz_mk).sub hqconst
  have hbranch : Tendsto branchExpr (𝓝[≠] x) (𝓝 targetExpr) := by
    intro U hU
    have hpU := hposExpr hU
    have hnU := hnegExpr hU
    change {z : ℝ | posExpr z ∈ U} ∈ 𝓝[≠] x at hpU
    change {z : ℝ | negExpr z ∈ U} ∈ 𝓝[≠] x at hnU
    change {z : ℝ | branchExpr z ∈ U} ∈ 𝓝[≠] x
    filter_upwards [hpU, hnU] with z hzpos hzneg
    by_cases hsign : 0 ≤ y3f z
    · simpa [branchExpr, hsign] using hzpos
    · simpa [branchExpr, hsign] using hzneg
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =ᶠ[𝓝[≠] x]
        branchExpr := by
    filter_upwards [hy_ne_event, hx3gt_event, hzright_event, hzD_event]
      with z hyne hx3 hzright hzD
    by_cases hsign : 0 ≤ y3f z
    · have hypos : 0 < y3f z := lt_of_le_of_ne hsign hyne.symm
      have hformula := thetaDefect_lowerRight_upperRight_of_chordY_pos
        (A := A) (B := B) (e := e) (x := z) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hzright ha hzD
        (by simpa [x3f] using hx3)
        (by simpa [y3f] using hypos)
      rw [lowerThetaDefectAtX, dif_pos (show e < z from hzright)]
      simpa [lowerThetaDefectAtX, hzright, branchExpr, posExpr, x3f, y3f, hsign]
        using hformula
    · have hyneg : y3f z < 0 := not_le.mp hsign
      have hformula := thetaDefect_lowerRight_upperRight_of_chordY_neg
        (A := A) (B := B) (e := e) (x := z) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hzright ha hzD
        (by simpa [x3f] using hx3)
        (by simpa [y3f] using hyneg)
      rw [lowerThetaDefectAtX, dif_pos (show e < z from hzright)]
      simpa [lowerThetaDefectAtX, hzright, branchExpr, negExpr, x3f, y3f, hsign]
        using hformula
  have hsumroot := lowerRightKerPoint_add_upperRightKerPoint_eq_root_of_chordY_zero
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
  have htarget :
      targetExpr =
        lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) x := by
    rw [lowerThetaDefectAtX, dif_pos hx]
    simp [targetExpr, T, qtheta, thetaDefect, thetaPeriod, hsumroot,
      sub_eq_add_neg, add_assoc]
  have hlim := Tendsto.congr' heq.symm hbranch
  simpa [htarget] using hlim

theorem lowerThetaDefectOnIoi_eventually_eq_of_chordY_pos
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3pos :
      0 < chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a))) :
    ∀ᶠ y : Set.Ioi e in 𝓝 (⟨x, hx⟩ : Set.Ioi e),
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) y =
        lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) ⟨x, hx⟩ := by
  let x3f : ℝ → ℝ :=
    fun z => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let y3f : ℝ → ℝ :=
    fun z => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  have hx3 : e < x3f x := by
    dsimp [x3f]
    exact lower_upper_chordX_gt_root_of_chordY_ne_zero
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx ha hD hy3pos.ne'
  have hUx : {z : ℝ | e < z ∧ z - a ≠ 0 ∧ e < x3f z ∧ 0 < y3f z} ∈ 𝓝 x := by
    have hright : {z : ℝ | e < z} ∈ 𝓝 x := Ioi_mem_nhds hx
    have hne : {z : ℝ | z - a ≠ 0} ∈ 𝓝 x := by
      filter_upwards [eventually_ne_nhds (sub_ne_zero.mp hD)] with z hz
      exact sub_ne_zero.mpr hz
    have hx3mem : {z : ℝ | e < x3f z} ∈ 𝓝 x := by
      change
        ((fun z : ℝ =>
          chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) ⁻¹' Ioi e) ∈ 𝓝 x
      exact
        (continuousAt_lower_upper_chordX (A := A) (B := B) (x := x) (a := a) hD)
          (Ioi_mem_nhds hx3)
    have hy3mem : {z : ℝ | 0 < y3f z} ∈ 𝓝 x := by
      change
        ((fun z : ℝ =>
          chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) ⁻¹' Ioi 0) ∈ 𝓝 x
      exact
        (continuousAt_lower_upper_chordY (A := A) (B := B) (x := x) (a := a) hD)
          (Ioi_mem_nhds (by simpa [y3f] using hy3pos))
    filter_upwards [hright, hne, hx3mem, hy3mem] with z hz hza hz3 hyz3
    exact ⟨hz, hza, hz3, hyz3⟩
  rcases Metric.mem_nhds_iff.mp hUx with ⟨δ, hδ, hδU⟩
  let s : Set ℝ := Metric.ball x δ
  have hsopen : IsOpen s := Metric.isOpen_ball
  have hspre : IsPreconnected s := by
    rw [show s = Ioo (x - δ) (x + δ) by
      dsimp [s]
      exact Real.ball_eq_Ioo x δ]
    exact isPreconnected_Ioo
  have hxs : x ∈ s := by
    simp [s, hδ]
  have hball_nhds : s ∈ 𝓝 x := Metric.ball_mem_nhds x hδ
  have hball_sub :
      {y : Set.Ioi e | (y : ℝ) ∈ s} ∈ 𝓝 (⟨x, hx⟩ : Set.Ioi e) :=
    continuous_subtype_val.continuousAt hball_nhds
  filter_upwards [hball_sub] with y hy
  have hconst := thetaDefect_lowerRight_some_const_on_of_chordY_pos
    (A := A) (B := B) (e := e) (a := a) (b := √(shortCubic A B a))
    (qtheta := -sigma A B a) (s := s)
    hsopen hspre hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos
      (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint
      (A := A) (B := B) (e := e) hposRight ha)
    (fun z hz => (hδU hz).1)
    (fun z hz => (hδU hz).2.1)
    (fun z hz => (hδU hz).2.2.1)
    (fun z hz => (hδU hz).2.2.2)
    hxs hy
  simpa [lowerThetaDefectOnIoi] using hconst.symm

theorem lowerThetaDefectOnIoi_eventually_eq_of_chordY_neg
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3neg :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) < 0) :
    ∀ᶠ y : Set.Ioi e in 𝓝 (⟨x, hx⟩ : Set.Ioi e),
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) y =
        lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) ⟨x, hx⟩ := by
  let x3f : ℝ → ℝ :=
    fun z => chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  let y3f : ℝ → ℝ :=
    fun z => chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))
  have hx3 : e < x3f x := by
    dsimp [x3f]
    exact lower_upper_chordX_gt_root_of_chordY_ne_zero
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx ha hD hy3neg.ne
  have hUx : {z : ℝ | e < z ∧ z - a ≠ 0 ∧ e < x3f z ∧ y3f z < 0} ∈ 𝓝 x := by
    have hright : {z : ℝ | e < z} ∈ 𝓝 x := Ioi_mem_nhds hx
    have hne : {z : ℝ | z - a ≠ 0} ∈ 𝓝 x := by
      filter_upwards [eventually_ne_nhds (sub_ne_zero.mp hD)] with z hz
      exact sub_ne_zero.mpr hz
    have hx3mem : {z : ℝ | e < x3f z} ∈ 𝓝 x := by
      change
        ((fun z : ℝ =>
          chordX A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) ⁻¹' Ioi e) ∈ 𝓝 x
      exact
        (continuousAt_lower_upper_chordX (A := A) (B := B) (x := x) (a := a) hD)
          (Ioi_mem_nhds hx3)
    have hy3mem : {z : ℝ | y3f z < 0} ∈ 𝓝 x := by
      change
        ((fun z : ℝ =>
          chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a))) ⁻¹' Iio 0) ∈ 𝓝 x
      exact
        (continuousAt_lower_upper_chordY (A := A) (B := B) (x := x) (a := a) hD)
          (Iio_mem_nhds (by simpa [y3f] using hy3neg))
    filter_upwards [hright, hne, hx3mem, hy3mem] with z hz hza hz3 hyz3
    exact ⟨hz, hza, hz3, hyz3⟩
  rcases Metric.mem_nhds_iff.mp hUx with ⟨δ, hδ, hδU⟩
  let s : Set ℝ := Metric.ball x δ
  have hsopen : IsOpen s := Metric.isOpen_ball
  have hspre : IsPreconnected s := by
    rw [show s = Ioo (x - δ) (x + δ) by
      dsimp [s]
      exact Real.ball_eq_Ioo x δ]
    exact isPreconnected_Ioo
  have hxs : x ∈ s := by
    simp [s, hδ]
  have hball_nhds : s ∈ 𝓝 x := Metric.ball_mem_nhds x hδ
  have hball_sub :
      {y : Set.Ioi e | (y : ℝ) ∈ s} ∈ 𝓝 (⟨x, hx⟩ : Set.Ioi e) :=
    continuous_subtype_val.continuousAt hball_nhds
  filter_upwards [hball_sub] with y hy
  have hconst := thetaDefect_lowerRight_some_const_on_of_chordY_neg
    (A := A) (B := B) (e := e) (a := a) (b := √(shortCubic A B a))
    (qtheta := -sigma A B a) (s := s)
    hsopen hspre hposRight
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)
    (hQ := shortW_nonsingular_sqrt_of_pos
      (A := A) (B := B) (x := a) (hposRight ha))
    rfl
    (thetaCandidate_upperRightKerPoint
      (A := A) (B := B) (e := e) hposRight ha)
    (fun z hz => (hδU hz).1)
    (fun z hz => (hδU hz).2.1)
    (fun z hz => (hδU hz).2.2.1)
    (fun z hz => (hδU hz).2.2.2)
    hxs hy
  simpa [lowerThetaDefectOnIoi] using hconst.symm

theorem lowerThetaDefectOnIoi_eventually_eq_of_clean
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3_ne :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) ≠ 0) :
    ∀ᶠ y : Set.Ioi e in 𝓝 (⟨x, hx⟩ : Set.Ioi e),
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) y =
        lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) ⟨x, hx⟩ := by
  rcases lt_or_gt_of_ne hy3_ne.symm with hy3pos | hy3neg
  · exact lowerThetaDefectOnIoi_eventually_eq_of_chordY_pos
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx ha hD hy3pos
  · exact lowerThetaDefectOnIoi_eventually_eq_of_chordY_neg
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx ha hD hy3neg

theorem lowerThetaDefectOnIoi_eq_on_clean_preconnected
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a)
    {s : Set ℝ}
    (hsconn : IsPreconnected s)
    (hsright : ∀ z ∈ s, e < z)
    (hsne : ∀ z ∈ s, z - a ≠ 0)
    (hsy :
      ∀ z ∈ s,
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0)
    {x y : ℝ}
    (hx : x ∈ s)
    (hy : y ∈ s) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨x, hsright x hx⟩ =
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨y, hsright y hy⟩ := by
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha)
  let g : s → AddCircle (thetaPeriod A B e) :=
    fun z => F ⟨(z : ℝ), hsright z z.2⟩
  have hloc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hzright : e < (z : ℝ) := hsright z z.2
    have hclean :
        ∀ᶠ y : Set.Ioi e in 𝓝 (⟨(z : ℝ), hzright⟩ : Set.Ioi e),
          F y = F ⟨(z : ℝ), hzright⟩ := by
      simpa [F] using
        lowerThetaDefectOnIoi_eventually_eq_of_clean
          (A := A) (B := B) (e := e) (x := (z : ℝ)) (a := a)
          (hroot := hroot) (hderiv := hderiv) hposRight hzright ha
          (hsne z z.2)
          (hsy z z.2)
    have hmap :
        Tendsto (fun y : s => (⟨(y : ℝ), hsright y y.2⟩ : Set.Ioi e))
          (𝓝 z) (𝓝 (⟨(z : ℝ), hzright⟩ : Set.Ioi e)) :=
      (Continuous.subtype_mk continuous_subtype_val (fun y : s => hsright y y.2)).continuousAt
    filter_upwards [hmap hclean] with y hy
    simpa [g] using hy
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace hsconn
  simpa [g, F] using
    hloc.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : s) (⟨y, hy⟩ : s)

theorem lowerThetaDefectOnIoi_eq_on_t2_right_interval
    {A B e x a ε y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0)
    (hε : 0 < ε)
    (hsne : ∀ z ∈ Ioo x (x + ε), z - a ≠ 0)
    (hsy :
      ∀ z ∈ Ioo x (x + ε),
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0)
    (hy : y ∈ Ioo x (x + ε))
    (hyright : e < y) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨y, hyright⟩ =
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨x, hx⟩ := by
  let Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q
  have hlim :
      Tendsto (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q)
        (𝓝[>] x)
        (𝓝 (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q x)) := by
    exact (tendsto_lowerThetaDefectAtX_upperRight_t2_nhdsNE
      (A := A) (B := B) (e := e) (x := x) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero).mono_left
        (nhdsWithin_mono x (by
          intro z hz
          exact (ne_of_gt hz : z ≠ x)))
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q =ᶠ[𝓝[>] x]
        fun _ : ℝ => F ⟨y, hyright⟩ := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : x + ε > x)] with z hz
    have hzright : e < z := by linarith [hx, hz.1]
    have hconst := lowerThetaDefectOnIoi_eq_on_clean_preconnected
      (A := A) (B := B) (e := e) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight ha
      (s := Ioo x (x + ε))
      isPreconnected_Ioo
      (fun w hw => by linarith [hx, hw.1])
      hsne
      hsy
      (x := z) (y := y) hz hy
    simpa [F, Q, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hzright] using hconst
  have hlim_const :
      Tendsto (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q)
        (𝓝[>] x) (𝓝 (F ⟨y, hyright⟩)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim hlim_const
  have hxF :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q x =
        F ⟨x, hx⟩ := by
    simp [F, Q, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hx]
  exact huniq.symm.trans hxF

theorem lowerThetaDefectOnIoi_eq_on_t2_left_interval
    {A B e x a ε y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0)
    (hε : 0 < ε)
    (hεray : ε < x - e)
    (hsne : ∀ z ∈ Ioo (x - ε) x, z - a ≠ 0)
    (hsy :
      ∀ z ∈ Ioo (x - ε) x,
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0)
    (hy : y ∈ Ioo (x - ε) x)
    (hyright : e < y) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨y, hyright⟩ =
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨x, hx⟩ := by
  let Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv :=
    upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight Q
  have hlim :
      Tendsto (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q)
        (𝓝[<] x)
        (𝓝 (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q x)) := by
    exact (tendsto_lowerThetaDefectAtX_upperRight_t2_nhdsNE
      (A := A) (B := B) (e := e) (x := x) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero).mono_left
        (nhdsWithin_mono x (by
          intro z hz
          exact (ne_of_lt hz : z ≠ x)))
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q =ᶠ[𝓝[<] x]
        fun _ : ℝ => F ⟨y, hyright⟩ := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith : x - ε < x)] with z hz
    have hzright : e < z := by linarith [hz.1, hεray]
    have hconst := lowerThetaDefectOnIoi_eq_on_clean_preconnected
      (A := A) (B := B) (e := e) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight ha
      (s := Ioo (x - ε) x)
      isPreconnected_Ioo
      (fun w hw => by linarith [hw.1, hεray])
      hsne
      hsy
      (x := z) (y := y) hz hy
    simpa [F, Q, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hzright] using hconst
  have hlim_const :
      Tendsto (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q)
        (𝓝[<] x) (𝓝 (F ⟨y, hyright⟩)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim hlim_const
  have hxF :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight Q x =
        F ⟨x, hx⟩ := by
    simp [F, Q, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hx]
  exact huniq.symm.trans hxF

theorem lowerThetaDefectOnIoi_eventually_eq_t2
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x)
    (ha : e < a)
    (hD : x - a ≠ 0)
    (hy3zero :
      chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0) :
    ∀ᶠ y : Set.Ioi e in 𝓝 (⟨x, hx⟩ : Set.Ioi e),
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) y =
        lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) ⟨x, hx⟩ := by
  have habs_pos : 0 < |x - a| := abs_pos.mpr hD
  let ε : ℝ := min ((x - e) / 2) (|x - a| / 2)
  have hhalf_ray : 0 < (x - e) / 2 := by linarith
  have hhalf_a : 0 < |x - a| / 2 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hhalf_ray hhalf_a
  have hε_le_ray_half : ε ≤ (x - e) / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_a_half : ε ≤ |x - a| / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  have hεray : ε < x - e := by linarith
  have hεa : ε < |x - a| := by linarith
  have hsneR : ∀ z ∈ Ioo x (x + ε), z - a ≠ 0 := by
    intro z hz hza
    have hzaeq : z = a := sub_eq_zero.mp hza
    subst z
    have hlt : |x - a| < ε := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hz.1)]
      linarith [hz.2]
    linarith
  have hsneL : ∀ z ∈ Ioo (x - ε) x, z - a ≠ 0 := by
    intro z hz hza
    have hzaeq : z = a := sub_eq_zero.mp hza
    subst z
    have hlt : |x - a| < ε := by
      rw [abs_sub_comm, abs_of_neg (sub_neg.mpr hz.2)]
      linarith [hz.1]
    linarith
  have hsyR :
      ∀ z ∈ Ioo x (x + ε),
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
    intro z hz hyz
    have huniq := lower_upper_chordY_zero_unique
      (A := A) (B := B) (e := e) (x := x) (z := z) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight hx (by linarith [hx, hz.1])
      ha hD (hsneR z hz) hy3zero hyz
    exact (ne_of_gt hz.1) huniq
  have hsyL :
      ∀ z ∈ Ioo (x - ε) x,
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
    intro z hz hyz
    have huniq := lower_upper_chordY_zero_unique
      (A := A) (B := B) (e := e) (x := x) (z := z) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight hx (by linarith [hz.1, hεray])
      ha hD (hsneL z hz) hy3zero hyz
    exact (ne_of_lt hz.2) huniq
  have hball :
      {y : Set.Ioi e | (y : ℝ) ∈ Metric.ball x ε} ∈
        𝓝 (⟨x, hx⟩ : Set.Ioi e) :=
    continuous_subtype_val.continuousAt (Metric.ball_mem_nhds x hε)
  filter_upwards [hball] with y hyball
  have habs : |(y : ℝ) - x| < ε := by
    have hdist : dist (y : ℝ) x < ε := by
      simpa [Metric.mem_ball] using hyball
    simpa [Real.dist_eq] using hdist
  by_cases hyx : (y : ℝ) = x
  · have hy_eq : y = (⟨x, hx⟩ : Set.Ioi e) := Subtype.ext hyx
    simp [hy_eq]
  · rcases lt_or_gt_of_ne hyx with hylt | hygt
    · have hyI : (y : ℝ) ∈ Ioo (x - ε) x := by
        constructor
        · have hleft := (abs_sub_lt_iff.mp habs).2
          linarith
        · exact hylt
      exact lowerThetaDefectOnIoi_eq_on_t2_left_interval
        (A := A) (B := B) (e := e) (x := x) (a := a) (ε := ε) (y := (y : ℝ))
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
        hε hεray hsneL hsyL hyI y.2
    · have hyI : (y : ℝ) ∈ Ioo x (x + ε) := by
        constructor
        · exact hygt
        · have hright := (abs_sub_lt_iff.mp habs).1
          linarith
      exact lowerThetaDefectOnIoi_eq_on_t2_right_interval
        (A := A) (B := B) (e := e) (x := x) (a := a) (ε := ε) (y := (y : ℝ))
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
        hε hsneR hsyR hyI y.2

theorem lowerThetaDefectOnIoi_eq_zero_on_anchor_right_interval
    {A B e a ε y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a)
    (hε : 0 < ε)
    (hsy :
      ∀ z ∈ Ioo a (a + ε),
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0)
    (hy : y ∈ Ioo a (a + ε))
    (hyright : e < y) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨y, hyright⟩ = 0 := by
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha)
  have hlim0 :
      Tendsto
        (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha))
        (𝓝[>] a) (𝓝 0) := by
    exact (tendsto_lowerThetaDefectAtX_upperRight_vertical_nhdsNE
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight ha).mono_left
        (nhdsWithin_mono a (by
          intro z hz
          exact (ne_of_gt hz : z ≠ a)))
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =ᶠ[𝓝[>] a]
        fun _ : ℝ => F ⟨y, hyright⟩ := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : a + ε > a)] with z hz
    have hzright : e < z := by linarith [ha, hz.1]
    have hconst := lowerThetaDefectOnIoi_eq_on_clean_preconnected
      (A := A) (B := B) (e := e) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight ha
      (s := Ioo a (a + ε))
      isPreconnected_Ioo
      (fun w hw => by linarith [ha, hw.1])
      (fun w hw => by linarith [hw.1])
      hsy
      (x := z) (y := y) hz hy
    simpa [F, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hzright] using hconst
  have hlim_const :
      Tendsto
        (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha))
        (𝓝[>] a) (𝓝 (F ⟨y, hyright⟩)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim0 hlim_const
  exact huniq.symm

theorem lowerThetaDefectOnIoi_eq_zero_on_anchor_left_interval
    {A B e a ε y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a)
    (hε : 0 < ε)
    (hεray : ε < a - e)
    (hsy :
      ∀ z ∈ Ioo (a - ε) a,
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0)
    (hy : y ∈ Ioo (a - ε) a)
    (hyright : e < y) :
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        ⟨y, hyright⟩ = 0 := by
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha)
  have hlim0 :
      Tendsto
        (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha))
        (𝓝[<] a) (𝓝 0) := by
    exact (tendsto_lowerThetaDefectAtX_upperRight_vertical_nhdsNE
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight ha).mono_left
        (nhdsWithin_mono a (by
          intro z hz
          exact (ne_of_lt hz : z ≠ a)))
  have heq :
      lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =ᶠ[𝓝[<] a]
        fun _ : ℝ => F ⟨y, hyright⟩ := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith : a - ε < a)] with z hz
    have hzright : e < z := by linarith [hz.1, hεray]
    have hconst := lowerThetaDefectOnIoi_eq_on_clean_preconnected
      (A := A) (B := B) (e := e) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight ha
      (s := Ioo (a - ε) a)
      isPreconnected_Ioo
      (fun w hw => by linarith [hw.1, hεray])
      (fun w hw => by linarith [hw.2])
      hsy
      (x := z) (y := y) hz hy
    simpa [F, lowerThetaDefectAtX, lowerThetaDefectOnIoi, hzright] using hconst
  have hlim_const :
      Tendsto
        (lowerThetaDefectAtX (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha))
        (𝓝[<] a) (𝓝 (F ⟨y, hyright⟩)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim0 hlim_const
  exact huniq.symm

theorem lowerThetaDefectOnIoi_eventually_eq_anchor
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    ∀ᶠ y : Set.Ioi e in 𝓝 (⟨a, ha⟩ : Set.Ioi e),
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) y =
        lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) ⟨a, ha⟩ := by
  let F : Set.Ioi e → AddCircle (thetaPeriod A B e) :=
    lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
      (upperRightKerPoint (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight a ha)
  have hanchor : F ⟨a, ha⟩ = 0 := by
    have hdef :
        thetaDefect (A := A) (B := B) (e := e)
            (lowerRightKerPoint (A := A) (B := B) (e := e)
              (hroot := hroot) (hderiv := hderiv) hposRight a ha)
            (upperRightKerPoint (A := A) (B := B) (e := e)
              (hroot := hroot) (hderiv := hderiv) hposRight a ha) = 0 := by
      have hneg := neg_upperRightKerPoint_eq_lowerRightKerPoint
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight ha
      have htheta_neg :
          thetaCandidate (A := A) (B := B) (e := e)
              (-upperRightKerPoint (A := A) (B := B) (e := e)
                (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
            thetaCandidate (A := A) (B := B) (e := e)
              (lowerRightKerPoint (A := A) (B := B) (e := e)
                (hroot := hroot) (hderiv := hderiv) hposRight a ha) := by
        rw [hneg]
      rw [← hneg]
      simp [thetaDefect, thetaPeriod, htheta_neg]
    simpa [F, lowerThetaDefectOnIoi] using hdef
  have hYevent :
      {z : ℝ |
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0}
        ∈ 𝓝[≠] a :=
    eventually_lower_upper_chordY_ne_zero_vertical
      (A := A) (B := B) (e := e) hposRight ha
  rcases Metric.mem_nhdsWithin_iff.mp hYevent with ⟨δY, hδY, hδYsub⟩
  let ε : ℝ := min δY ((a - e) / 2)
  have hhalf_pos : 0 < (a - e) / 2 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hδY hhalf_pos
  have hε_le_δY : ε ≤ δY := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_half : ε ≤ (a - e) / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  have hεray : ε < a - e := by linarith
  have hsyR :
      ∀ z ∈ Ioo a (a + ε),
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
    intro z hz
    apply hδYsub
    constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      have habs : |z - a| < ε := by
        rw [abs_of_pos (sub_pos.mpr hz.1)]
        linarith [hz.2]
      exact lt_of_lt_of_le habs hε_le_δY
    · exact by simpa using (ne_of_gt hz.1 : z ≠ a)
  have hsyL :
      ∀ z ∈ Ioo (a - ε) a,
        chordY A z (-√(shortCubic A B z)) a (√(shortCubic A B a)) ≠ 0 := by
    intro z hz
    apply hδYsub
    constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      have habs : |z - a| < ε := by
        rw [abs_of_neg (sub_neg.mpr hz.2)]
        linarith [hz.1]
      exact lt_of_lt_of_le habs hε_le_δY
    · exact by simpa using (ne_of_lt hz.2 : z ≠ a)
  have hball :
      {y : Set.Ioi e | (y : ℝ) ∈ Metric.ball a ε} ∈
        𝓝 (⟨a, ha⟩ : Set.Ioi e) :=
    continuous_subtype_val.continuousAt (Metric.ball_mem_nhds a hε)
  filter_upwards [hball] with y hyball
  have habs : |(y : ℝ) - a| < ε := by
    have hdist : dist (y : ℝ) a < ε := by
      simpa [Metric.mem_ball] using hyball
    simpa [Real.dist_eq] using hdist
  by_cases hya : (y : ℝ) = a
  · have hy_eq : y = (⟨a, ha⟩ : Set.Ioi e) := Subtype.ext hya
    simp [hy_eq]
  · rcases lt_or_gt_of_ne hya with hylt | hygt
    · have hyI : (y : ℝ) ∈ Ioo (a - ε) a := by
        constructor
        · have hleft := (abs_sub_lt_iff.mp habs).2
          linarith
        · exact hylt
      have hzero := lowerThetaDefectOnIoi_eq_zero_on_anchor_left_interval
        (A := A) (B := B) (e := e) (a := a) (ε := ε) (y := (y : ℝ))
        (hroot := hroot) (hderiv := hderiv) hposRight ha hε hεray hsyL hyI y.2
      exact (by simpa [F] using hzero.trans hanchor.symm)
    · have hyI : (y : ℝ) ∈ Ioo a (a + ε) := by
        constructor
        · exact hygt
        · have hright := (abs_sub_lt_iff.mp habs).1
          linarith
      have hzero := lowerThetaDefectOnIoi_eq_zero_on_anchor_right_interval
        (A := A) (B := B) (e := e) (a := a) (ε := ε) (y := (y : ℝ))
        (hroot := hroot) (hderiv := hderiv) hposRight ha hε hsyR hyI y.2
      exact (by simpa [F] using hzero.trans hanchor.symm)

@[simp]
theorem thetaDefect_lowerRight_upperRight_anchor
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    thetaDefect (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) = 0 := by
  have hneg := neg_upperRightKerPoint_eq_lowerRightKerPoint
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    hposRight ha
  have htheta_neg :
      thetaCandidate (A := A) (B := B) (e := e)
          (-upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
        thetaCandidate (A := A) (B := B) (e := e)
          (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) := by
    rw [hneg]
  rw [← hneg]
  simp [thetaDefect, thetaPeriod, htheta_neg]

theorem lowerThetaDefectOnIoi_upperRight_isLocallyConstant
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (ha : e < a) :
    IsLocallyConstant
      (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rcases x with ⟨x, hx⟩
  by_cases hxa : x = a
  · subst x
    simpa using
      lowerThetaDefectOnIoi_eventually_eq_anchor
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight ha
  · have hD : x - a ≠ 0 := sub_ne_zero.mpr hxa
    by_cases hy3zero :
        chordY A x (-√(shortCubic A B x)) a (√(shortCubic A B a)) = 0
    · exact lowerThetaDefectOnIoi_eventually_eq_t2
        (A := A) (B := B) (e := e) (x := x) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero
    · exact lowerThetaDefectOnIoi_eventually_eq_of_clean
        (A := A) (B := B) (e := e) (x := x) (a := a)
        (hroot := hroot) (hderiv := hderiv) hposRight hx ha hD hy3zero

theorem lowerThetaDefectOnIoi_eq_zero_of_isLocallyConstant_anchor
    {A B e a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    {ha : e < a}
    (hloc : IsLocallyConstant
      (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha))) :
    ∀ x : Set.Ioi e,
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) x = 0 := by
  intro x
  let anchor : Set.Ioi e := ⟨a, ha⟩
  have hconst := lowerThetaDefectOnIoi_eq_of_isLocallyConstant
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    (hposRight := hposRight)
    (Q := upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha) hloc x anchor
  have hanchor :
      lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) anchor = 0 := by
    simp [lowerThetaDefectOnIoi, anchor]
  exact hconst.trans hanchor

theorem thetaCandidate_mixed_additive_of_isLocallyConstant
    {A B e x a : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    (hx : e < x)
    (ha : e < a)
    (hloc : IsLocallyConstant
      (lowerThetaDefectOnIoi (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha))) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx +
        upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
      thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight a ha) := by
  have hzero := lowerThetaDefectOnIoi_eq_zero_of_isLocallyConstant_anchor
    (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
    (hposRight := hposRight) (ha := ha) hloc ⟨x, hx⟩
  exact (thetaDefect_eq_zero_iff (A := A) (B := B) (e := e)
    (lowerRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight x hx)
    (upperRightKerPoint (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight a ha)).1
    (by simpa [lowerThetaDefectOnIoi] using hzero)

theorem thetaCandidate_mixed_additive
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    {x a : ℝ} (hx : e < x) (ha : e < a) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) =
      thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight a ha) := by
  exact thetaCandidate_mixed_additive_of_isLocallyConstant
    (A := A) (B := B) (e := e) (x := x) (a := a)
    (hroot := hroot) (hderiv := hderiv) (hposRight := hposRight) hx ha
    (lowerThetaDefectOnIoi_upperRight_isLocallyConstant
      (A := A) (B := B) (e := e) (a := a)
      (hroot := hroot) (hderiv := hderiv) hposRight ha)

end

end MazurProof.RealTopology
