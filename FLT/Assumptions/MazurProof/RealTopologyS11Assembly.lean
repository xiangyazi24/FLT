import FLT.Assumptions.MazurProof.RealTopologyS9
import FLT.Assumptions.MazurProof.RealTopologyS6
import FLT.Assumptions.MazurProof.RealTopologyS5
import FLT.Assumptions.MazurProof.RealTopologyS10T2
import FLT.Assumptions.MazurProof.RealTopologyS10Mixed

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology
open scoped Topology

namespace MazurProof.RealTopology

noncomputable section

/-!
S11 assembles `ThetaCandidateAdditive` from the two analytic inputs:
translation by the branch two-torsion point and mixed lower/upper additivity.
Everything below those two declarations is group algebra, branch exhaustion,
and AddCircle arithmetic.
-/

-- T2 translation and mixed additivity are now imported from
-- S10T2 and S10Mixed respectively.

theorem s11_componentKer_branch_exhaustion
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

theorem thetaPeriod_pos
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    0 < thetaPeriod A B e := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  simp [thetaPeriod]
  linarith

theorem neg_rootKerPoint_eq_rootKerPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    -rootKerPoint (A := A) (B := B) (e := e) hroot hderiv =
      rootKerPoint (A := A) (B := B) (e := e) hroot hderiv := by
  apply Subtype.ext
  change -(rootKerPoint (A := A) (B := B) (e := e) hroot hderiv :
      WeierstrassCurve.Affine.Point (shortW A B)) =
    rootKerPoint (A := A) (B := B) (e := e) hroot hderiv
  unfold rootKerPoint rootPoint
  rw [WeierstrassCurve.Affine.Point.neg_some]
  exact point_some_ext (A := A) (B := B)
    (x := e) (y := WeierstrassCurve.Affine.negY (shortW A B) e 0)
    (x' := e) (y' := 0) rfl (by simp [shortW])

theorem rootKerPoint_add_self
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    rootKerPoint (A := A) (B := B) (e := e) hroot hderiv +
        rootKerPoint (A := A) (B := B) (e := e) hroot hderiv =
      (0 : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) := by
  have hneg := neg_rootKerPoint_eq_rootKerPoint
    (A := A) (B := B) (e := e) hroot hderiv
  simpa [hneg] using
    (add_neg_cancel
      (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv))

theorem thetaCandidate_root_add_self
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) +
      thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      0 := by
  rw [thetaCandidate_rootKerPoint]
  rw [← AddCircle.coe_add]
  convert AddCircle.coe_period (p := thetaPeriod A B e) using 2
  ring

theorem thetaCandidate_neg_rootKerPoint
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :
    thetaCandidate (A := A) (B := B) (e := e)
        (-rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      -thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) := by
  have hneg := neg_rootKerPoint_eq_rootKerPoint
    (A := A) (B := B) (e := e) hroot hderiv
  rw [hneg, thetaCandidate_rootKerPoint]
  change (((halfPeriod A B e : ℝ)) : AddCircle (thetaPeriod A B e)) =
    -(((halfPeriod A B e : ℝ)) : AddCircle (thetaPeriod A B e))
  rw [← AddCircle.coe_neg]
  simpa [thetaPeriod] using addCircle_halfPeriod_eq_neg (A := A) (B := B) (e := e)

theorem thetaCandidate_upperRightKerPoint_eq_period_sub_sigma
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx) =
      ((thetaPeriod A B e - sigma A B x : ℝ) : AddCircle (thetaPeriod A B e)) := by
  rw [thetaCandidate_upperRightKerPoint]
  have h := AddCircle.coe_add_period
    (p := thetaPeriod A B e) (x := -sigma A B x)
  rw [← h]
  congr 1
  ring

theorem thetaCandidate_upperRight_add_root_eq_mid
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      ((halfPeriod A B e - sigma A B x : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  rw [thetaCandidate_T2_translation hposRight]
  rw [thetaCandidate_upperRightKerPoint, thetaCandidate_rootKerPoint]
  rw [← AddCircle.coe_add]
  congr 1
  ring

theorem addCircle_mid_ne_zero
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    ((halfPeriod A B e - sigma A B x : ℝ) :
        AddCircle (thetaPeriod A B e)) ≠ 0 := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hp : 0 < thetaPeriod A B e :=
    thetaPeriod_pos (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
  letI : Fact (0 < thetaPeriod A B e) := ⟨hp⟩
  have hs0 : 0 < sigma A B x :=
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hx
  have hsT : sigma A B x < halfPeriod A B e :=
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hx
  have hmid_mem : halfPeriod A B e - sigma A B x ∈
      Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simp
      linarith
    · simp [thetaPeriod]
      nlinarith
  have hzero_mem : (0 : ℝ) ∈ Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simp
    · simpa using hp
  intro hcircle
  have hcoef : halfPeriod A B e - sigma A B x = 0 := by
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := thetaPeriod A B e) (a := 0) hmid_mem hzero_mem).mp (by
        simpa using hcircle)
  linarith

theorem addCircle_mid_ne_root
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    ((halfPeriod A B e - sigma A B x : ℝ) :
        AddCircle (thetaPeriod A B e)) ≠
      ((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)) := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hp : 0 < thetaPeriod A B e :=
    thetaPeriod_pos (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
  letI : Fact (0 < thetaPeriod A B e) := ⟨hp⟩
  have hs0 : 0 < sigma A B x :=
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hx
  have hsT : sigma A B x < halfPeriod A B e :=
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hx
  have hmid_mem : halfPeriod A B e - sigma A B x ∈
      Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simp
      linarith
    · simp [thetaPeriod]
      nlinarith
  have hroot_mem : halfPeriod A B e ∈ Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simpa using hT.le
    · simp [thetaPeriod]
      linarith
  intro hcircle
  have hcoef : halfPeriod A B e - sigma A B x = halfPeriod A B e := by
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := thetaPeriod A B e) (a := 0) hmid_mem hroot_mem).mp hcircle
  linarith

theorem addCircle_mid_ne_upper
    {A B e x z : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) (hz : e < z) :
    ((halfPeriod A B e - sigma A B x : ℝ) :
        AddCircle (thetaPeriod A B e)) ≠
      ((thetaPeriod A B e - sigma A B z : ℝ) :
        AddCircle (thetaPeriod A B e)) := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hp : 0 < thetaPeriod A B e :=
    thetaPeriod_pos (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight
  letI : Fact (0 < thetaPeriod A B e) := ⟨hp⟩
  have hsx0 : 0 < sigma A B x :=
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hx
  have hsxT : sigma A B x < halfPeriod A B e :=
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hx
  have hsz0 : 0 < sigma A B z :=
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hz
  have hszT : sigma A B z < halfPeriod A B e :=
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hz
  have hmid_mem : halfPeriod A B e - sigma A B x ∈
      Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simp
      linarith
    · simp [thetaPeriod]
      nlinarith
  have hupper_mem : thetaPeriod A B e - sigma A B z ∈
      Ico 0 (0 + thetaPeriod A B e) := by
    constructor
    · simp [thetaPeriod]
      nlinarith
    · simp [thetaPeriod]
      linarith
  intro hcircle
  have hcoef :
      halfPeriod A B e - sigma A B x =
        thetaPeriod A B e - sigma A B z := by
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := thetaPeriod A B e) (a := 0) hmid_mem hupper_mem).mp hcircle
  have hleft_lt : halfPeriod A B e - sigma A B x < halfPeriod A B e := by
    linarith
  have hright_gt : halfPeriod A B e < thetaPeriod A B e - sigma A B z := by
    simp [thetaPeriod]
    linarith
  linarith

theorem upperRightKerPoint_add_rootKerPoint_is_lower
    {A B e x : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) :
    ∃ z hz,
      upperRightKerPoint (A := A) (B := B) (e := e)
          (hroot := hroot) (hderiv := hderiv) hposRight x hx +
        rootKerPoint (A := A) (B := B) (e := e) hroot hderiv =
          lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight z hz := by
  let U := upperRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let R := rootKerPoint (A := A) (B := B) (e := e) hroot hderiv
  have htheta :
      thetaCandidate (A := A) (B := B) (e := e) (U + R) =
        ((halfPeriod A B e - sigma A B x : ℝ) :
          AddCircle (thetaPeriod A B e)) := by
    simpa [U, R] using
      thetaCandidate_upperRight_add_root_eq_mid
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight hx
  rcases s11_componentKer_branch_exhaustion (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight (U + R) with
    hzero | hrootcase | hupper | hlower
  · exfalso
    have hcircle :
        ((halfPeriod A B e - sigma A B x : ℝ) :
          AddCircle (thetaPeriod A B e)) = 0 := by
      rw [← htheta, hzero]
      simp
    exact addCircle_mid_ne_zero
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx hcircle
  · exfalso
    have hcircle :
        ((halfPeriod A B e - sigma A B x : ℝ) :
          AddCircle (thetaPeriod A B e)) =
            ((halfPeriod A B e : ℝ) : AddCircle (thetaPeriod A B e)) := by
      rw [← htheta, hrootcase, thetaCandidate_rootKerPoint]
    exact addCircle_mid_ne_root
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx hcircle
  · rcases hupper with ⟨z, hz, hP⟩
    exfalso
    have hcircle :
        ((halfPeriod A B e - sigma A B x : ℝ) :
          AddCircle (thetaPeriod A B e)) =
            ((thetaPeriod A B e - sigma A B z : ℝ) :
              AddCircle (thetaPeriod A B e)) := by
      rw [← htheta, hP]
      rw [thetaCandidate_upperRightKerPoint_eq_period_sub_sigma]
    exact addCircle_mid_ne_upper
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hx hz hcircle
  · exact hlower

theorem thetaCandidate_neg
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaCandidate (A := A) (B := B) (e := e) (-P) =
      -thetaCandidate (A := A) (B := B) (e := e) P := by
  rcases s11_componentKer_branch_exhaustion (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight P with
    hzero | hrootcase | hupper | hlower
  · subst P
    simp
  · subst P
    exact thetaCandidate_neg_rootKerPoint
      (A := A) (B := B) (e := e) hroot hderiv
  · rcases hupper with ⟨x, hx, rfl⟩
    rw [neg_upperRightKerPoint_eq_lowerRightKerPoint]
    exact thetaCandidate_lowerRightKerPoint_eq_neg_upper hposRight hx
  · rcases hlower with ⟨x, hx, rfl⟩
    rw [neg_lowerRightKerPoint_eq_upperRightKerPoint]
    rw [thetaCandidate_lowerRightKerPoint_eq_neg_upper hposRight hx]
    simp

theorem thetaCandidate_root_right_add
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaCandidate (A := A) (B := B) (e := e)
        (P + rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) =
      thetaCandidate (A := A) (B := B) (e := e) P +
        thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) :=
  thetaCandidate_T2_translation hposRight P

theorem thetaCandidate_root_left_add
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaCandidate (A := A) (B := B) (e := e)
        (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv + P) =
      thetaCandidate (A := A) (B := B) (e := e)
          (rootKerPoint (A := A) (B := B) (e := e) hroot hderiv) +
        thetaCandidate (A := A) (B := B) (e := e) P := by
  rw [add_comm]
  rw [thetaCandidate_T2_translation hposRight]
  abel

theorem thetaCandidate_upper_lower
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) (hy : e < y) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) =
      thetaCandidate (A := A) (B := B) (e := e)
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) := by
  rw [add_comm]
  rw [thetaCandidate_mixed_additive hposRight hy hx]
  abel

theorem thetaCandidate_upper_upper
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) (hy : e < y) :
    thetaCandidate (A := A) (B := B) (e := e)
        (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) =
      thetaCandidate (A := A) (B := B) (e := e)
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (upperRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) := by
  let R := rootKerPoint (A := A) (B := B) (e := e) hroot hderiv
  let U₁ := upperRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let U₂ := upperRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight y hy
  rcases upperRightKerPoint_add_rootKerPoint_is_lower
      (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
      hposRight hy with ⟨z, hz, hL⟩
  let L := lowerRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight z hz
  have hL' : U₂ + R = L := by
    simpa [U₂, R, L] using hL
  have hR2 : R + R = 0 := by
    simpa [R] using rootKerPoint_add_self
      (A := A) (B := B) (e := e) hroot hderiv
  have hthetaR2 :
      thetaCandidate (A := A) (B := B) (e := e) R +
          thetaCandidate (A := A) (B := B) (e := e) R =
        0 := by
    simpa [R] using thetaCandidate_root_add_self
      (A := A) (B := B) (e := e) hroot hderiv
  have harg : (U₁ + L) + R = U₁ + U₂ := by
    rw [← hL']
    calc
      (U₁ + (U₂ + R)) + R = U₁ + U₂ + (R + R) := by abel
      _ = U₁ + U₂ + 0 := by rw [hR2]
      _ = U₁ + U₂ := by simp
  calc
    thetaCandidate (A := A) (B := B) (e := e) (U₁ + U₂)
        = thetaCandidate (A := A) (B := B) (e := e) ((U₁ + L) + R) := by
            rw [harg]
    _ = thetaCandidate (A := A) (B := B) (e := e) (U₁ + L) +
          thetaCandidate (A := A) (B := B) (e := e) R := by
            exact thetaCandidate_T2_translation hposRight (U₁ + L)
    _ = thetaCandidate (A := A) (B := B) (e := e) (L + U₁) +
          thetaCandidate (A := A) (B := B) (e := e) R := by
            rw [add_comm U₁ L]
    _ = (thetaCandidate (A := A) (B := B) (e := e) L +
            thetaCandidate (A := A) (B := B) (e := e) U₁) +
          thetaCandidate (A := A) (B := B) (e := e) R := by
            simp [L, U₁, thetaCandidate_mixed_additive hposRight hz hx]
    _ = (thetaCandidate (A := A) (B := B) (e := e) (U₂ + R) +
            thetaCandidate (A := A) (B := B) (e := e) U₁) +
          thetaCandidate (A := A) (B := B) (e := e) R := by
            rw [hL']
    _ = ((thetaCandidate (A := A) (B := B) (e := e) U₂ +
              thetaCandidate (A := A) (B := B) (e := e) R) +
            thetaCandidate (A := A) (B := B) (e := e) U₁) +
          thetaCandidate (A := A) (B := B) (e := e) R := by
            rw [thetaCandidate_T2_translation hposRight]
    _ = thetaCandidate (A := A) (B := B) (e := e) U₁ +
          thetaCandidate (A := A) (B := B) (e := e) U₂ +
            (thetaCandidate (A := A) (B := B) (e := e) R +
              thetaCandidate (A := A) (B := B) (e := e) R) := by
            abel
    _ = thetaCandidate (A := A) (B := B) (e := e) U₁ +
          thetaCandidate (A := A) (B := B) (e := e) U₂ := by
            rw [hthetaR2]
            simp

theorem thetaCandidate_lower_lower
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) (hy : e < y) :
    thetaCandidate (A := A) (B := B) (e := e)
        (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx +
          lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) =
      thetaCandidate (A := A) (B := B) (e := e)
          (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight x hx) +
        thetaCandidate (A := A) (B := B) (e := e)
          (lowerRightKerPoint (A := A) (B := B) (e := e)
            (hroot := hroot) (hderiv := hderiv) hposRight y hy) := by
  let L₁ := lowerRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let L₂ := lowerRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight y hy
  let U₁ := upperRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight x hx
  let U₂ := upperRightKerPoint (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight y hy
  have hL₁ : L₁ = -U₁ := by
    simpa [L₁, U₁] using
      (neg_upperRightKerPoint_eq_lowerRightKerPoint
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight hx).symm
  have hL₂ : L₂ = -U₂ := by
    simpa [L₂, U₂] using
      (neg_upperRightKerPoint_eq_lowerRightKerPoint
        (A := A) (B := B) (e := e) (hroot := hroot) (hderiv := hderiv)
        hposRight hy).symm
  have hsum : L₁ + L₂ = -(U₁ + U₂) := by
    rw [hL₁, hL₂]
    abel
  have hthetaL₁ :
      thetaCandidate (A := A) (B := B) (e := e) L₁ =
        -thetaCandidate (A := A) (B := B) (e := e) U₁ := by
    rw [hL₁]
    exact thetaCandidate_neg hposRight U₁
  have hthetaL₂ :
      thetaCandidate (A := A) (B := B) (e := e) L₂ =
        -thetaCandidate (A := A) (B := B) (e := e) U₂ := by
    rw [hL₂]
    exact thetaCandidate_neg hposRight U₂
  calc
    thetaCandidate (A := A) (B := B) (e := e) (L₁ + L₂)
        = thetaCandidate (A := A) (B := B) (e := e) (-(U₁ + U₂)) := by
            rw [hsum]
    _ = -thetaCandidate (A := A) (B := B) (e := e) (U₁ + U₂) := by
            exact thetaCandidate_neg hposRight (U₁ + U₂)
    _ = -(thetaCandidate (A := A) (B := B) (e := e) U₁ +
            thetaCandidate (A := A) (B := B) (e := e) U₂) := by
            rw [thetaCandidate_upper_upper hposRight hx hy]
    _ = -thetaCandidate (A := A) (B := B) (e := e) U₁ +
          -thetaCandidate (A := A) (B := B) (e := e) U₂ := by
            abel
    _ = thetaCandidate (A := A) (B := B) (e := e) L₁ +
          thetaCandidate (A := A) (B := B) (e := e) L₂ := by
            rw [hthetaL₁, hthetaL₂]

theorem thetaCandidateAdditive
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    ThetaCandidateAdditive (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) := by
  intro P Q
  rcases s11_componentKer_branch_exhaustion (A := A) (B := B) (e := e)
      (hroot := hroot) (hderiv := hderiv) hposRight P with
    hP0 | hPR | hPU | hPL
  · subst P
    simp
  · subst P
    exact thetaCandidate_root_left_add (hposRight := hposRight) Q
  · rcases hPU with ⟨x, hx, rfl⟩
    rcases s11_componentKer_branch_exhaustion (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q with
      hQ0 | hQR | hQU | hQL
    · subst Q
      simp
    · subst Q
      exact thetaCandidate_root_right_add hposRight _
    · rcases hQU with ⟨y, hy, rfl⟩
      exact thetaCandidate_upper_upper hposRight hx hy
    · rcases hQL with ⟨y, hy, rfl⟩
      exact thetaCandidate_upper_lower hposRight hx hy
  · rcases hPL with ⟨x, hx, rfl⟩
    rcases s11_componentKer_branch_exhaustion (A := A) (B := B) (e := e)
        (hroot := hroot) (hderiv := hderiv) hposRight Q with
      hQ0 | hQR | hQU | hQL
    · subst Q
      simp
    · subst Q
      exact thetaCandidate_root_right_add hposRight _
    · rcases hQU with ⟨y, hy, rfl⟩
      exact thetaCandidate_mixed_additive hposRight hx hy
    · rcases hQL with ⟨y, hy, rfl⟩
      exact thetaCandidate_lower_lower hposRight hx hy

end

end MazurProof.RealTopology
