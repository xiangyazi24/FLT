import FLT.Assumptions.MazurProof.RealTopologyS4

open scoped WeierstrassCurve.Affine
open MeasureTheory Set Real Filter Topology

namespace MazurProof.RealTopology

noncomputable section

/-- The kernel of the real component homomorphism from S3. -/
abbrev ComponentKer {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e) :=
  (componentBitHom (A := A) (B := B) (e := e) hroot hderiv).ker

/-- A real representative of the sigma-coordinate on the identity component.

The upper branch uses `2T - σ x`, which represents `-σ x` modulo the period
`2T` but lies in the fundamental interval `[0, 2T)`. -/
def thetaRep
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) : ℝ :=
  match P.1 with
  | 0 => 0
  | WeierstrassCurve.Affine.Point.some x y _ =>
      if x = e then halfPeriod A B e
      else if 0 ≤ y then 2 * halfPeriod A B e - sigma A B x
      else sigma A B x

/-- The non-additive theta candidate.  Additivity is the S6-S8 work; S5 only
sets up branch formulas and injectivity infrastructure. -/
def thetaCandidate
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    AddCircle (2 * halfPeriod A B e) :=
  thetaRep (A := A) (B := B) (e := e) P

@[simp]
theorem thetaRep_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} :
    thetaRep (A := A) (B := B) (e := e)
      (0 : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) = 0 :=
  rfl

@[simp]
theorem thetaCandidate_zero
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e} :
    thetaCandidate (A := A) (B := B) (e := e)
      (0 : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) = 0 :=
  rfl

theorem componentKer_some_not_lt
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h) :
    ¬ x < e := by
  have hk := P.2
  change componentBit e P.1 = 0 at hk
  rw [hP] at hk
  by_contra hx
  simp [componentBit, sideBit, hx] at hk

theorem componentKer_some_eq_or_gt
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h) :
    x = e ∨ e < x := by
  have hnlt := componentKer_some_not_lt (A := A) (B := B) (e := e)
    (x := x) (y := y) (h := h) P hP
  have hle : e ≤ x := not_lt.mp hnlt
  rcases eq_or_lt_of_le hle with hxe | hex
  · exact Or.inl hxe.symm
  · exact Or.inr hex

theorem componentKer_some_gt_of_ne
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hxne : x ≠ e) :
    e < x := by
  rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
      (x := x) (y := y) (h := h) P hP with hxe | hex
  · exact (hxne hxe).elim
  · exact hex

theorem componentKer_some_y_eq_zero_of_x_eq_root
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (_P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (_hP : _P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hxe : x = e) :
    y = 0 :=
  branch_y_eq_zero (A := A) (B := B) (e := e) (x := x) (y := y)
    hroot hxe h

theorem componentKer_some_y_branch_of_gt
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (_P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (_hP : _P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (_hex : e < x) :
    y = √(shortCubic A B x) ∨ y = -√(shortCubic A B x) :=
  shortW_y_eq_sqrt_or_eq_neg_sqrt (A := A) (B := B) (x := x) (y := y) h

theorem thetaRep_some_root
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hxe : x = e) :
    thetaRep (A := A) (B := B) (e := e) P = halfPeriod A B e := by
  simp [thetaRep, hP, hxe]

theorem thetaCandidate_some_root
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hxe : x = e) :
    thetaCandidate (A := A) (B := B) (e := e) P =
      ((halfPeriod A B e : ℝ) : AddCircle (2 * halfPeriod A B e)) := by
  simp [thetaCandidate, thetaRep_some_root (A := A) (B := B) (e := e) P hP hxe]

theorem thetaRep_some_upper
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : 0 ≤ y) :
    thetaRep (A := A) (B := B) (e := e) P =
      2 * halfPeriod A B e - sigma A B x := by
  have hxne : x ≠ e := ne_of_gt hex
  simp [thetaRep, hP, hxne, hy]

theorem thetaCandidate_some_upper
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : 0 ≤ y) :
    thetaCandidate (A := A) (B := B) (e := e) P =
      (((2 * halfPeriod A B e - sigma A B x : ℝ)) :
        AddCircle (2 * halfPeriod A B e)) := by
  simp [thetaCandidate, thetaRep_some_upper (A := A) (B := B) (e := e) P hP hex hy]

theorem thetaCandidate_some_upper_eq_neg_sigma
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : 0 ≤ y) :
    thetaCandidate (A := A) (B := B) (e := e) P =
      ((-sigma A B x : ℝ) : AddCircle (2 * halfPeriod A B e)) := by
  rw [thetaCandidate_some_upper (A := A) (B := B) (e := e) P hP hex hy]
  rw [show 2 * halfPeriod A B e - sigma A B x =
      -sigma A B x + 2 * halfPeriod A B e by ring]
  exact AddCircle.coe_add_period (p := 2 * halfPeriod A B e) (-sigma A B x)

theorem thetaRep_some_lower
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : y < 0) :
    thetaRep (A := A) (B := B) (e := e) P = sigma A B x := by
  have hxne : x ≠ e := ne_of_gt hex
  have hynle : ¬ 0 ≤ y := not_le_of_gt hy
  simp [thetaRep, hP, hxne, hynle]

theorem thetaCandidate_some_lower
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : y < 0) :
    thetaCandidate (A := A) (B := B) (e := e) P =
      ((sigma A B x : ℝ) : AddCircle (2 * halfPeriod A B e)) := by
  simp [thetaCandidate, thetaRep_some_lower (A := A) (B := B) (e := e) P hP hex hy]

theorem addCircle_halfPeriod_eq_neg
    {A B e : ℝ} :
    ((halfPeriod A B e : ℝ) : AddCircle (2 * halfPeriod A B e)) =
      ((-halfPeriod A B e : ℝ) : AddCircle (2 * halfPeriod A B e)) := by
  have h := AddCircle.coe_add_period
    (p := 2 * halfPeriod A B e) (-halfPeriod A B e)
  rwa [show -halfPeriod A B e + 2 * halfPeriod A B e = halfPeriod A B e by ring] at h

theorem thetaRep_mem_Ico
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv) :
    thetaRep (A := A) (B := B) (e := e) P ∈
      Ico 0 (2 * halfPeriod A B e) := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  cases hP : P.1 with
  | zero =>
      simp [thetaRep, hP, hT]
  | some x y h =>
      rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
          (x := x) (y := y) (h := h) P hP with hxe | hex
      · simp [thetaRep, hP, hxe, hT]
        nlinarith
      · by_cases hy : 0 ≤ y
        · have hsig0 : 0 < sigma A B x :=
            sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hex
          have hsigT : sigma A B x < halfPeriod A B e :=
            sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
              hroot hderiv hposRight hex
          simp [thetaRep, hP, ne_of_gt hex, hy]
          constructor <;> nlinarith
        · have hsig0 : 0 < sigma A B x :=
            sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hex
          have hsigT : sigma A B x < halfPeriod A B e :=
            sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
              hroot hderiv hposRight hex
          simp [thetaRep, hP, ne_of_gt hex, hy]
          constructor <;> nlinarith

theorem thetaCandidate_eq_iff_thetaRep_eq
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    {P Q : ComponentKer (A := A) (B := B) (e := e) hroot hderiv} :
    thetaCandidate (A := A) (B := B) (e := e) P =
        thetaCandidate (A := A) (B := B) (e := e) Q ↔
      thetaRep (A := A) (B := B) (e := e) P =
        thetaRep (A := A) (B := B) (e := e) Q := by
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  have h2T : 0 < 2 * halfPeriod A B e := by nlinarith
  letI : Fact (0 < 2 * halfPeriod A B e) := ⟨h2T⟩
  change
    (((thetaRep (A := A) (B := B) (e := e) P : ℝ)) :
        AddCircle (2 * halfPeriod A B e)) =
          ((thetaRep (A := A) (B := B) (e := e) Q : ℝ) :
            AddCircle (2 * halfPeriod A B e)) ↔
      thetaRep (A := A) (B := B) (e := e) P =
        thetaRep (A := A) (B := B) (e := e) Q
  exact AddCircle.coe_eq_coe_iff_of_mem_Ico
    (p := 2 * halfPeriod A B e) (a := 0)
    (by
      simpa [zero_add] using
        thetaRep_mem_Ico (A := A) (B := B) (e := e) hposRight P)
    (by
      simpa [zero_add] using
        thetaRep_mem_Ico (A := A) (B := B) (e := e) hposRight Q)

theorem sigma_injective_of_right
    {A B e x z : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (hx : e < x) (hz : e < z)
    (hsigma : sigma A B x = sigma A B z) :
    x = z := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxz | hzx
  · have hlt : sigma A B z < sigma A B x :=
      strictAntiOn_sigma_Ioi (A := A) (B := B) (e := e)
        hroot hderiv hposRight hx hz hxz
    linarith
  · have hlt : sigma A B x < sigma A B z :=
      strictAntiOn_sigma_Ioi (A := A) (B := B) (e := e)
        hroot hderiv hposRight hz hx hzx
    linarith

theorem componentKer_some_y_eq_sqrt_of_gt_of_nonneg
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : 0 ≤ y) :
    y = √(shortCubic A B x) := by
  rcases componentKer_some_y_branch_of_gt (A := A) (B := B) (e := e)
      (x := x) (y := y) (h := h) P hP hex with hypos | hyneg
  · exact hypos
  · exfalso
    have hsqrtpos : 0 < √(shortCubic A B x) :=
      Real.sqrt_pos.mpr (hposRight hex)
    have hylt : y < 0 := by
      rw [hyneg]
      exact neg_lt_zero.mpr hsqrtpos
    linarith

theorem componentKer_some_y_eq_neg_sqrt_of_gt_of_neg
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : y < 0) :
    y = -√(shortCubic A B x) := by
  rcases componentKer_some_y_branch_of_gt (A := A) (B := B) (e := e)
      (x := x) (y := y) (h := h) P hP hex with hypos | hyneg
  · exfalso
    have hsqrtpos : 0 < √(shortCubic A B x) :=
      Real.sqrt_pos.mpr (hposRight hex)
    have hygt : 0 < y := by
      rw [hypos]
      exact hsqrtpos
    linarith
  · exact hyneg

theorem point_some_ext
    {A B x y x' y' : ℝ}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    {h' : WeierstrassCurve.Affine.Nonsingular (shortW A B) x' y'}
    (hx : x = x') (hy : y = y') :
    (WeierstrassCurve.Affine.Point.some x y h :
        WeierstrassCurve.Affine.Point (shortW A B)) =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

theorem thetaRep_some_lower_pos_lt_halfPeriod
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : y < 0) :
    0 < thetaRep (A := A) (B := B) (e := e) P ∧
      thetaRep (A := A) (B := B) (e := e) P < halfPeriod A B e := by
  rw [thetaRep_some_lower (A := A) (B := B) (e := e) P hP hex hy]
  exact ⟨
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hex,
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hex⟩

theorem thetaRep_some_upper_halfPeriod_lt
    {A B e x y : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    {h : WeierstrassCurve.Affine.Nonsingular (shortW A B) x y}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u)
    (P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv)
    (hP : P.1 = WeierstrassCurve.Affine.Point.some x y h)
    (hex : e < x) (hy : 0 ≤ y) :
    halfPeriod A B e < thetaRep (A := A) (B := B) (e := e) P ∧
      thetaRep (A := A) (B := B) (e := e) P < 2 * halfPeriod A B e := by
  have hsig0 : 0 < sigma A B x :=
    sigma_pos_of_right (A := A) (B := B) (e := e) hroot hderiv hposRight hex
  have hsigT : sigma A B x < halfPeriod A B e :=
    sigma_lt_halfPeriod_of_right (A := A) (B := B) (e := e)
      hroot hderiv hposRight hex
  rw [thetaRep_some_upper (A := A) (B := B) (e := e) P hP hex hy]
  constructor <;> nlinarith

theorem thetaRep_injective
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Function.Injective
      (fun P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv =>
        thetaRep (A := A) (B := B) (e := e) P) := by
  intro P Q htheta
  have hT : 0 < halfPeriod A B e :=
    halfPeriod_pos (A := A) (B := B) (e := e) hroot hderiv hposRight
  apply Subtype.ext
  cases hP : P.1 with
  | zero =>
      cases hQ : Q.1 with
      | zero =>
          rfl
      | some x y h =>
          exfalso
          have hP0 : thetaRep (A := A) (B := B) (e := e) P = 0 := by
            simp [thetaRep, hP]
          rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
              (x := x) (y := y) (h := h) Q hQ with hxe | hex
          · have hQrep := thetaRep_some_root (A := A) (B := B) (e := e)
              (x := x) (y := y) (h := h) Q hQ hxe
            nlinarith
          · by_cases hy : 0 ≤ y
            · have hQrange := thetaRep_some_upper_halfPeriod_lt
                (A := A) (B := B) (e := e) hposRight Q hQ hex hy
              nlinarith
            · have hylt : y < 0 := not_le.mp hy
              have hQrange := thetaRep_some_lower_pos_lt_halfPeriod
                (A := A) (B := B) (e := e) hposRight Q hQ hex hylt
              nlinarith
  | some x y h =>
      cases hQ : Q.1 with
      | zero =>
          exfalso
          have hQ0 : thetaRep (A := A) (B := B) (e := e) Q = 0 := by
            simp [thetaRep, hQ]
          rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
              (x := x) (y := y) (h := h) P hP with hxe | hex
          · have hPrep := thetaRep_some_root (A := A) (B := B) (e := e)
              (x := x) (y := y) (h := h) P hP hxe
            nlinarith
          · by_cases hy : 0 ≤ y
            · have hPrange := thetaRep_some_upper_halfPeriod_lt
                (A := A) (B := B) (e := e) hposRight P hP hex hy
              nlinarith
            · have hylt : y < 0 := not_le.mp hy
              have hPrange := thetaRep_some_lower_pos_lt_halfPeriod
                (A := A) (B := B) (e := e) hposRight P hP hex hylt
              nlinarith
      | some x' y' h' =>
          rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
              (x := x) (y := y) (h := h) P hP with hxe | hex
          · rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
                (x := x') (y := y') (h := h') Q hQ with hxe' | hex'
            · have hy0 := componentKer_some_y_eq_zero_of_x_eq_root
                (A := A) (B := B) (e := e) (x := x) (y := y) (h := h)
                P hP hxe
              have hy0' := componentKer_some_y_eq_zero_of_x_eq_root
                (A := A) (B := B) (e := e) (x := x') (y := y') (h := h')
                Q hQ hxe'
              exact point_some_ext
                (A := A) (B := B) (x := x) (y := y) (x' := x') (y' := y')
                (h := h) (h' := h') (hxe.trans hxe'.symm) (hy0.trans hy0'.symm)
            · have hPrep := thetaRep_some_root (A := A) (B := B) (e := e)
                (x := x) (y := y) (h := h) P hP hxe
              by_cases hy'nonneg : 0 ≤ y'
              · have hQrange := thetaRep_some_upper_halfPeriod_lt
                  (A := A) (B := B) (e := e) hposRight Q hQ hex' hy'nonneg
                nlinarith
              · have hy'lt : y' < 0 := not_le.mp hy'nonneg
                have hQrange := thetaRep_some_lower_pos_lt_halfPeriod
                  (A := A) (B := B) (e := e) hposRight Q hQ hex' hy'lt
                nlinarith
          · rcases componentKer_some_eq_or_gt (A := A) (B := B) (e := e)
                (x := x') (y := y') (h := h') Q hQ with hxe' | hex'
            · have hQrep := thetaRep_some_root (A := A) (B := B) (e := e)
                (x := x') (y := y') (h := h') Q hQ hxe'
              by_cases hynonneg : 0 ≤ y
              · have hPrange := thetaRep_some_upper_halfPeriod_lt
                  (A := A) (B := B) (e := e) hposRight P hP hex hynonneg
                nlinarith
              · have hylt : y < 0 := not_le.mp hynonneg
                have hPrange := thetaRep_some_lower_pos_lt_halfPeriod
                  (A := A) (B := B) (e := e) hposRight P hP hex hylt
                nlinarith
            · by_cases hynonneg : 0 ≤ y
              · by_cases hy'nonneg : 0 ≤ y'
                · have hPrep := thetaRep_some_upper (A := A) (B := B) (e := e)
                    (x := x) (y := y) (h := h) P hP hex hynonneg
                  have hQrep := thetaRep_some_upper (A := A) (B := B) (e := e)
                    (x := x') (y := y') (h := h') Q hQ hex' hy'nonneg
                  have hsigma : sigma A B x = sigma A B x' := by
                    nlinarith
                  have hx' : x = x' :=
                    sigma_injective_of_right (A := A) (B := B) (e := e)
                      hroot hderiv hposRight hex hex' hsigma
                  have hy' : y = y' := by
                    have hy_sqrt := componentKer_some_y_eq_sqrt_of_gt_of_nonneg
                      (A := A) (B := B) (e := e) (x := x) (y := y) (h := h)
                      hposRight P hP hex hynonneg
                    have hy'_sqrt := componentKer_some_y_eq_sqrt_of_gt_of_nonneg
                      (A := A) (B := B) (e := e) (x := x') (y := y') (h := h')
                      hposRight Q hQ hex' hy'nonneg
                    calc
                      y = √(shortCubic A B x) := hy_sqrt
                      _ = √(shortCubic A B x') := by rw [hx']
                      _ = y' := hy'_sqrt.symm
                  exact point_some_ext
                    (A := A) (B := B) (x := x) (y := y) (x' := x') (y' := y')
                    (h := h) (h' := h') hx' hy'
                · have hy'lt : y' < 0 := not_le.mp hy'nonneg
                  have hPrange := thetaRep_some_upper_halfPeriod_lt
                    (A := A) (B := B) (e := e) hposRight P hP hex hynonneg
                  have hQrange := thetaRep_some_lower_pos_lt_halfPeriod
                    (A := A) (B := B) (e := e) hposRight Q hQ hex' hy'lt
                  nlinarith
              · have hylt : y < 0 := not_le.mp hynonneg
                by_cases hy'nonneg : 0 ≤ y'
                · have hPrange := thetaRep_some_lower_pos_lt_halfPeriod
                    (A := A) (B := B) (e := e) hposRight P hP hex hylt
                  have hQrange := thetaRep_some_upper_halfPeriod_lt
                    (A := A) (B := B) (e := e) hposRight Q hQ hex' hy'nonneg
                  nlinarith
                · have hy'lt : y' < 0 := not_le.mp hy'nonneg
                  have hPrep := thetaRep_some_lower (A := A) (B := B) (e := e)
                    (x := x) (y := y) (h := h) P hP hex hylt
                  have hQrep := thetaRep_some_lower (A := A) (B := B) (e := e)
                    (x := x') (y := y') (h := h') Q hQ hex' hy'lt
                  have hsigma : sigma A B x = sigma A B x' := by
                    nlinarith
                  have hx' : x = x' :=
                    sigma_injective_of_right (A := A) (B := B) (e := e)
                      hroot hderiv hposRight hex hex' hsigma
                  have hy' : y = y' := by
                    have hy_sqrt := componentKer_some_y_eq_neg_sqrt_of_gt_of_neg
                      (A := A) (B := B) (e := e) (x := x) (y := y) (h := h)
                      hposRight P hP hex hylt
                    have hy'_sqrt := componentKer_some_y_eq_neg_sqrt_of_gt_of_neg
                      (A := A) (B := B) (e := e) (x := x') (y := y') (h := h')
                      hposRight Q hQ hex' hy'lt
                    calc
                      y = -√(shortCubic A B x) := hy_sqrt
                      _ = -√(shortCubic A B x') := by rw [hx']
                      _ = y' := hy'_sqrt.symm
                  exact point_some_ext
                    (A := A) (B := B) (x := x) (y := y) (x' := x') (y' := y')
                    (h := h) (h' := h') hx' hy'

theorem thetaCandidate_injective
    {A B e : ℝ}
    {hroot : shortCubic A B e = 0}
    {hderiv : 0 < shortCubicDeriv A B e}
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Function.Injective
      (fun P : ComponentKer (A := A) (B := B) (e := e) hroot hderiv =>
        thetaCandidate (A := A) (B := B) (e := e) P) := by
  intro P Q hPQ
  apply thetaRep_injective (A := A) (B := B) (e := e)
    (hroot := hroot) (hderiv := hderiv) hposRight
  exact (thetaCandidate_eq_iff_thetaRep_eq (A := A) (B := B) (e := e)
    hposRight (P := P) (Q := Q)).mp hPQ

end

end MazurProof.RealTopology
