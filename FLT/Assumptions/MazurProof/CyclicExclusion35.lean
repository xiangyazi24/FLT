import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.TateNormalFormBridge
import FLT.Assumptions.MazurProof.TateOriginDivision
import FLT.Assumptions.MazurProof.RationalPointsX135Formal

/-!
# Cyclic order 35 exclusion

A rational point of exact order `35 = 5 · 7` gives, by taking `7 • P` and
`5 • P`, simultaneous rational points of order `5` and `7` on the same curve.
Geometrically this is a non-cuspidal rational point on the fiber product
`X₁(5) ×_{j-line} X₁(7)` (equivalently `X₁(35)`), which has only cuspidal
rational points over `ℚ`.

The order-`5` and order-`7` subpoints are extracted with the axiom-free
prime-order reduction lemma `exists_point_of_prime_order_of_dvd`.  Their Tate
parameters give a noncuspidal point on `X₀(35)`, whose explicit map to the
rank-zero quotient `35a1` contradicts its proved rational-point
classification.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

open Polynomial
open Scratch.TateZ2xZ10Reduction

noncomputable section

/-! ## Order-`5` and order-`7` subpoints of an order-`35` point -/

/-- From a rational point of exact order `35`, the point `7 • P` has order `5`. -/
theorem order35_gives_order5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 5 :=
  exists_point_of_prime_order_of_dvd E
    (show (35 : ℕ) ≠ 0 by norm_num)
    (show Nat.Prime 5 by norm_num)
    (show (5 : ℕ) ∣ 35 by norm_num) h

/-- From a rational point of exact order `35`, the point `5 • P` has order `7`. -/
theorem order35_gives_order7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 7 :=
  exists_point_of_prime_order_of_dvd E
    (show (35 : ℕ) ≠ 0 by norm_num)
    (show Nat.Prime 7 by norm_num)
    (show (7 : ℕ) ∣ 35 by norm_num) h

/-- A rational point of exact order `35` yields simultaneous rational points of
order `5` and order `7`. -/
theorem order35_gives_orders5_and_7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 5 ∧ HasRationalPointOfOrder E 7 :=
  ⟨order35_gives_order5 E h, order35_gives_order7 E h⟩

/-! ## Explicit `X₀(5)` and `X₀(7)` parameters -/

private abbrev TateCurve35 (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

private lemma eval_prePsi_five_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 5).eval 0 =
      ((TateCurve35 b c).preΨ₄).eval 0 *
          ((TateCurve35 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((TateCurve35 b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0)
    ((TateCurve35 b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_seven_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 7).eval 0 =
      ((TateCurve35 b c).preΨ' 5).eval 0 *
          (((TateCurve35 b c).preΨ' 3).eval 0) ^ 3 -
        ((TateCurve35 b c).preΨ' 4).eval 0 ^ 3 *
          ((TateCurve35 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0)
    ((TateCurve35 b c).preΨ'_odd 1)
  simpa using h

private theorem prePsi_five_at_origin_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 5).eval 0 = b ^ 8 * (b - c) := by
  rw [eval_prePsi_five_35]
  simp [TateCurve35, tateNormalFormCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem prePsi_seven_at_origin_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 7).eval 0 =
      b ^ 16 * (c ^ 3 - b ^ 2 + b * c) := by
  rw [eval_prePsi_seven_35, eval_prePsi_five_35]
  simp [TateCurve35, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem order_five_parameter_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 b c)]
    (hb : b ≠ 0)
    (hord : addOrderOf (TateNormalFormBridge.tateOrigin b c) = 5) :
    c = b := by
  have hord' : addOrderOf (TateOriginDivision.tateOrigin b c) = 5 := by
    rw [TateOriginDivision.tateOrigin_eq_normalized_origin]
    exact hord
  have hpre := TateOriginDivision.prePsi_eval_zero_of_odd_addOrder
    b c (show ¬ Even 5 by decide) hord'
  rw [prePsi_five_at_origin_35] at hpre
  have : b - c = 0 :=
    (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 8 hb)
  linarith

private theorem order_seven_parameter_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 b c)]
    (hb : b ≠ 0)
    (hord : addOrderOf (TateNormalFormBridge.tateOrigin b c) = 7) :
    c ^ 3 - b ^ 2 + b * c = 0 := by
  have hord' : addOrderOf (TateOriginDivision.tateOrigin b c) = 7 := by
    rw [TateOriginDivision.tateOrigin_eq_normalized_origin]
    exact hord
  have hpre := TateOriginDivision.prePsi_eval_zero_of_odd_addOrder
    b c (show ¬ Even 7 by decide) hord'
  rw [prePsi_seven_at_origin_35] at hpre
  exact (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 16 hb)

private def hauptmodul5 (p : ℚ) : ℚ :=
  (p ^ 2 - 11 * p - 1) / p

private def hauptmodul7 (t : ℚ) : ℚ :=
  (t ^ 3 - 8 * t ^ 2 + 5 * t + 1) / (t * (t - 1))

private theorem tate_order_five_delta (p : ℚ) :
    (TateCurve35 p p).Δ = p ^ 5 * (p ^ 2 - 11 * p - 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private theorem tate_order_five_c4 (p : ℚ) :
    (TateCurve35 p p).c₄ =
      p ^ 4 - 12 * p ^ 3 + 14 * p ^ 2 + 12 * p + 1 := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem tate_order_seven_delta (t : ℚ) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).Δ =
      t ^ 7 * (t - 1) ^ 7 *
        (t ^ 3 - 8 * t ^ 2 + 5 * t + 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private theorem tate_order_seven_c4 (t : ℚ) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).c₄ =
      (t ^ 2 - t + 1) *
        (t ^ 6 - 11 * t ^ 5 + 30 * t ^ 4 - 15 * t ^ 3 -
          10 * t ^ 2 + 5 * t + 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem tate_order_five_j
    (p : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 p p)]
    (hp : p ≠ 0) (hd : p ^ 2 - 11 * p - 1 ≠ 0) :
    (TateCurve35 p p).j =
      RationalPointsX135.J5Numerator (hauptmodul5 p) / hauptmodul5 p := by
  rw [WeierstrassCurve.j]
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  rw [tate_order_five_delta, tate_order_five_c4]
  unfold RationalPointsX135.J5Numerator hauptmodul5
  field_simp [hp, hd]
  ring

private theorem tate_order_seven_j
    (t : ℚ)
    [WeierstrassCurve.IsElliptic
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1)))]
    (ht : t ≠ 0) (ht1 : t - 1 ≠ 0)
    (hq : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j =
      RationalPointsX135.J7Numerator (hauptmodul7 t) / hauptmodul7 t := by
  rw [WeierstrassCurve.j]
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  rw [tate_order_seven_delta, tate_order_seven_c4]
  unfold RationalPointsX135.J7Numerator hauptmodul7
  field_simp [ht, ht1, hq]
  ring

/-- Simultaneous rational points of orders five and seven give a noncuspidal
point on the affine fiber product `X₀(5) ×_j X₀(7)`. -/
theorem simultaneous_orders_five_seven_to_X035_fiber
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h5 : HasRationalPointOfOrder E 5)
    (h7 : HasRationalPointOfOrder E 7) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧
      RationalPointsX135.X035FiberEquation a b := by
  obtain ⟨P5, hP5⟩ := h5
  obtain ⟨p, c5, hEll5, hord5, hp, hj5⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three_with_j
      E P5 5 (by norm_num) hP5
  letI : WeierstrassCurve.IsElliptic (TateCurve35 p c5) := hEll5
  have hc5 : c5 = p := order_five_parameter_eq p c5 hp hord5
  subst c5
  have hd5 : p ^ 2 - 11 * p - 1 ≠ 0 := by
    intro hd
    have hDelta : (TateCurve35 p p).Δ ≠ 0 :=
      (TateCurve35 p p).isUnit_Δ.ne_zero
    apply hDelta
    rw [tate_order_five_delta, hd]
    ring
  let a : ℚ := hauptmodul5 p
  have ha : a ≠ 0 := by
    exact div_ne_zero hd5 hp
  have hj5formula : (TateCurve35 p p).j =
      RationalPointsX135.J5Numerator a / a := by
    exact tate_order_five_j p hp hd5

  obtain ⟨P7, hP7⟩ := h7
  obtain ⟨b7, c7, hEll7, hord7, hb7, hj7⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three_with_j
      E P7 7 (by norm_num) hP7
  letI : WeierstrassCurve.IsElliptic (TateCurve35 b7 c7) := hEll7
  have hF7 : c7 ^ 3 - b7 ^ 2 + b7 * c7 = 0 :=
    order_seven_parameter_eq b7 c7 hb7 hord7
  have hc7 : c7 ≠ 0 := by
    intro hc
    rw [hc] at hF7
    norm_num at hF7
    exact hb7 hF7
  let t : ℚ := b7 / c7
  have hb7tc : b7 = t * c7 := by
    dsimp [t]
    field_simp [hc7]
  have hc7param : c7 = t * (t - 1) := by
    have hc7sq : c7 ^ 2 ≠ 0 := pow_ne_zero 2 hc7
    have hfactor : c7 ^ 2 * (c7 - t ^ 2 + t) = 0 := by
      rw [hb7tc] at hF7
      linear_combination hF7
    have hlinear := (mul_eq_zero.mp hfactor).resolve_left hc7sq
    nlinarith
  have hb7param : b7 = t ^ 2 * (t - 1) := by
    rw [hb7tc, hc7param]
    ring
  have ht : t ≠ 0 := by
    intro ht
    apply hb7
    rw [hb7param, ht]
    ring
  have ht1 : t - 1 ≠ 0 := by
    intro ht1
    apply hb7
    rw [hb7param, ht1]
    ring
  have hcurve7 : TateCurve35 b7 c7 =
      TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1)) := by
    rw [hb7param, hc7param]
  letI hEll7' : WeierstrassCurve.IsElliptic
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))) := by
    rw [← hcurve7]
    exact hEll7
  have hq7 : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0 := by
    intro hq
    have hDelta :
        (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).Δ ≠ 0 :=
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).isUnit_Δ.ne_zero
    apply hDelta
    rw [tate_order_seven_delta, hq]
    ring
  let b : ℚ := hauptmodul7 t
  have hb : b ≠ 0 := by
    exact div_ne_zero hq7 (mul_ne_zero ht ht1)
  have hj7' :
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j = E.j := by
    simpa only [hcurve7] using hj7
  have hj7formula :
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j =
        RationalPointsX135.J7Numerator b / b := by
    exact tate_order_seven_j t ht ht1 hq7
  have hj : RationalPointsX135.J5Numerator a / a =
      RationalPointsX135.J7Numerator b / b := by
    calc
      RationalPointsX135.J5Numerator a / a = (TateCurve35 p p).j :=
        hj5formula.symm
      _ = E.j := hj5
      _ = (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j := hj7'.symm
      _ = RationalPointsX135.J7Numerator b / b := hj7formula
  refine ⟨a, b, ha, hb, ?_⟩
  unfold RationalPointsX135.X035FiberEquation
  field_simp [ha, hb] at hj
  simpa [mul_comm] using hj

/-! ## The simultaneous-torsion obstruction and order-`35` exclusion -/

/-- No elliptic curve over `ℚ` has simultaneous rational points of exact
orders five and seven.  The associated Hauptmodul pair gives a noncuspidal
point of `X₀(35)`; its image on `35a1` would have first coordinate both equal
to and different from one. -/
theorem no_simultaneous_orders_five_seven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ (HasRationalPointOfOrder E 5 ∧ HasRationalPointOfOrder E 7) := by
  rintro ⟨h5, h7⟩
  obtain ⟨a, b, _ha, hb, hfiber⟩ :=
    simultaneous_orders_five_seven_to_X035_fiber E h5 h7
  obtain ⟨hx, hX035⟩ := RationalPointsX135.fiber_to_X035 hb hfiber
  have hE35 := RationalPointsX135.map_to_E35 hx hX035
  have hw : RationalPointsX135.quotientW (RationalPointsX135.inverseX a b) = 1 :=
    RationalPointsX135.E35_affine_w_eq_one hE35
  exact RationalPointsX135.quotientW_ne_one hx hw

/-- An elliptic curve over `ℚ` has no rational point of exact order `35`. -/
theorem no_rational_point_of_order_35
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 35 := by
  intro h35
  exact no_simultaneous_orders_five_seven E
    (order35_gives_orders5_and_7 E h35)

/-! ## Position of `35` in the composite-exclusion framework (mirrors `15`) -/

/-- Order `35` is a residual composite: it is above the Mazur cyclic list, is
not in that list, and all its prime divisors (`5`, `7`) are allowed. -/
theorem needs_composite_exclusion_35 : NeedsCompositeExclusion 35 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp57 : p ∣ 5 * 7 := by simpa using hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp57 with hp5 | hp7
    · have hp_eq : p = 5 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
      rw [hp_eq]
      norm_num [allowedPrimeOrders]
    · have hp_eq : p = 7 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7
      rw [hp_eq]
      norm_num [allowedPrimeOrders]

/-- The framework-level order-`35` exclusion: it follows from the generic
future composite-exclusion input, with no extra assumption specific to `35`. -/
theorem no_order35_from_future_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 35 :=
  hcomp E (n := 35) (by norm_num) needs_composite_exclusion_35

end

end MazurProof
