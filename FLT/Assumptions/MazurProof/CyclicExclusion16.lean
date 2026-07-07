import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.RationalPointsN16

/-!
# Cyclic order 16 exclusion

This file records the cyclic `N = 16` composite exclusion needed by
`CyclicOrderReduction`.

The noncyclic statement `ZMod 2 × ZMod 16` is handled in `DescentBridgeN16`.
That does not imply the cyclic case.  Here the cyclic case is separated into:

* elementary order extraction from a point of exact order `16`;
* the bookkeeping fact that `16` is one of the composite residual orders;
* a cyclic `X₁(16)`/Tate-normal-form bridge to the existing N=16 obstruction
  curve `w² = u³ - u² - u`;
* the already-proved rational-points computation in `RationalPointsN16`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Elementary order extraction from a point of order 16 -/

theorem addOrderOf_two_nsmul_of_order16
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 16) :
    addOrderOf (2 • P) = 8 := by
  rw [addOrderOf_nsmul' P (by norm_num : (2 : ℕ) ≠ 0), hP]
  norm_num

theorem addOrderOf_four_nsmul_of_order16
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 16) :
    addOrderOf (4 • P) = 4 := by
  rw [addOrderOf_nsmul' P (by norm_num : (4 : ℕ) ≠ 0), hP]
  norm_num

theorem addOrderOf_eight_nsmul_of_order16
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 16) :
    addOrderOf (8 • P) = 2 := by
  rw [addOrderOf_nsmul' P (by norm_num : (8 : ℕ) ≠ 0), hP]
  norm_num

theorem order16_gives_order8
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 16) :
    HasRationalPointOfOrder E 8 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨2 • P, addOrderOf_two_nsmul_of_order16 hP⟩

theorem order16_gives_order4
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 16) :
    HasRationalPointOfOrder E 4 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨4 • P, addOrderOf_four_nsmul_of_order16 hP⟩

theorem order16_gives_order2
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 16) :
    HasRationalPointOfOrder E 2 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨8 • P, addOrderOf_eight_nsmul_of_order16 hP⟩

/-! ## Position of `16` in the composite-order reduction framework -/

theorem needs_composite_exclusion_16 : NeedsCompositeExclusion 16 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp_le : p ≤ 16 := Nat.le_of_dvd (by norm_num) hpdvd
    have hp_ge : 2 ≤ p := hp.two_le
    interval_cases p
    all_goals simp [allowedPrimeOrders] at hpdvd ⊢
    all_goals norm_num at hp

theorem no_order16_from_future_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 16 :=
  hcomp E (n := 16) (by norm_num) needs_composite_exclusion_16

/-! ## Cyclic `N = 16` modular-curve bridge -/

/--
The cyclic `N = 16` Tate/Kubert computation.

Mathematically, a rational point of exact order `16` gives a noncuspidal
rational point on `X₁(16)`.  The explicit Tate normal form and the standard
descent to the N=16 obstruction coordinates produce a rational point on
`w² = u³ - u² - u`; the cuspidal parameters are exactly
`E_N16_DegenerateParameter`.
-/
def CyclicOrder16KubertBridge : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 16 →
      ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u

/--
Residual cyclic `N = 16` bridge.

This is the cyclic-order-specific modular-curve computation.  After this
bridge, the contradiction is supplied by the elementary rational-points proof
in `RationalPointsN16`.
-/
theorem cyclic_order_16_kubert_bridge : CyclicOrder16KubertBridge := by
  intro E hEll horder
  sorry

/-! ## Exclusion theorem -/

theorem no_rational_point_of_order_16_of_kubert_bridge
    (hbridge : CyclicOrder16KubertBridge)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 16 := by
  intro horder
  rcases hbridge E horder with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (RationalPointsN16.obstruction_curve_N16_from_elementary u w hcurve)

/-- No elliptic curve over `ℚ` has a rational point of exact order `16`. -/
theorem no_rational_point_of_order_16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 16 :=
  no_rational_point_of_order_16_of_kubert_bridge cyclic_order_16_kubert_bridge E

theorem no_rational_point_of_order_eq_16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ} (hn : n = 16) :
    ¬ HasRationalPointOfOrder E n := by
  subst hn
  exact no_rational_point_of_order_16 E

end MazurProof
