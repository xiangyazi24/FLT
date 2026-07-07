import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.DescentBridgeN14

/-!
# Cyclic exclusion for order 14

This file records the cyclic `N = 14` composite exclusion needed by
`CyclicOrderReduction`.

The existing `DescentBridgeN14` file excludes the noncyclic subgroup
`ZMod 2 × ZMod 14`; that is not enough for a cyclic point of order `14`.
Here the cyclic case is routed through its own Tate/Kubert modular-curve
bridge to the same `N = 14` obstruction curve

`w² = u³ + u² - 2u`.

The remaining external computation is isolated as
`cyclic_order_14_kubert_bridge`: a rational point of order `14` gives a
nondegenerate rational point on the `N = 14` obstruction curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Order 14 is a composite residual -/

theorem needs_composite_exclusion_14 : NeedsCompositeExclusion 14 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp_le : p ≤ 14 := Nat.le_of_dvd (by norm_num) hpdvd
    have hp_ge : 2 ≤ p := hp.two_le
    interval_cases p
    all_goals simp [allowedPrimeOrders] at hpdvd ⊢
    all_goals norm_num at hp

/-! ## Elementary prime-order reductions from a point of order 14 -/

theorem order14_gives_order7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 14) :
    HasRationalPointOfOrder E 7 :=
  exists_point_of_prime_order_of_dvd (E := E) (n := 14) (p := 7)
    (by norm_num) (by norm_num) (by norm_num) h

theorem order14_gives_order2
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 14) :
    HasRationalPointOfOrder E 2 :=
  exists_point_of_prime_order_of_dvd (E := E) (n := 14) (p := 2)
    (by norm_num) (by norm_num) (by norm_num) h

/-! ## Cyclic `N = 14` modular-curve bridge -/

/--
The cyclic `N = 14` Tate/Kubert computation.

Mathematically, one starts from the Tate normal form with a marked point of
order `7`, imposes that the marked lift has order `14`, and obtains a rational
point on `w² = u³ + u² - 2u`.  Nondegeneracy excludes the cuspidal parameters.
-/
def CyclicOrder14KubertBridge : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 14 →
      ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u

/--
Residual cyclic `N = 14` bridge.

This is the only cyclic-order-specific modular-curve computation in this file;
the contradiction after this point is formal.
-/
theorem cyclic_order_14_kubert_bridge : CyclicOrder14KubertBridge := by
  intro E hEll horder
  sorry

/-! ## Exclusion theorem -/

theorem no_rational_point_of_order_14_of_kubert_bridge
    (hbridge : CyclicOrder14KubertBridge)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 := by
  intro horder
  rcases hbridge E horder with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)

/-- No elliptic curve over `ℚ` has a rational point of order `14`. -/
theorem no_rational_point_of_order_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 :=
  no_rational_point_of_order_14_of_kubert_bridge cyclic_order_14_kubert_bridge E

theorem no_rational_point_of_order_eq_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ} (hn : n = 14) :
    ¬ HasRationalPointOfOrder E n := by
  subst hn
  exact no_rational_point_of_order_14 E

end MazurProof
