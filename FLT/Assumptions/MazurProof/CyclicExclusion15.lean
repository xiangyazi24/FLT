import FLT.Assumptions.MazurProof.CyclicOrderReduction

/-!
# Cyclic order 15 exclusion

A rational point of exact order `15 = 3 * 5` gives rational points of
orders `5` and `3` by taking `3 • P` and `5 • P`.  The remaining arithmetic
input is the rational-points computation on `X₁(15)`: over `ℚ`, the curve has
only cuspidal rational points, equivalently no elliptic curve over `ℚ` has
simultaneously a rational point of order `3` and one of order `5`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Elementary order extraction from a point of order 15 -/

theorem addOrderOf_three_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (3 • P) = 5 := by
  rw [addOrderOf_nsmul' P (by norm_num : (3 : ℕ) ≠ 0), hP]
  norm_num

theorem addOrderOf_five_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (5 • P) = 3 := by
  rw [addOrderOf_nsmul' P (by norm_num : (5 : ℕ) ≠ 0), hP]
  norm_num

theorem order15_gives_order5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 5 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨3 • P, addOrderOf_three_nsmul_of_order15 hP⟩

theorem order15_gives_order3
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨5 • P, addOrderOf_five_nsmul_of_order15 hP⟩

theorem order15_gives_orders3_and5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5 :=
  ⟨order15_gives_order3 E hord, order15_gives_order5 E hord⟩

/-! ## Position of `15` in the composite-order reduction framework -/

theorem needs_composite_exclusion_15 : NeedsCompositeExclusion 15 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp35 : p ∣ 3 * 5 := by
      simpa using hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp35 with hp3 | hp5
    · have hp_eq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      rw [hp_eq]
      norm_num [allowedPrimeOrders]
    · have hp_eq : p = 5 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
      rw [hp_eq]
      norm_num [allowedPrimeOrders]

theorem no_order15_from_future_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 :=
  hcomp E (n := 15) (by norm_num) needs_composite_exclusion_15

/-! ## The remaining `X₁(15)` arithmetic input -/

/--
The `X₁(15)` rational-points input.

Mathematically, `X₁(15)` is an elliptic curve of rank `0` over `ℚ`; its
rational points are cusps.  In the present torsion language this says that no
elliptic curve over `ℚ` has both a rational point of order `3` and a rational
point of order `5`.
-/
theorem x1_15_no_simultaneous_rational_3_and_5_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ (HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5) := by
  sorry

/-- No elliptic curve over `ℚ` has a rational point of exact order `15`. -/
theorem no_rational_point_of_order_15
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 := by
  intro hord
  exact x1_15_no_simultaneous_rational_3_and_5_torsion E
    (order15_gives_orders3_and5 E hord)

end MazurProof
