import FLT.Assumptions.MazurProof.CyclicOrderReduction

/-!
# Cyclic order 35 exclusion

A rational point of exact order `35 = 5 · 7` gives, by taking `7 • P` and
`5 • P`, simultaneous rational points of order `5` and `7` on the same curve.
Geometrically this is a non-cuspidal rational point on the fiber product
`X₁(5) ×_{j-line} X₁(7)` (equivalently `X₁(35)`), which has only cuspidal
rational points over `ℚ`.

This file discharges the **reduction** genuinely — no axiom, no `sorry`,
no `native_decide`.  The order-`5` and order-`7` subpoints are extracted with
the existing, axiom-free prime-order reduction lemma
`exists_point_of_prime_order_of_dvd`, and the order-`35` exclusion is then a
one-line consequence of the simultaneous `5`-and-`7` obstruction.

The remaining arithmetic input — that no elliptic curve over `ℚ` carries
*both* a rational point of order `5` and one of order `7` — is not formalized
in Mathlib or elsewhere in this development.  It is therefore surfaced here
as an explicit hypothesis `NoSimultaneousOrder5And7`, in exactly the way
`FutureCompositeExclusions` is a parameter rather than a new axiom.  This keeps
the file axiom-free and `sorry`-free while making the precise open input visible
in the statement's type.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

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

/-! ## The `X₁(35)` simultaneous-torsion input, as an explicit hypothesis -/

/-- The `X₁(35)` arithmetic input: the elliptic curve `E / ℚ` has no
simultaneous rational `5`- and `7`-torsion.  Equivalently, `E` gives no
non-cuspidal rational point on the fiber product `X₁(5) ×_{j-line} X₁(7)`.

This is surfaced as a hypothesis rather than an axiom, mirroring
`FutureCompositeExclusions`; its arithmetic proof is not yet formalized. -/
def NoSimultaneousOrder5And7 (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ¬ (HasRationalPointOfOrder E 5 ∧ HasRationalPointOfOrder E 7)

/-! ## Order-`35` exclusion via the order-`5` and order-`7` subpoints -/

/-- No elliptic curve over `ℚ` satisfying the `X₁(35)` input has a rational
point of exact order `35`.

Genuine reduction (axiom-free, `sorry`-free): the order-`35` point is split into
its order-`5` and order-`7` subpoints via `order35_gives_orders5_and_7`, which
contradicts the simultaneous-torsion hypothesis. -/
theorem no_rational_point_of_order_35
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hX35 : NoSimultaneousOrder5And7 E) :
    ¬ HasRationalPointOfOrder E 35 :=
  fun h => hX35 (order35_gives_orders5_and_7 E h)

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

end MazurProof
