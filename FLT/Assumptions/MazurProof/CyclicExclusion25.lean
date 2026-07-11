import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# Cyclic order 25 exclusion

A rational point of order 25 on E/ℚ. This is one of the hardest composite
exclusions: X₁(25) has genus 12, and no rank-0 elliptic bridge exists
at level 25.

The generic odd-order Tate bridge and the explicit factorisation in
`TateOrder25Factor` reduce the geometric statement to one primitive polynomial
condition.  Exact order `25` gives

* `preΨ'₂₅(0) = 0`;
* `preΨ'₅(0) ≠ 0`, excluding the proper order-five factor;
* a nonsingular Tate normal form with `b ≠ 0`;
* the primitive degree-40 equation `F₂₅(b,c) = 0` after the proper order-five
  factor has been removed.

Only the final rational-point assertion for this explicit affine model of
`X₁(25)` is retained as a named input.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion25

open TateOrder25Factor

/-- Compatibility name for the exact raw Tate-division system. -/
abbrev RawOrder25TateObstruction : Prop :=
  TateOrder25Factor.RawOrder25TateObstruction

/-- The explicit primitive degree-40 order-25 obstruction. -/
abbrev ExplicitOrder25Obstruction : Prop :=
  TateOrder25Factor.ExplicitOrder25Obstruction

/-- Exact order 25 produces the explicit raw Tate-division obstruction. -/
theorem order25_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    RawOrder25TateObstruction :=
  TateOrder25Factor.order25_to_raw_tate_obstruction E h25

/-- Remaining arithmetic boundary for order 25: the explicit primitive
degree-40 factor has no noncuspidal rational zero. -/
axiom no_explicit_order25_obstruction : ¬ ExplicitOrder25Obstruction

theorem no_rational_point_of_order_25
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 25 := by
  intro h25
  exact no_explicit_order25_obstruction
    (TateOrder25Factor.order25_to_explicit_obstruction E h25)

end MazurProof.CyclicExclusion25
