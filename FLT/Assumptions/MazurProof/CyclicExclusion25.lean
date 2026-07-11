import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# Cyclic order 25 exclusion

A rational point of order 25 on E/ℚ. This is one of the hardest composite
exclusions: X₁(25) has genus 12, and no rank-0 elliptic bridge exists
at level 25.

The generic odd-order Tate bridge reduces the geometric statement to a precise
raw division-polynomial condition.  Exact order `25` gives

* `preΨ'₂₅(0) = 0`;
* `preΨ'₅(0) ≠ 0`, excluding the proper order-five factor;
* a nonsingular Tate normal form with `b ≠ 0`.

Only the final arithmetic assertion that this system has no rational solution
is retained as a named input.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion25

open TateOriginDivision

/-- The exact raw Tate-division system left by a rational point of order 25.
The nonvanishing order-five evaluation removes the only nontrivial proper
divisor of 25. -/
def RawOrder25TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧
        ((W b c).preΨ' 25).eval 0 = 0 ∧
        ((W b c).preΨ' 5).eval 0 ≠ 0

/-- Exact order 25 produces the explicit raw Tate-division obstruction. -/
theorem order25_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    RawOrder25TateObstruction := by
  obtain ⟨b, c, hEll, hord, hb, h25eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 25) (by norm_num) (by decide) h25
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h5eval : ((W b c).preΨ' 5).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 25) (m := 5) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  exact ⟨b, c, inferInstance, hb, h25eval, h5eval⟩

/-- Remaining arithmetic boundary for order 25: the displayed exact-order
Tate division system has no rational solution. -/
axiom no_raw_order25_tate_obstruction : ¬ RawOrder25TateObstruction

theorem no_rational_point_of_order_25
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 25 := by
  intro h25
  exact no_raw_order25_tate_obstruction
    (order25_to_raw_tate_obstruction E h25)

end MazurProof.CyclicExclusion25
