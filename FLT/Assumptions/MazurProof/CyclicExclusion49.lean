import FLT.Assumptions.MazurProof.TateOriginDivision
import FLT.Assumptions.MazurProof.CyclicExclusion49Polynomial

/-!
# Cyclic order 49 exclusion

A rational point of order 49 can be placed at the origin of a nonsingular Tate
normal form.  The generic odd-order division bridge then gives
`preΨ'₄₉(0) = 0`; exactness gives `preΨ'₇(0) ≠ 0`, removing the only nontrivial
proper divisor.  This file proves that geometric front end and leaves only the
explicit raw Tate-division system as an arithmetic input.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion49

open TateOriginDivision

/-- The raw exact-order-49 Tate division system. -/
def RawOrder49TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧
        ((W b c).preΨ' 49).eval 0 = 0 ∧
        ((W b c).preΨ' 7).eval 0 ≠ 0

/-- Exact order 49 produces the explicit raw Tate-division obstruction. -/
theorem order49_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h49 : HasRationalPointOfOrder E 49) :
    RawOrder49TateObstruction := by
  obtain ⟨b, c, hEll, hord, hb, h49eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 49) (by norm_num) (by decide) h49
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h7eval : ((W b c).preΨ' 7).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 49) (m := 7) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  exact ⟨b, c, inferInstance, hb, h49eval, h7eval⟩

/-- Remaining arithmetic boundary for order 49.
Proved via the compact polynomial reduction in CyclicExclusion49Polynomial. -/
theorem no_raw_order49_tate_obstruction : ¬ RawOrder49TateObstruction :=
  CyclicExclusion49Polynomial.no_raw_order49_tate_obstruction

theorem no_rational_point_of_order_49
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 49 := by
  intro h49
  exact no_raw_order49_tate_obstruction
    (order49_to_raw_tate_obstruction E h49)

end MazurProof.CyclicExclusion49
