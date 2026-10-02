import FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Zero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

/-- A nonzero regular function on the actual W-chart has a finite-dimensional
zero-scheme over the binary field. -/
theorem wChart_quotient_finite (a : W) (ha : a ≠ 0) :
    Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) := by
  apply (Module.finite_iff_krullDimLE_zero
    (ZMod 2) (W ⧸ Ideal.span ({a} : Set W))).2
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  exact hP.1.1.isMaximal
    (ne_bot_of_le_ne_bot (Ideal.span_singleton_eq_bot.not.mpr ha) hP.1.2)

end MazurProof.N25F_NonBoundaryPrincipalDivisor

