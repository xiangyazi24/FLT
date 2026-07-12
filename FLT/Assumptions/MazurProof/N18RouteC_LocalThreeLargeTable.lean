import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSolubility

namespace MazurProof.N18RouteC.LocalThree

/-- Exhaustive two-variable certificate for the chart `D = 1`. -/
theorem large_scaled_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, IsUnit5 U ∧ W * 2 = U ^ 3) → InDualLine W := by
  native_decide +revert

end MazurProof.N18RouteC.LocalThree
