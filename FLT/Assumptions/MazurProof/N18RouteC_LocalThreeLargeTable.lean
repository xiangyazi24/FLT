import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSolubility

namespace MazurProof.N18RouteC.LocalThree

set_option maxRecDepth 4000

/-- Certificate for the chart `D = 1`.  The dual-line membership witness is read
off `dualData`; the remaining search is over the hypothesis `∃ U`. -/
set_option maxHeartbeats 0 in
theorem large_scaled_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, IsUnit5 U ∧ W * 2 = U ^ 3) → InDualLine W := by
  intro W hW hU
  refine ⟨(dualData W).1, (dualData W).2, ?_, ?_⟩
  · revert W; decide
  · revert W; decide

end MazurProof.N18RouteC.LocalThree
