import FLT.Assumptions.MazurProof.N13ConstructedHalfIntegralSpread
import FLT.Assumptions.MazurProof.N13SelectedRootContractedFrame

/-!
# The exact contracted-frame seam for the constructed N13 half

This adapter specializes the factor-level Čech output to the Padé-selected
half retained by the two-surjectivity proof.  It makes the remaining
producer explicit without asserting coefficientwise integrality of the
canonical affine graph.
-/

namespace MazurProof.N13ConstructedHalfContractedFrame

noncomputable section

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- The exact module-valued Čech datum still required for one constructed
half.  Its affine factors lie in the raw contraction and its multiplier
inverse, not merely in the divisorial hull. -/
abbrev Data (P : G) : Type :=
  N13SelectedRootContractedFrame.FactorData
    (N13ConstructedHalfIntegralSpread.rootIdeal P)

/-- A contracted frame closes the selected-half affine spread
invertibility theorem immediately and non-circularly. -/
theorem integralRootHull_isUnit
    (P : G) (D : Data P) :
    IsUnit
      (N13ConstructedHalfIntegralSpread.integralRootHull P) := by
  exact D.isUnit_divisorialHull
    (N13ConstructedHalfIntegralSpread.rootIdeal_ne_bot P)
    (N13ConstructedHalfIntegralSpread.rootIdeal_isUnit P)

end

end MazurProof.N13ConstructedHalfContractedFrame
