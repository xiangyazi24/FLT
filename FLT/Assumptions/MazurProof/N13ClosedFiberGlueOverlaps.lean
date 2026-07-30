import FLT.Assumptions.MazurProof.GlueDataClosedBaseChange
import FLT.Assumptions.MazurProof.N13ClosedFiberOverlaps

/-!
# Off-diagonal overlap adapters for the N13 glue data

The full glue data produced by `GlueData.ofGlueData'` stores its overlap
objects behind a dependent diagonal/off-diagonal conditional.  These
lemmas expose the two concrete off-diagonal objects without treating
them as definitional equalities.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberGlueOverlaps

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

/-- The `false,true` object of the full glue data is the ordinary affine
principal-open overlap. -/
theorem affineOverlap_eq :
    D.V (false, true) =
      Spec (.of N13OrdinaryCurveOverlap.AffineOverlap) := by
  simp [D, N13IntegralCurveScheme.glueData,
    CategoryTheory.GlueData.ofGlueData',
    N13IntegralCurveScheme.glueData',
    N13IntegralCurveScheme.overlap]

/-- The `true,false` object of the full glue data is the ordinary
infinity principal-open overlap. -/
theorem infinityOverlap_eq :
    D.V (true, false) =
      Spec (.of N13OrdinaryCurveOverlap.InfinityOverlap) := by
  simp [D, N13IntegralCurveScheme.glueData,
    CategoryTheory.GlueData.ofGlueData',
    N13IntegralCurveScheme.glueData',
    N13IntegralCurveScheme.overlap]

/-- The explicit affine overlap, oriented toward the corresponding
object of the full glue data. -/
def affineOverlapIso :
    Spec (.of N13OrdinaryCurveOverlap.AffineOverlap) ≅
      D.V (false, true) :=
  eqToIso affineOverlap_eq.symm

/-- The explicit infinity overlap, oriented toward the corresponding
object of the full glue data. -/
def infinityOverlapIso :
    Spec (.of N13OrdinaryCurveOverlap.InfinityOverlap) ≅
      D.V (true, false) :=
  eqToIso infinityOverlap_eq.symm

end MazurProof.N13ClosedFiberGlueOverlaps
