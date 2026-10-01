import FLT.Assumptions.MazurProof.N13RationalCurvePointPicardRealization
import FLT.Assumptions.MazurProof.N13InverseInfinityWitnessClass
import FLT.Assumptions.MazurProof.N13CoherentChartComparison

/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate SPECIFICATION only. Lean elaboration / build / axiom checks: NOT RUN.
The imported candidate must be installed under FLT/Assumptions/MazurProof/.
No existence result for this structure is proved here.
-/
namespace MazurProof.N13CoherentChooserSpecification
noncomputable section

abbrev G := N13RationalPointEndgame.G
abbrev Data := N13TwoChartPicardRealization.Data

/-- Pointwise realization and geometric compatibility with rational points.
No additive law for the special code occurs in this specification. -/
structure Chooser where
  choose : G → Data
  generic_eq : ∀ P, (choose P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P
  saturated : ∀ P, N13TwoChartPicardRealization.AffineVerticallySaturated (choose P).charts
  point_compatible : ∀ P : N13RationalPointEndgame.RationalCurvePoint,
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (choose (N13RationalPointEndgame.rationalAbel P)).charts
      (N13RationalCurvePointPicardRealization.data P).realization.charts)

/-- The separate geometric tensor-normalization obligation. A proof must
produce four actual regular functions for every P,Q, with nonzero reductions,
matching principal ideal equations and one common overlap fraction.
This is a target to prove, not an assumed substitute for the end theorem. -/
def HasIntegralTensorComparisons (c : Chooser) : Prop :=
  ∀ P Q : G, Nonempty (N13CoherentChartComparison.IntegralComparison
    (N13TwoChartLineTensor.tensor (c.choose P).charts (c.choose Q).charts)
    (N13TwoChartLineTensor.tensor (c.choose (P + Q)).charts (c.choose 0).charts))

/-- Precise combined existence target; deliberately a proposition definition,
not a theorem or a postulate. Its proof is missing. -/
def GlobalExistenceTarget : Prop :=
  ∃ c : Chooser, HasIntegralTensorComparisons c ∧
    c.choose 0 = N13InfinityPointPicardRealization.infinityPlusData ∧
    c.choose (N13Arithmetic.AJ13 N13Arithmetic.T) =
      N13InfinityPointPicardRealization.infinityMinusData ∧
    c.choose (-N13Arithmetic.AJ13 N13Arithmetic.T) =
      N13InverseInfinityWitness.inverseInfinityData

end
end MazurProof.N13CoherentChooserSpecification
