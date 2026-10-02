TASK_ID: FLT-N13-ENDPOINT
REVISION: 2
TYPE: RECEIPT + NEXT_TASK
STATUS: PARTIAL — 29/57 modules compiled and committed; 2 FAIL; 26 blocked behind them
REPO: xiangyazi24/FLT
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: c200807b37
SUPERSEDES: FLT-N13-ENDPOINT r1

Lead-run gate (one `lake build` of all 29 modules: "Build completed successfully (8860 jobs)"; `#print axioms` on all 243 public
theorems: 243 x [propext, Classical.choice, Quot.sound], 0 sorryAx). All under FLT/Assumptions/MazurProof/:
  COMPILED: N13NormalizedHermiteResidual N13GoodPointFirstJet N13EffectiveInfinityRepair N13EffectiveGraphData N13InfinityChartMarking
  N13OverlapBranchCompatibility N13PrimitiveVerticalPresentation N13PrincipalBranchBalance N13PrincipalBranchIdeals
  N13PrimitiveAffineComparison N13InfinityBranchJets N13InfinityBranchJetLift N13InfinityIdealApproximation N13LocalizationAdicPatch
  N13GenericInfinityComparison N13IntegralPrincipalComparison N13MarkedQuadraticExistence N13MarkedEffectiveData
  N13MarkedTensorComparison N13EffectiveDataCompatibility N13PointDataCertificates N13SpecialInfinityBranchJets
  N13SpecialComparisonFactorPair N13SpecialAffineNorm N13SpecialLaurentBranches N13SpecialOverlapBranches
  N13SpecialBranchFaithfulness N13SpecialDivisorBranchOrders N13SpecialSmallNumerator

Header diffs vs your branch (meaning unchanged, please adopt in future drafts):
  - N13NormalizedHermiteResidual: `residual` -> `N13HermiteResidualDivisibility.residual` (ambiguous name).
  - N13PrimitiveVerticalPresentation.exists_affine_primitive_fraction_presentation: `(2 : CommonField)` -> `algebraMap Affine CommonField 2`.
  - N13GoodPointFirstJet: `abbrev Dual`/`Good` take `(K : Type u) [Field K]` explicitly; `include hc hd in` before
    value_derivative_of_square_graph (section variables were not included automatically).
  - N13EffectiveInfinityRepair: added `local instance : DecidableEq K := Classical.decEq K`.
  - New helper lemmas only: includePower_injective, includePower_ne_zero, two_eq_C, base_X, base_X', polynomialJet_apply.

FIRST BLOCKERS (files untouched by the lead; these gate the remaining 26 incl. N13ConstructedRationalPointTheorem):
  1. N13SpecialSmallFunctionCertificate.lean
     - l.20 "failed to compile definition, consider marking it as 'noncomputable'" (no noncomputable section);
     - l.33:70 "unexpected token 'set_option'; expected 'lemma'" (doc comment directly before `set_option ... in`);
     - l.44 jet_polynomials_satisfy_equations proved by `decide` on divisibility in F2[X]: "failed to synthesize Decidable".
       Mathlib Polynomial is noncomputable; needs explicit cofactor witnesses (p = q * r checked by ring/norm_num/decide on coeffs)
       or a computable representation with a proved bridge.
     Blocks: SpecialCertifiedNumerator, SpecialRootJetAgreement, SpecialFiniteBranchJets, SpecialJetOrder, SpecialSixJetOrders,
     SpecialFiniteBranchFaithfulness, SpecialFinitePointOrders, SpecialDegreeFourCode.
  2. N13CalibratedChooser.lean
     - l.28 `Polynomial.mod_eq_of_lt` unknown (removed/renamed in this Mathlib);
     - l.34 `compute_degree` applied to a goal that is not natDegree/degree/coeff;
     - l.54, l.60 maxHeartbeats exceeded.
  Then N13ConstructedSpecialization (needs both) and the straight 16-module chain N13ConstructedReductionClassifier ...
  N13ConstructedRationalPointTheorem.

NEXT TASK (priority over the sorryAx-closure task from r1): deliver repaired candidates for blockers 1 and 2 against source
c200807b37, statements unchanged, as before (uncompiled is fine; the lead compiles). If any statement in those two files is false or
not decidable as stated, say so with the exact declaration and reason instead of changing it.
