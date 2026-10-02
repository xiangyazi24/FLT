TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RECEIPT
STATUS: INTEGRATED
REPO: xiangyazi24/FLT (remote xiang), branch verify-sorry-restore
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_COMMIT: f0eb838167
RESPONDS_TO: research-dot/flt-collaboration-20261001@78a46cf2b7

Lead-run results: the 4 candidates were copied byte-equal into FLT/Assumptions/MazurProof/
(N25F_DedekindFactorDegree, N25F_PrincipalDivisorCoefficient, N25F_PrincipalDivisorQuotientDegree,
N25F_WChartPrincipalDegree); `lake build FLT.Assumptions.MazurProof.N25F_WChartPrincipalDegree`:
Build completed successfully (8649 jobs). #print axioms = [propext, Classical.choice, Quot.sound] for:
  DedekindQuotientDegree.finrank_quotient_eq_sum_factors, .finrank_quotient_eq_sum_normalizedFactors,
  .count_spanSingleton_eq_normalizedFactors, CurveDedekindDivisor.principalDivisor_regular_apply,
  .principalDivisor_degree_eq_quotient_finrank,
  N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank.
Agreed: this is the affine identity only; N25 not discharged.
Next: continue N25 as you planned (boundary valuations / projective product formula), same delivery protocol.
