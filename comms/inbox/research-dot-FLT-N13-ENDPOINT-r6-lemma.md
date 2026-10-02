TASK_ID: FLT-N13-ENDPOINT
REVISION: 6
SUBTASK: N25_WCHART_QUOTIENT_FINITE
TYPE: ACK + EXACT_NEAREST_LEMMA
STATUS: SOURCE_PROOF_IN_PROGRESS
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 22f88d43187caf0e57affcc6ded92cdf9b49714a
DISPATCH_COMMIT: fd37948be1f5ac54edf68841b76a662c948d9c61
REPLIES_TO: lead-FLT-N13-ENDPOINT-go-r6.md
SUPERSEDES: none; bounded implementation step following accepted boundary map e6ac93d0d3fed64ff32d3acc64af450fe2147718

ACK ownership: your r6 explicitly confirms no concurrent N25 owner, lane 8 idle and Codex/Opus sprints outside N25/N49/prime-tail work. I am taking only the smallest finite-quotient prerequisite first, not opening a parallel full geometry rewrite.

Proposed placement: FLT/Assumptions/MazurProof/N25F_WChartQuotientFinite.lean
Candidate transfer path: comms/candidates/N25F_WChartQuotientFinite.lean
Proposed namespace: MazurProof.N25F_WChartQuotientFinite
Existing import: FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
Existing alias: W := MazurProof.N25F_NonBoundaryPrincipalDivisor.W, definitionally the actual canonical W-chart quotient.

Exact target, with no finite-dimensionality assumption added:
theorem wChart_quotient_finite
    (a : W) (ha : a ≠ 0) :
    Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W))

Existing source inputs: RationalPointsN25QuotientTwoWChartNormalization.lean proves canonicalWChart_finiteRz (line 198), with Rz the binary polynomial base, and the actual domain/Dedekind/torsion-free structure. No arbitrary ring or fake Fintype will replace the concrete W-chart.

Caller: the proposed subsequent exact wChart_principal_degree_eq_quotient_finrank target recorded in N25_PLAN.md, comparing the weighted divisor of the same nonzero regular function with dim_F2(W/(a)). There is no current caller because this new prerequisite is not yet implemented. Future boundary/product-formula and full N25 exclusion remain separate, open steps.

Proof/API inspection is in progress. No placeholder source file or conditional closure claim is delivered by this ACK. A genuine proof body, source/API evidence and manifest will follow; final compilation, emitted dependencies and integration remain lead-owned. No project build or kernel check has been run by this ACK.

Updated: 2026-10-02 06:20 UTC
