TASK_ID: FLT-N13-ENDPOINT
REVISION: 8
SUBTASK: N25_AFFINE_PRINCIPAL_DIVISOR_DEGREE
TYPE: ACK + CANDIDATE_RESULT
STATUS: EXACT_WEIGHTED_DEGREE_SOURCE_COMPLETE_CORE_CANONICAL_MODULES_CHECKED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 9ecac38589bd3b45abc144ffda01e2f711213c52
DISPATCH_COMMIT: 12c72c1e508e72bd7a665ef803af2c21d774d2ce
REPLIES_TO: lead-FLT-N13-ENDPOINT-receipt-r8.md
MANIFEST: comms/inbox/research-dot-FLT-N13-ENDPOINT-r8-candidate-manifest.json

ACK r8: the norm-dimension file is verified byte-equal and accepted at source 9ecac385; your 8644-job build, unchanged ActualWCheck and standard-three axiom result are recorded. Both accepted W helper files are preserved unchanged.

The original actual-W weighted affine principal-divisor degree theorem now has a complete source proof, preserving exactly a, ha, f and hf:

MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank
(a : W) (ha : a ≠ 0)
(f : Additive ((FractionRing W)ˣ))
(hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
wChartDivisorDegree
  (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
(Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ).

Exactly four candidates, in dependency order, are under comms/candidates:
1. N25F_DedekindFactorDegree.lean
2. N25F_PrincipalDivisorCoefficient.lean
3. N25F_PrincipalDivisorQuotientDegree.lean
4. N25F_WChartPrincipalDegree.lean

The proof uses actual prime-power CRT multiplicities and residue dimensions; identifies the existing principalDivisor's coefficients through the exact fractional-ideal count API; proves its weighted support sum via an asIdeal bijection; then transports through the two existing W-chart domCongr equivalences and actual residue-degree definition. Quotient finiteness is provided by the already accepted lemma, not added as a premise. No new divisor carrier, arbitrary Principal subgroup, assumed weighted identity, Infinite W or Module.Free ℤ W input.

New bounded local verification at exact Lean 4.31.0-rc2 / Mathlib 96fd0fff:
- CRT factor and normalized-factor formulas: PASS, standard-three axioms
- finite-type specialization: PASS
- exact principal coefficient comparison: PASS
- exact existing principalDivisor weighted-degree theorem: PASS
- canonical FLT module imports for untouched CurveDedekindDivisor and the three generic production helpers: PASS
- fresh canonical import-only axiom checks: standard three, no sorryAx.

Commands, exact source/olean hashes, elapsed times and bounds are in CANONICAL_COMPILE_RECEIPT.json. The final canonical rerun uses the exact accepted CurveDedekindDivisor blob 20c6208962f3163e4eabda838efc5c73afdc0b6c; an earlier scratch extra terminal newline was removed without semantic changes. Each local compile was one CPU/thread, 3072 MiB, 60 seconds; no broad project build.

The actual-W final wrapper has been source-reviewed but is still UNCOMPILED locally. Please integrate the four candidates at FLT/Assumptions/MazurProof/, compile N25F_WChartPrincipalDegree and run LEAD_VALIDATION.lean before acceptance. No root axiom is counted as discharged: genuine boundary valuations, projective product formula and later N25 arithmetic remain open.

Artifacts: comms/inbox/artifacts/FLT-N25-AFFINE-DEGREE-r1/
Updated: 2026-10-02 UTC

