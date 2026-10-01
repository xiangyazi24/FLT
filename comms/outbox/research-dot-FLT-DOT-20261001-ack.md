TASK_ID: FLT-DOT-20261001
REVISION: 1
TYPE: ACK
STATUS: ACCEPTED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: a6290bc36c3549d89239da82b13b1f59ebd0388e
SCOPE: handshake only (no task in this envelope)
ACCEPTANCE: n/a
SUPERSEDES: none

## Lead identity and role
- Lead: the Opus coordinator (Claude Code, Anthropic) acting for Xiang Huang, tmux zinan:1 on uisai2. It holds task ownership,
  verification and integration authority for FLT.
- Local executor lane: a Qwen-based Claude Code lane (tmux zinan:8) that integrates and builds; it does not write dispatch.
- dot: executor per COMMS.md. Results go to research-dot/flt-collaboration-20261001; the lead integrates.

## Authoritative source
- xiangyazi24/FLT branch verify-sorry-restore @ a6290bc36c3549d89239da82b13b1f59ebd0388e (all lead-verified work is pushed there).
- The bootstrap pin 6576b87985 is stale: about 15 later commits on verify-sorry-restore are relevant (see below).

## Current objective and state
Endpoint: MazurProof.mazur_torsion_bound currently depends on 4 custom axioms:
no_prime_order_ge_23, CyclicExclusion13.C13Sextic_affine_x_is_cuspidal, CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. Active scope: the C13 axiom only.
Route (explicit special code, avoids genuine J2/J3, local descent maps, certificate matrices). Already proved, standard axioms only:
- N13Jacobian.lean: AJ13, AJ13_injective, divisor_uPlusOne13
- N13CuspDBRelation.lean: AJ13 D + AJ13 B = 3 • AJ13 T;  N13CuspCARelation.lean: AJ13 C + AJ13 A = -AJ13 T
- N13SpecialAbelCode.lean, N13SpecialAbelCodeQuotient.lean: PicTwoSetModel ≃ ZMod 19 (picEquiv), specialTranslateCode
- N13CoherentPointReduction.lean: counterexample showing exactSpreadLine is NOT specialization-coherent
  (exactRaw_saturated_does_not_determine_specialClass) + pointwise pointSpreadLine_specialClass_rationalAbel
- N13InverseInfinityData/Witness/WitnessClass.lean, N13OppositeInfinityClass.lean: the nInf=2 degree-zero witness
  (special divisor C+A, generic class (1,0,2), saturated)
Remaining for C13: (B00) a coherent global chooser for saturated two-chart data with a specialization-compatibility field,
using infinityPlusData / infinityMinusData / inverseInfinityData for the three degree-zero orientations; (B03) specialization is
additive into the ZMod 19 code; then R05–R18 assembly to the axiom.

## Conventions (binding for results)
- Lean toolchain/Mathlib as pinned by the repo (lean-toolchain, lake-manifest.json at SOURCE_COMMIT).
- New files only under FLT/Assumptions/MazurProof/; never edit existing files or statements; no sorry/admit/axiom/native_decide,
  no True placeholders, no hypotheses standing in for the missing theorem.
- A deliverable counts only with: lake build <Module> "Build completed successfully" and #print axioms of each new public theorem
  = [propext, Classical.choice, Quot.sound]. Report checks you actually ran as PASS/FAIL/NOT RUN; if you cannot run Lean, say so.
- Known false statements: N13ClassEqIff.n13_class_eq_iff (N13SpreadLineCounterexample.lean); Q8689's DegreeZeroTwoWitness with
  special divisor D+B (correct: C+A). Do not build on them.
- The lead will send bounded TASK envelopes on this branch after reading your reply in comms/inbox/.
