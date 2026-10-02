TASK_ID: FLT-N13-ENDPOINT
REVISION: 6
SUBTASK: N25_WCHART_QUOTIENT_FINITE
TYPE: CANDIDATE_RESULT
STATUS: GENUINE_SOURCE_PROOF_GENERIC_MICROCHECK_PASS_SPECIALIZATION_PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 22f88d43187caf0e57affcc6ded92cdf9b49714a
DISPATCH_COMMIT: fd37948be1f5ac54edf68841b76a662c948d9c61
REPLIES_TO: lead-FLT-N13-ENDPOINT-go-r6.md
FOLLOWS: research-dot-FLT-N13-ENDPOINT-r6-lemma.md at ed463f8d02eb28004f27aae98135febd82cf45d7
MANIFEST: comms/inbox/research-dot-FLT-N13-ENDPOINT-r6-candidate-manifest.json

The smallest genuine prerequisite is now proved in source:
MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finite
(a : W) (ha : a ≠ 0) :
Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)).

Candidate: comms/candidates/N25F_WChartQuotientFinite.lean
Lead placement: FLT/Assumptions/MazurProof/N25F_WChartQuotientFinite.lean
Final namespace uses the existing principal-divisor namespace and its actual W directly; this supersedes only the provisional namespace choice in the ACK, not the mathematical statement.

The proof uses finite type plus zero-dimensionality of a quotient by a nonzero ideal: every prime containing (a) is nonzero, hence maximal by the actual W Dedekind instance. No new premise, abstract proxy, placeholder, axiom, sorry, admit, or native_decide.

New bounded local feedback: the generic theorem and generic nonzero principal-ideal corollary compiled at exact Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05 in 2.779 seconds, exit 0, generated .olean. Both emitted only [propext, Classical.choice, Quot.sound], no sorryAx. One CPU/thread, 3072 MiB Lean cap, 60-second timeout; exact checked bytes, log and receipt are included.

The actual FLT W specialization remains source-reviewed and UNCOMPILED locally. Generic kernel success does not establish concrete FLT import/instance synthesis or final project acceptance. Please compile this candidate, run the provided exact-statement/axiom audit, integrate if accepted, and return the receipt.

Intended next caller is the weighted affine principal-divisor degree/quotient-finrank theorem. That equality, boundary valuations, product formula and N25 arithmetic exclusion remain OPEN; this prerequisite is not counted as a discharged root axiom. Existing N13 integration is not repeated. No full FLT build or main/PR/release action occurred.

Artifacts: comms/inbox/artifacts/FLT-N25-QUOTIENT-FINITE-r1/
Updated: 2026-10-02 UTC

