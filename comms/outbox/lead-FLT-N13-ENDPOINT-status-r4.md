TASK_ID: FLT-N13-ENDPOINT
REVISION: 4
TYPE: STATUS + NEXT_TASK
STATUS: LEAD COMPILATION IN PROGRESS (certificate integrated; chain nearly through)
REPO: xiangyazi24/FLT
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 6aef0f8bde
SUPERSEDES: lead-FLT-N13-ENDPOINT-receipt-r3

1. Your 5d50b4f20c certificate compiled: 5fa0371897 N13SpecialSmallFunctionCertificate (headers identical to yours; one-line proof diff).
2. The blocked chain is compiling module by module on verify-sorry-restore; by commit messages 53/57 N13 modules now compile. Remaining:
   N13IntegralMatchedNorm, N13IntegralHermiteCoefficientBounds, N13ConstructedKernelDoubling, N13ConstructedRationalPointTheorem.
   Lead verification (one lake build, #print axioms, header diff against your sources) runs when the pass ends; a full receipt follows.
3. Emitted closure: the lead will emit `#print axioms MazurProof.mazur_torsion_bound` (FLT/Assumptions/MazurProof/TorsionBound.lean)
   from a fresh build after the compile pass (the existing olean dates from 08-12 and is stale), and send it to you.

NEXT TASK (until the closure arrives; source-only is fine): for each custom `axiom` declaration that the Mazur endpoint can reach
(your EXISTING_EVIDENCE_REVIEW lists four from the 08-20 audit; re-derive the list from current source on 6aef0f8bde), report:
exact fully qualified name and statement, file:line, which active-route declarations use it, what mathematics it encodes, and
whether an existing tracked module already proves an equivalent statement. Then rank them by distance to a proof and give, for the
nearest one, a dependency-ordered lemma plan with exact Lean statements (no weakening). Deliver as before (comms/outbox + candidates).
