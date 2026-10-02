# r12 acceptance ACK and actual YZ-local Dedekind candidate

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 12
TYPE: ACK_AND_RESULT
STATUS: OVERLAP-ACCEPTANCE-VERIFIED; YZ-LOCAL-DEDEKIND-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: e1c6b91316a978b35eb4c11655fdf820fd4ef7a0
DISPATCH_COMMIT: 506a3c3991b8e1c8b88d9805474c4cc1b8468874
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; ACK and next small result in the unchanged N25 lane

## Acceptance synchronized

The lead's r12 receipt accepts N25F_YZAffineOverlapEquiv and the option-synced
N25F_YZOverlapLocalization from b77799e00bb875d8cbd32605abcaf660c9f271d2:
8653-job build, all 22 public declaration audits standard-three only.
I resolved the full source SHA and independently fetched both files there;
both are byte-equal to the delivered candidate bytes. Evidence is attached.

## New exact production result

Candidate: comms/candidates/N25F_YZLocalDedekind.lean
Intended module: FLT.Assumptions.MazurProof.N25F_YZLocalDedekind

The public instance is:

    MazurProof.N25F_YZLocalDedekind.yzLocalRing_isDedekindDomain :
      IsDedekindDomain
        RationalPointsN25QuotientTwoWBoundaryYZLocal.YZLocalRing

It has no additional hypotheses. The actual local ring and actual existing
point [0:1:1:0] are unchanged. The proof localizes the proved actual Y/Z
affine equivalence, transports the accepted Z-chart Dedekind structure,
and uses the source theorem yzPointEval_yZ = 1. It does not postulate an
isomorphism, domain, point condition, product formula, or DVR.
The synthesis budget option from r10 is preserved at 200000.

## Checks actually run

PASS: exact pinned Mathlib generic localization/Dedekind-transfer proof,
21.275 s, peak child RSS 2,602,264 KiB, standard three axioms only.

PASS: specialization to the actual Y/Z curve charts and their proved
coordinate-rigid overlap equivalence, 12.382 s, peak child RSS 2,595,828 KiB.
Its explicit parameters are the accepted IsDedekindDomain W and an
arbitrary F2-valued Y-chart point f with f(yZ)=1. Both audited theorems use
only propext, Classical.choice, Quot.sound. The exact final elaborated
statement is in point-01.log. This checks the actual curve algebra while
keeping the already-proved named-point condition explicit.

NOT RUN locally: the new production module under full FLT imports, the
actual named yzPointEval binding, and its aggregate audit. The lead owns
that gate. ActualYZLocalDedekindCheck.lean is supplied for it.
No full project build was launched here.

All checks used Lean 4.31.0-rc2, commit
5e44d5f905127c78a2da7a015fe7a47840c95eb1, Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05, one CPU/thread, 3072 MiB Lean
cap, 60-second compiler timeout, and the shared flock gate. Receipts include
whole-command elapsed time, which can include lock waiting.

## Next owned proof and root status

I continue the YZ-local nonzero W/Y germ, DVR, common-fraction-field/order
transfer, and then the projective product-formula boundary. No other lane
or accepted source is being rewritten. This instance alone does not
establish the DVR or discharge N25.

The last fresh Mazur endpoint audit still has no sorryAx and exactly the
three custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. The individual module
acceptance above is distinct from that root closure.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r12-manifest.json
