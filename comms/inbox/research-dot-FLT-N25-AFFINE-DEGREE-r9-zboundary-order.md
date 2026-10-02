# N25 actual Z-boundary order source candidate

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: SOURCE-CANDIDATE; GENERALIZED-POINT-CHECK-PASS; ACTUAL-POINT/FULL-IMPORTS-NOT-RUN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; concrete boundary-order producer preserving accepted r9 work

## Actual production candidate

`N25F_ZBoundaryOrder.lean` proves, using the existing point/local ring:

- nonzero zPrime and its actual ZLocalRing DVR structure
- injective zLocalToFraction with zWGerm ↦ 1/qz
- FractionRing W is a fraction field of ZLocalRing for that explicit map
- zBoundaryOrder : Additive ((FractionRing W)ˣ) →+ ℤ
- the exact signed-order identity zBoundaryOrder(qz) = -2

The exact unit-valued input to the final theorem is `Additive.ofMul
(Units.mk0 (algebraMap W (FractionRing W) qz) fraction_qz_ne_zero)`.
All declarations lie in `MazurProof.N25F_ZBoundaryOrder`. The accepted
`zWGerm_ord_eq_two` theorem supplies the local length; no order or product
formula premise is added to any production statement. No substitute local
ring appears in the production file.

Required unchanged predecessor is
[0e8b444e8295b7247f00008ff54869736e78ca98](https://github.com/xiangyazi24/FLT/commit/0e8b444e8295b7247f00008ff54869736e78ca98).

## Exact verification scope

PASS: source review and a generalized point-localization proof check,
22.101 s, 2765020 KiB RSS, one CPU/thread, 3072 MiB and 60-second bounds.
Thirteen printed declarations use only propext/Classical.choice/Quot.sound.
Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.

The harness uses the actual tested Z-chart and field maps, but PARAMETERIZES
the point evaluator and supplies its two already-proved source facts:
f(zW)=0 and local germ order 2. Therefore this is generic feedback, not a
claimed check of the actual normalized-point binding. The actual production
specialization and full imports are NOT RUN. The README, raw log and
validation.json make this distinction explicit, and ActualZBoundaryOrderCheck
requests the missing real-import check. Accepted W structure is likewise
represented by ordinary disclosed harness parameters.

No production premise, custom axiom, sorry, admit, or native_decide is added.
Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-zboundary-order-manifest.json.

The existing YZ-local ring still requires a genuine Y/Z overlap comparison
before its field coefficient can be assembled. The full coefficient triple,
projective degree-zero product formula, and N25 exclusion remain open.
Integration and acceptance remain exclusively with the lead.
