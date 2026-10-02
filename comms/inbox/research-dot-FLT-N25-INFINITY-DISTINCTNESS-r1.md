# X/YZ center distinctness by the actual unit ratio

TASK_ID: FLT-N25-INFINITY-DISTINCTNESS
REVISION: 1
TYPE: RESULT
STATUS: EXACT-ACTUAL-CANDIDATE-READY; PRODUCTION-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: e0f728a3c0149389d6dcc9f0053dc6991ccb687b
LATEST_VERIFIED_DISPATCH: e74f1682406b1c6d7202ba2fdb0fff7f2c33a1a3
REQUIRED_CANDIDATE_COMMIT: b4175cfe6cc8e4d1a9a291f54529b32e6a4d20ff
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the lead-authorized N25 infinity route

## Result and dependency status

Candidate: comms/candidates/N25F_InfinityCenterDistinctness.lean.
It proves the exact remaining inequality xInfinityPrime ≠ yzInfinityPrime
and combines it with the two Z inequalities into infinityCenters_distinct.
It also supplies exists_equiv_of_same_center, the generic coefficient-
compatible local equivalence used in the argument. Three public declarations.

The file imports the shared named-Algebra module from b4175cfe and enables
all six definitions locally. It depends on that commit's parameter-order
candidate for the two Z inequalities. At preparation, the last verified
lead receipt remains r28; acceptance of b4175cfe is not presumed. Integrate
its prerequisites first. No accepted source is changed in this packet.

## Actual mathematical contradiction

If the X and YZ centers were equal, their proved normalization-localization
equivalences would yield a common-field-compatible X/YZ local equivalence.
Compatibility is proved by localization ring-hom extensionality from the
actual normalization inclusion, not assumed as an opaque equivalence.

Z/Y is an actual unit in the YZ ring. Carry it back to X. Its common-field
image is qz/qy, while Y/X and Z/X map to qy/qx and qz/qx. The exact field
identity

    (qy/qx) * (qz/qy) = qz/qx

uses the already proved qy ≠ 0. Injectivity of the actual X-field map gives
(Y/X) * transported_unit = Z/X inside the actual X-local ring. Multiplying
by a unit preserves Ring.ord, contradicting the established orders 1 and 2.
Thus X and YZ have different centers. No center distinctness, valuation
comparison, local isomorphism, or product formula is an added premise.

## Validation ledger

PASS: generic equal-center local equivalence, the unit-ratio/order
contradiction, and the exact fraction identity above. generic-03 exits 0
in 5.699 seconds wrapper elapsed, with 2,473,728 KiB peak child RSS and no
warnings. The local equivalence audits [propext, Quot.sound]; the private
unit-ratio proof audits [propext, Classical.choice, Quot.sound]. No sorryAx.
The two helper proof bodies in the candidate match the checked source.

NOT RUN locally: all three actual production declarations with named
X/YZ coordinates and full FLT imports. The bounded local setup lacks the
compiled production closure; the attached actual audit file is for the
lead's gate. The generic and field-identity checks are not labeled actual
production checks. Source uses the requested exported Algebra definitions
rather than relying on local instance leakage.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler seconds,
synthesis budget 200,000. No broad build.

## Next owned step

Next are the actual residue degrees and the finite fiber sum over (T),
using the now-constructed centers, localizations, orders 1,1,2 and the
separate distinctness proof. Completeness of the three primes over (T)
and the arbitrary-function norm/product formula remain open.
The last fresh Mazur root audit remains no sorryAx and exactly the same
three custom axioms; this candidate does not close N25 or Mazur.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-DISTINCTNESS-r1-manifest.json
