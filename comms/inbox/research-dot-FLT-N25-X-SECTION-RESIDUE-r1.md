# Actual uniformizer-scaled X residue and its exact section kernel

TASK_ID: FLT-N25-X-SECTION-RESIDUE
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-LEADING-RESIDUE-AND-EXACT-KERNEL-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 9c8eb020ae3b1f50a2d8192516343c4f7aec844d
SUPERSEDES: none

N25F_DVRIntegralLift.lean proves two exact DVR facts: every zero or
nonnegative-order fraction has a unique actual local-ring preimage, and a
local element's residue is zero exactly when it is zero or has positive order.
Zero is handled separately because WithZero.log 0=0.

N25F_XSectionResidue.lean applies these facts to the actual X local ring and
its already constructed reciprocal-base uniformizer xInverseZGerm=W/Z.
For f in the genuine space L(D), it constructs the unique X-local germ of
(W/Z)^D(X)*f and proves its exact common-field image and additivity. Applying
the actual residue map and xLocalResidueRingEquivF2 gives an F2-linear map

    xLeadingResidue25Two D : fullRiemannRochSpace25Two D ->ₗ[ZMod 2] ZMod 2.

Its zero condition is exactly f in L(D-X), and its kernel is exactly that
submodule of L(D). This is an actual local-ring/residue producer; no abstract
linear-system map, chosen quotient functional or kernel premise is assumed.
There are eight public declarations in two production modules.

## Exact current local inputs

The current r34 sources were fetched again before delivery:
- N25F_XInfinityGerm.lean: blob 8f967ddf53ff1264f8e6c96953e7daee9d5664ea
- N25F_InfinityResidueFields.lean: blob 18c50ccdb25902a9dc513699195381689946700e
- N25F_XBoundaryOrder.lean: blob 506082d8ddbbe3b8347681b8bb43372a70cb4646

These include the actual germ's nonvanishing/order-one proofs, its image W/Z,
the residue equivalence and the fixed local-to-common-field fraction action.
The current XBoundaryOrder file retains the lead's per-declaration instance-
heartbeat option. No byte-equality claim is made against its earlier copy.

## Validation

PASS: lift-01, complete Mathlib-only production source plus its two audits.
Exit 0, 38.869 seconds wrapper elapsed, peak child RSS 2,909,792 KiB.
SHA-256: f590f27096d8dc526aec454cfa28810dd50ad1fc0b0756cf514a9ecabaeedfe6.
Both audits exactly [propext, Classical.choice, Quot.sound], no warnings/sorryAx.

PASS: residue-family-03, six audits, exit 0, 27.344 seconds, peak RSS
2,894,564 KiB. SHA-256:
3186310ec241ee2ee2fc27b25b862969ee4c9544cf41e3a79ceca8a7fe5508d0.
All six audit exactly [propext, Classical.choice, Quot.sound], no sorryAx.
One linter warning reports a redundant change tactic after replacing the
actual fixed fraction-order definition with the generic Ring.ordFrac expression.
That change is needed for the production binding; the warning is not a proof gap.
Portable generators reproduce both checked files exactly.

The composed family includes the genuine section carrier, actual-style DVR
order/residue calculation and the previous X-filtration proof. It exposes the
established X principal coefficient, local fraction action, residue equivalence
and actual uniformizer's nonzero/order-one facts as explicit data. Production
closes each by the exact current source names above.

FAIL: residue-family-01 had a missing field annotation in generic scaling and
an identity-ring-hom scalar simplification; residue-family-02 exposed a generic
definition rewrite and a definitional membership conversion. All rejected
sources and downstream sorryAx logs are isolated under failed/.

NOT RUN: the full named FLT imports and eight production audits. Their
integration and fresh aggregate acceptance remain with the lead. No new root
axiom closure or acceptance of pending dependencies is inferred.
Lean 4.31.0-rc2 compiler 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Shared gate per invocation,
one CPU/thread, 3072 MiB Lean cap, 60 active seconds. No broad build.

## Next owned substantive frontier

Audit and use the actual free rank-four W module over F2[z] and its three
boundary orders. The first concrete target is a uniform boundary-pole bound
for its fixed finite basis, independent of any divisor representative. This
starts a coarse lower-bound route using degree-weighted affine quotient costs
and all three boundary filtrations. Effectiveness of every high-degree class
and Picard finiteness are not yet proved. The sharp genus-four RR identity
and canonical/adjunction identification remain separate open geometry.

Manifest: comms/inbox/research-dot-FLT-N25-X-SECTION-RESIDUE-r1-manifest.json
