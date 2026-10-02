# r20/r21 ACK and checked rational-base inversion

TASK_ID: FLT-N25-INFINITY-BASE-MAPS
REVISION: 21
TYPE: ACK_AND_RESULT
STATUS: BOUNDARY-BASE-MAPS-ACCEPTED; EXACT-INVERSION-MODULE-COMPILED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 723fc37242042afc5985caa084d626b49e304d59
DISPATCH_COMMIT: 936cbf66990bc170b8f38520798eb2a0d9e6f077
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continued inverted-base comparison

## Acceptance synchronized

R20 accepts the actual X reciprocal germ byte-equal at
ddf67bf931362bd4dfbc1d3fbf1d9ac1a1402c2a: 8658-job build and six
standard-three public audits. R21 accepts the actual infinity-base maps
byte-equal at the full source pin above: 8682-job build and fifteen
standard-three public audits. I independently checked both accepted
modules and the retained r19 qualified-W source. Those production gates
are now closed; they do not assert the general product formula.

## Concrete new field automorphism

Candidate: comms/candidates/N25F_RationalBaseInversion.lean
Namespace: MazurProof.N25F_RationalBaseInversion

The module uses exactly:

    BasePolynomial := Polynomial (ZMod 2)
    BaseField := FractionRing BasePolynomial
    baseVariable := algebraMap BasePolynomial BaseField Polynomial.X

It constructs baseInversion : BaseField ≃ₐ[ZMod 2] BaseField and proves
baseInversion(baseVariable)=baseVariable^-1 and that baseInversion is
involutive. The underlying homomorphism's restriction to polynomials is
proved to be evaluation at the inverse variable.

The construction extends an injective polynomial evaluation to its
fraction field. It proves injectivity via transcendence/inversion, then
proves the composite is the identity by localization and polynomial
extensionality. No automorphism, inverse-field identification or finite-
extension equivalence is assumed.

This is the concrete rational-base coordinate change needed to compare
the original qz and reciprocal-qz scalar actions on the same curve field.
The actual comparison and transfer of degree four remain the next proof;
they are not hidden hypotheses in this module.

## Exact local verification

PASS: the complete delivered Mathlib-only source bytes compiled under the
local module name N25F_RationalBaseInversion and emitted an olean.
production-01:26.182s wrapper elapsed,2,122,856KiB peak child RSS, exit0.
Source SHA256: da686b7db9b7cdf4129fcddabb1575cb9ff6f7ffe34a08ca94d37ebc35d5d9ce.

PASS: a separate import of that emitted module audited all nine public
declarations, including the two carrier aliases and baseVariable.
audit-01:9.520s wrapper elapsed, exit0; every audit is exactly
propext/Classical.choice/Quot.sound, no sorryAx. There are no fixture
parameters or uncompiled production proof bodies in this local result.
The source and local/olean hash receipts are attached.

NOT RUN here: integration under its FLT module path and the lead's aggregate
build/audit. ActualRationalBaseInversionCheck.lean lists all nine audits for
that gate. The local module imports only pinned Mathlib, not a substitute
FLT source closure. No broad FLT build was run.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One CPU/thread,3072MiB Lean
cap,60s compiler limit, one shared gate per command, synth budget200000.
Elapsed wrapper times may include shared-lock waiting. No version or
compiler-bound change.

## Next owned proof and unchanged endpoint scope

Next is proving that the common curve-field action of the reciprocal
rational base is the old action composed with this automorphism, then
transporting its finite degree-four basis. After that, construct and
identify the actual finite normalization at infinity with the three
boundary places, and prove the norm/valuation sum for arbitrary functions.
The accepted base-polynomial degree-zero theorem is a genuine subcase;
the arbitrary-function projective product formula remains open.

The last fresh Mazur root audit remains no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion and the
N49 raw-obstruction exclusion. No N25 or root completion is claimed.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-BASE-MAPS-r21-manifest.json
