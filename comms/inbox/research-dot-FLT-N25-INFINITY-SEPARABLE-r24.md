# r24 ACK and actual reciprocal integral normalization

TASK_ID: FLT-N25-INFINITY-SEPARABLE
REVISION: 24
TYPE: ACK_AND_RESULT
STATUS: SEPARABILITY-ACCEPTED; FINITE-DEDEKIND-RANK-FOUR-NORMALIZATION-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 078432313380bb9603096339caf21fb3114ce325
DISPATCH_COMMIT: 8fa22f850e5ba4417783e8447fa20ca442f9e8d4
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the actual infinity normalization proof

## Acceptance ACK

R24 integrates N25F_InfinitySeparable byte-equal from
8188f9ae3036230b2ba685f8ea896895e71c9195. I resolved the full source hash
and independently compared the accepted bytes. The lead reports an
8685-job successful build and all three public declarations with exactly
propext, Classical.choice, Quot.sound. This binding gate is closed.

## New actual construction

Candidate comms/candidates/N25F_InfinityNormalization.lean defines
InfinityNormalization as the actual integralClosure BasePolynomial CurveField
under infinityBaseToField.toRingHom.toAlgebra. The reciprocal polynomial
and rational actions are explicit reducible data with local-only instance
registration; the old global affine action is not replaced.

Production proves, without new premises:

    infinityNormalization_finite :
      Module.Finite BasePolynomial InfinityNormalization
    infinityNormalization_isFractionRing :
      IsFractionRing InfinityNormalization CurveField
    infinityNormalization_isDedekindDomain :
      IsDedekindDomain InfinityNormalization
    infinityNormalization_finrank_eq_four :
      Module.finrank BasePolynomial InfinityNormalization = 4

The tower is proved from the accepted explicit coefficient restriction.
Finite degree four and separability come from the accepted r23/r24
actual reciprocal-field theorems. The standard integral-closure theorems
then give finiteness, the identical fraction field, Dedekind structure,
and the rank equality. Module and SMul actions are aligned explicitly
with the reciprocal Algebras to avoid the existing localization-action
diamond. The carrier is constructed, not assumed.

## Checked generic boundary factor

Candidate comms/candidates/N25F_IntegralBoundaryFactor.lean constructs

    integralClosureToRing : integralClosure A K →ₐ[A] R

for CommRing A, CommRing R, Field K, the three compatible Algebra actions,
IsScalarTower A R K, IsFractionRing R K, and IsIntegrallyClosed R.
It uses integrality transitivity and integral closedness to construct
preimages. Six public declarations give existence, the homomorphism,
pointwise and exact AlgHom composite identities, injectivity and uniqueness.
No factor map, local isomorphism, product formula, finiteness or
separability hypothesis is presumed by this generic helper.

## Validation ledger

PASS: exact Mathlib-only production boundary-factor source, check-02.log;
its byte-copy six-declaration audit is clean, all standard-three.

PASS: actual-curve normalization fixture actual-05, exit0,55.116 seconds
wrapper elapsed,2,318,216KiB peak child RSS. All seven public declaration
audits are exactly standard-three, no sorryAx or warnings. The actual
carrier and four construction proofs are checked. The fixture exposes
already-accepted W structural facts, W rank4, and r24 reciprocal-action
separability as parameters. The production candidate instead references
the accepted named finite-degree/separability proofs and has no additional
premises. Default printed class names conceal Algebra parameters;
InfinityNormalizationCheck.lean pins the reciprocal action explicitly.

Development attempts actual-01 through actual-04 were rejected. In
particular, exit0 in attempts02-04 was insufficient: their axiom audit
exposed sorryAx in a misbound fixture-only separability declaration.
The final fixture directly uses the accepted reciprocal separability
fact; no accepted production source was changed to hide that failure.
Final source hash and clean audit are attached. These rejected runs are
not proof evidence.

NOT RUN locally: full new FLT normalization module with actual named
source bindings, aggregate integration and final production axiom audit.
ActualInfinityNormalizationCheck.lean lists all thirteen public declarations
in these two candidates for the lead.

Pins: Lean4.31.0-rc2,5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every check uses one
shared gate acquisition, one CPU/thread,3072MiB Lean cap,60 seconds active
compiler limit,synthInstance.maxHeartbeats200000. Wrapper duration can
include lock waiting. No broad project build was run here.

## Next owned result and remaining mathematical boundary

I retain ownership of the three actual normalization-to-boundary-ring
maps, specializing this factor through the established X,YZ,Z embeddings
and their accepted reciprocal-base compatibility. After these maps, the
remaining step is to identify the corresponding localizations and prove
that all primes above infinity have been accounted for. Only then can
the relative-norm/valuation identity yield degree zero for arbitrary
functions. The already accepted base-polynomial degree-zero theorem
remains a genuine subcase, not the general projective product formula.

The last fresh Mazur root audit remains no sorryAx and exactly three
custom axioms: no_prime_order_ge_23, the N25 obstruction exclusion, and
the N49 raw-obstruction exclusion. No N25 or Mazur completion is claimed.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-SEPARABLE-r24-manifest.json
