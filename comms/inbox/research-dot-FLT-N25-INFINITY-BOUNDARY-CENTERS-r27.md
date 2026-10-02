# r27 sync and actual center-localization equivalences

TASK_ID: FLT-N25-INFINITY-BOUNDARY-CENTERS
REVISION: 27
TYPE: ACK_AND_RESULT
STATUS: CENTERS-ACCEPTED-WITH-SCOPED-INSTANCE-FIX; LOCALIZATION-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: eb3f5d1c241368c4393d55a83e5c075963a499f0
DISPATCH_COMMIT: e35b83660ca8b8560e826e7c5905afd79c3ceb03
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the infinity route

## R27 correction synchronized

The delivered center module required the three polynomial-to-boundary
Algebra instances to be redeclared in its own module. R27 adds exactly
six lines, leaving statements and proof bodies unchanged. I independently
verified this exact delta at the full production source hash. The corrected
center source replaces our candidate copy in this packet. The lead reports
8,689 successful build jobs and all seventeen public audits standard-three.
Original-to-accepted byte equality is not claimed.

The earlier local evidence was an abstract boundary-family check importing
an emitted actual-normalization fixture. It did not compile the named
production center module and did not exercise those three coefficient
instance bindings. That limitation was listed in the delivery ledger and
is now resolved by the lead's production check. This packet retains the
same distinction. Its checks are separate modules importing the checked
normalization and helper modules; full production imports remain the
lead-owned gate.

The new localization candidate explicitly reinstalls its N-to-boundary
Algebra action inside each coefficient-compatibility proof. This was also
caught and repaired in the separate actual-carrier family microcheck.
No accepted field, order, or normalization proof is changed.

## Constructed localization comparison

Candidate: comms/candidates/N25F_CenterLocalization.lean
Namespace: MazurProof.N25F_CenterLocalization

Given a map f : A →+* R into a local ring and the exact identity
p = (maximalIdeal R).comap f, this module constructs

    centerLocalizationMap : Localization.AtPrime p →+* R

and proves its coefficient restriction and IsLocalHom property. Denominators
outside the center map to units. Localness is proved from the numerator of
a localized fraction and the exact center identity; it is not a premise.

If A is Dedekind, p is nonzero, and R embeds compatibly and injectively into
A's fixed fraction field K, the module constructs the fraction-field action
on Localization.AtPrime p and its fraction-ring structure, obtains its DVR
structure, and applies accepted valuation rigidity. It proves the map
bijective and constructs centerLocalizationEquiv over A. There are five
public declarations and no assumed local isomorphism.

PASS: the entire generic proof, with only its accepted FLT rigidity import
renamed to the byte-identical emitted local module. comparison-02 emits
its olean, exit 0, 14.710 seconds wrapper elapsed, 2,538,512 KiB peak child
RSS. All five public audits are standard-three, with no sorryAx or warnings.

## Actual X/YZ/Z equivalences

Candidate: comms/candidates/N25F_InfinityLocalizations.lean
Namespace: MazurProof.N25F_InfinityLocalizations

For each actual boundary B = X, YZ, Z:

    bInfinityLocalizationEquiv :
      letI : Algebra InfinityNormalization BLocalRing :=
        infinityNormalizationToB.toRingHom.toAlgebra
      Localization.AtPrime bInfinityPrime ≃ₐ[InfinityNormalization] BLocalRing

These use the fixed actual center, nonzeroness, factor map and injective
common-field embedding. Coefficient compatibility and its common-field
image are proved too, giving nine public declarations. No new hypothesis
appears in the production candidate.

PASS: the three comparison proof patterns specialized to the actual
normalization carrier, in a separate boundary-family module importing
emitted checks. family-02 exit 0, 60.531 seconds wrapper elapsed,
2,828,188 KiB peak child RSS, all three audits standard-three, no sorryAx
or warnings. The source has the already accepted normalization structures
and actual boundary facts explicit. Its first attempt was rejected for a
missing coefficient-action instance; the same fix is in production.

NOT RUN locally: the full new actual X/YZ/Z module and its named binding
closure. ActualInfinityLocalizationsCheck.lean lists the fifteen new public
declarations in this packet for the lead's full import and axiom gate.

## Order transport needed next

Candidate: comms/candidates/N25F_OrderRingEquiv.lean
Namespace: MazurProof.N25F_OrderRingEquiv

    ord_map_ringEquiv (e : R ≃+* S) (a : R) :
      Ring.ord S (e a) = Ring.ord R a

This is proved by the induced principal-ideal quotient equivalence and
surjective change of scalars for module length. The exact Mathlib-only
production source and its one-declaration standard-three audit pass.
It will transport the actual parameter orders 1,1,2 through the established
local identifications; no new valuation or order invariant is assumed.

## Bounds and remaining work

Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every invocation uses one
shared gate, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler seconds,
and synthesis budget 200,000. Wrapper duration includes gate waiting, so
family-02's 60.531 seconds does not enlarge the active limit. No broad build.

I continue with the reciprocal-prime contraction, order transport and
center distinctness, then residue degrees and fiber completeness. The
localization comparison itself does not assert that these three centers
exhaust the primes above (T). The arbitrary-function norm sum and general
projective product formula remain open. The latest fresh Mazur root audit
still has no sorryAx and the same three custom axioms: no_prime_order_ge_23,
N25 obstruction exclusion, N49 raw-obstruction exclusion.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-BOUNDARY-CENTERS-r27-manifest.json
