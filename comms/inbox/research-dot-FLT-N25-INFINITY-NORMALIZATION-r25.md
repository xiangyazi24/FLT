# r25 ACK, actual boundary factors, and local valuation rigidity

TASK_ID: FLT-N25-INFINITY-NORMALIZATION
REVISION: 25
TYPE: ACK_AND_RESULT
STATUS: NORMALIZATION-ACCEPTED; THREE-BOUNDARY-MAPS-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 40f7d090be57ff3439af1a3e7d257f3aabc47ca4
DISPATCH_COMMIT: 6f0ee137a8be3d4328d4f8c0a587ac75ec42db01
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the actual infinity route

## R25 ACK

The lead receipt at comms/outbox/lead-FLT-N25-receipt-r25.md accepts both
N25F_InfinityNormalization and N25F_IntegralBoundaryFactor byte-equal from
6258a2f09bba8272c67264cc012b675b81d67b4e. Both accepted files have been
independently read at the resolved full source hash and compared exactly.
The lead reports an 8687-job successful build and all thirteen public
audits standard-three. The actual finite, Dedekind, same-fraction-field,
rank-four reciprocal normalization is now integrated.

## Actual three boundary maps

Candidate: comms/candidates/N25F_InfinityBoundaryMaps.lean
Namespace: MazurProof.N25F_InfinityBoundaryMaps

For B = X, YZ, Z the candidate constructs the actual map

    infinityNormalizationToB :
      InfinityNormalization →ₐ[BasePolynomial] BLocalRing

and proves its composite with bLocalToFraction is the canonical
normalization inclusion, and that it is injective. These are nine public
declarations with the three actual fixed boundary rings and embeddings.
The scalar tower is proved pointwise from each accepted
bLocalToFraction_comp_infinityBase equality. Fraction-field structures
are the established named theorems; integral closedness comes from the
actual local DVR structures. No new hypothesis or assumed factor map
is added to production.

PASS: a boundary-ring-family microcheck using the actual common curve
field and actual reciprocal normalization carrier. family-03 exit0,
27.401 seconds wrapper elapsed,2,548,268KiB reported peak child RSS,
standard-three axiom audit, no sorryAx or warnings. It exposes only the
previously established boundary facts: a compatible reciprocal base map,
the fixed field embedding, and integral closedness/fraction-field status.
Those family parameters are not additional production premises.

NOT RUN locally: the complete new module with its nine named X/YZ/Z
bindings. The production candidate is source-reviewed; the full actual
specialization/audit is the lead's gate. The attached actual audit file
lists every declaration. This family check does not itself establish the
three named specializations or identify their localizations.

## A genuine next-step local rigidity lemma

Candidate: comms/candidates/N25F_LocalValuationRigidity.lean
Namespace: MazurProof.N25F_LocalValuationRigidity

    bijective_of_local_same_fraction_field
      (f : R →+* S) (g : S →+* K) [IsLocalHom f]
      (hg : Function.Injective g)
      (hcomp : g.comp f = algebraMap R K) : Function.Bijective f

The context is CommRing R, IsDomain R, ValuationRing R, CommRing S,
Field K, Algebra R K, IsFractionRing R K. No surjectivity or local
isomorphism is assumed. For s in S, the valuation property says g(s) or
its inverse lies in R. In the inverse case its image is a unit in S;
localness reflects that unit back to R, giving the desired inverse.
Injectivity follows from the fixed fraction-field inclusion.

PASS: exact Mathlib-only production source, production-01 exit0;
its appended one-declaration axiom audit is clean standard-three.
This is the rigidity step needed after constructing the center prime
and the localization map. It is not an assertion that those actual
centers, maps, or localness proofs have already been constructed.

## Evidence, bounds and next ownership

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation,one CPU/thread,3072MiB Lean cap,60 active compiler seconds,
synthesis budget200000. Wrapper elapsed times include lock waiting;
production-01's64.284 seconds therefore does not relax the60-second
compiler cap. Earlier family fixture instance-binding failures were
rejected; only family-03 is final proof evidence. No broad build here.

The unchanged normalization fixture was emitted in30.031 seconds and
remains clean; its source/olean hashes and receipt support the reused
actual carrier. Exact sources, logs and validation metadata are attached.

I continue to own the next actual center-prime/localization comparison.
After that, the three centers still need distinctness and completeness
above the reciprocal-coordinate prime (T), followed by the arbitrary-function
norm/valuation sum. The general product formula and N25 exclusion remain
open. The last fresh Mazur root audit remains no sorryAx and exactly the
same three custom axioms: no_prime_order_ge_23, N25 obstruction exclusion,
N49 raw-obstruction exclusion.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-NORMALIZATION-r25-manifest.json
