# r26 ACK and nonzero boundary centers

TASK_ID: FLT-N25-INFINITY-BOUNDARY-MAPS
REVISION: 26
TYPE: ACK_AND_RESULT
STATUS: THREE-BOUNDARY-MAPS-ACCEPTED; ACTUAL-CENTER-PRIMES-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 0045a84739791e85efbb83a2c3c9336a99016dde
DISPATCH_COMMIT: 2de23c92266d9dced2dfbe1e87fafacd5457f057
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the same infinity route

## R26 ACK

The actual X/YZ/Z factor maps and local valuation rigidity were accepted
byte-equal from26800c740c155ec60ebc307452f8c1ca33dc523d. I independently
resolved the full source hash and compared both files exactly. The lead
reports8689 successful jobs and all ten public audits standard-three.

## New actual definitions and proofs

Candidate: comms/candidates/N25F_InfinityBoundaryCenters.lean
Namespace: MazurProof.N25F_InfinityBoundaryCenters

infinityParameter is algebraMap BasePolynomial InfinityNormalization X.
Its nonzeroness is proved using the accepted reciprocal polynomial map's
injectivity into the same curve field.

For b = x,yz,z, bInfinityPrime is the exact comap of the maximal ideal of
BLocalRing under infinityNormalizationToB. The module proves:

    bInfinityPrime.IsPrime
    infinityParameter ∈ bInfinityPrime
    bInfinityPrime ≠ ⊥
    bInfinityPrime.IsMaximal

There are seventeen public declarations in total: the parameter and
nonzeroness, plus each center definition and four properties. Parameter
membership is obtained from the actual images xInverseZGerm,
yzInverseZGerm,zWGerm and their already-proved orders1,1,2. A unit has
order zero, so these actual images lie in the respective maximal ideals.
Thus each center contains the same nonzero normalization element.
The maximality proof uses dimension at most one; it does not assume that
the centers are distinct or exhaust the fiber.

No new hypothesis is added to production. The exact existing local rings,
field embeddings, factor maps, and coordinate-order theorems are retained.

## Validation

PASS: actual-normalization carrier and boundary-center family check,
family-04 exit0,25.973 seconds wrapper elapsed,2,629,352KiB peak child
RSS. Seven family declarations audit exactly propext,Classical.choice,
Quot.sound, with no sorryAx or warnings. The check makes the existing
W domain/torsionfree facts and the boundary map's nonzero parameter order
explicit; production supplies the three fixed maps and their orders.
Earlier checks also had clean axioms but fixture-only unused-variable
warnings; the final source removes those unnecessary parameters.

NOT RUN locally: the complete new FLT module with all seventeen named
production bindings and its aggregate audit. The attached
ActualInfinityBoundaryCentersCheck.lean lists every public declaration
for the lead. Source-specific family feedback is not a claim that the
actual named module has already passed its production gate.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation,one CPU/thread,3072MiB Lean cap,60 active seconds and
synthInstance.maxHeartbeats200000. Elapsed times may include gate waiting.
No broad project build or accepted-source rewrite was run here.

## Next owned proof

I continue with the actual localization at each constructed center. The
next map is the universal localization lift into the boundary ring; its
localness must be proved from the exact center identity. Then the accepted
valuation-rigidity theorem identifies it with the boundary ring. Current
parameter membership does not yet assert the full contraction equality
with(T), center distinctness, completeness, or the general norm/product
formula. Those remain separate proof steps.

The last fresh Mazur root audit remains no sorryAx and exactly the same
three custom axioms: no_prime_order_ge_23, N25 obstruction exclusion and
N49 raw-obstruction exclusion. N25 and Mazur are not claimed complete.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-BOUNDARY-MAPS-r26-manifest.json
