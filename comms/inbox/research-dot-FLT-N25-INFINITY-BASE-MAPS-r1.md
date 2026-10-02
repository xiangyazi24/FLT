# Concrete reciprocal-base maps into the three boundary rings

TASK_ID: FLT-N25-INFINITY-BASE-MAPS
REVISION: 1
TYPE: RESULT
STATUS: SOURCE-CANDIDATE; GENERIC-AND-ACTUAL-FIELD-FEEDBACK-PASS
PARENT_SCOPE: N25 actual infinity comparison / arbitrary-function product formula
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 8a8daa4e41c0d852b4b4a8a34aaed9c530012ea3
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none
DEPENDENCY_CANDIDATE: N25F_XInfinityGerm at 27a8aaedcc90d31b6a974fe60d54aa2225f6249a; full-import acceptance not yet observed

## New actual maps

Candidate: comms/candidates/N25F_InfinityBaseMaps.lean
Namespace: MazurProof.N25F_InfinityBaseMaps

The source constructs infinityBaseToField : Polynomial (ZMod 2) →ₐ[ZMod 2] K
by sending its variable to1/qz, for the same K=FractionRing W. It proves
this map injective, using the accepted exact coefficient-map identity and
transcendence preserved by inversion. No transcendence or injectivity
premise is added to production.

It constructs explicit F2-algebra maps from the same polynomial base into
XLocalRing, YZLocalRing and ZLocalRing:
- X: evaluate at the constructed xInverseZGerm
- YZ: evaluate at yzWGerm * inverse(yzZUnit)
- Z: evaluate at the existing zWGerm

Their compositions with the three accepted coordinate-rigid field maps
are each exactly infinityBaseToField. All three local base maps are
therefore injective. The new YZ reciprocal germ maps to1/qz, is nonzero,
and has actual Ring.ord one. The Z germ already has order two, and the
preceding X candidate proves order one. No competing global Algebra
instance is installed or existing qz-base coefficient action changed.

These are actual local/common-field maps, not an assumed local-ring
identification or formal interface asserting the desired product formula.

## Validation ledger

PASS: generic unit-inverse image calculation, unit-order preservation,
polynomial evaluation compatibility with an algebra homomorphism, and
injectivity under inversion of a transcendental field element.
generic-01:20.348s wrapper time,2,525,928KiB peak child RSS; all four audits
exactly propext/Classical.choice/Quot.sound, no sorryAx.

PASS: source-specific actual W-common-field reciprocal polynomial map and
its injectivity, field-01:15.504s,2,474,156KiB peak child RSS; both audits
exactly the standard three axioms, no sorryAx. This check imports the
actual W/Z curve/field definitions and uses the exact accepted r19
coefficient-map bridge. Only the already-established W structural
instances are explicit fixture parameters. One benign unused-section-
variable warning concerns that copied bridge.

NOT RUN locally: the entire15-declaration production module, the actual
named YZ unit binding and the combined three-boundary imports. The supplied
ActualInfinityBaseMapsCheck.lean audits all15 public declarations. Their
source-specific specialization was reviewed; the lead owns full-import
elaboration and acceptance. No new production hypotheses were added.

All checks use Lean4.31.0-rc2 at5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every invocation uses one
shared gate, oneCPU/thread,3072MiB Lean cap,60s compiler limit and synthesis
budget200000. Wrapper times may include lock waiting. No broad build.

## Next mathematical obligation

The reciprocal base can now be placed in the actual three boundary rings.
Next is the finite integral normalization over that base, its compatibility
with these localizations, and the complete relative-norm comparison at the
infinity prime. The common-field extension still has to be presented over
this inverted base; finiteness, identification and completeness of the
three primes above infinity are not assumed. The general product formula
remains open, despite the accepted base-polynomial subcase.

The last fresh Mazur root audit remains no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion and the
N49 raw-obstruction exclusion. No root-closure change is inferred here.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-BASE-MAPS-r1-manifest.json
