# r28 sync, shared Algebra data, and reciprocal-prime data

TASK_ID: FLT-N25-INFINITY-LOCALIZATIONS
REVISION: 28
TYPE: ACK_AND_RESULT
STATUS: LOCALIZATIONS-ACCEPTED-WITH-INSTANCE-FIX; SHARED-ACTIONS-AND-PRIME-DATA-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: e0f728a3c0149389d6dcc9f0053dc6991ccb687b
DISPATCH_COMMIT: e74f1682406b1c6d7202ba2fdb0fff7f2c33a1a3
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the infinity route

## R28 synchronization and requested scope repair

N25F_CenterLocalization and N25F_OrderRingEquiv are independently verified
byte-equal to accepted source. N25F_InfinityLocalizations required exactly
the eight lines in the lead receipt: opening the base namespaces, selecting
the reciprocal polynomial action, and redeclaring its three boundary
actions. I verified that precise addition and no other change, and copy
the accepted source back to our candidate in this packet. The lead reports
8,692 successful jobs and all fifteen public audits standard-three.

The second scope miss is real. Installing the normalization-to-boundary
action inside the coefficient proofs was insufficient: projections from
the existing polynomial-AlgHom also need the polynomial boundary action
available when the surrounding declaration is elaborated.

The requested single source module is supplied:
comms/candidates/N25F_InfinityBoundaryAlgebras.lean.
It exports six named reducible Algebra definitions, three for the polynomial
base and three for the normalization. They are not global instances.
Every new downstream production file in this packet imports this module
and explicitly enables its six definitions locally, together with the
existing infinityPolynomialAlgebra. No accepted source proof is refactored.

PASS: a two-module scope regression. The exporter emits an olean; a fresh
importing file proves that the polynomial action is initially absent,
then enables the exported definitions, elaborates normalizationMap.toRingHom,
and proves coefficient compatibility. Export/import take 2.769/2.455 seconds;
the theorem's audit is standard-three. This is a concrete dictionary-scope
regression over polynomial rings and ZMod 2, not a production FLT check.

UNAVAILABLE LOCALLY: the requested full production-import build. This
bounded sandbox has pinned Mathlib and emitted selective fixtures, not the
lead's compiled FLT dependency closure. I have not substituted concatenated
files or called the family tests production builds. The full actual modules
still require the lead's gate. The named-definition module and independent
scope regression address the observed failure within the available setup.

## Exact contraction to the reciprocal-coordinate prime

Candidate: comms/candidates/N25F_InfinityPrimeContraction.lean.
It defines infinityBasePrime = Ideal.span {Polynomial.X}, proves it maximal,
and proves the exact contraction equality and LiesOver instance for each
of the three actual center primes. There are nine public declarations.

The generic proof is short: the contracted prime contains X, while (X) is
maximal in the polynomial ring over a field. No contraction equality is
assumed. Each actual application supplies the accepted parameter-membership
proof. The generic theorem and an explicit LiesOver construction check pass
in 11.894 seconds with a standard-three axiom audit.

## Actual parameter orders and two distinctness statements

Candidate: comms/candidates/N25F_InfinityParameterOrders.lean.
It proves the three actual images of infinityParameter in the boundary
rings, transports their orders through the accepted localization equivalences,
and obtains orders 1,1,2 on the normalization localizations. Consequently:

    xInfinityPrime ≠ zInfinityPrime
    yzInfinityPrime ≠ zInfinityPrime

There are eight public declarations. The transport and equality-of-prime
helper proofs are checked together in 4.122 seconds; both audits are
standard-three. Source uses the shared named Algebra definitions, including
the polynomial action needed to elaborate each AlgHom projection.

NOT RUN locally: the six named production Algebra definitions and the
seventeen named contraction/order declarations against full FLT imports.
All three candidates are source-reviewed; ActualInfinityPrimeDataCheck.lean
lists all twenty-three public declarations for the lead. These results do
not yet assert xInfinityPrime ≠ yzInfinityPrime or fiber completeness.

## Next proof and bounds

I continue with X versus YZ using the actual unit Z/Y at YZ and the distinct
X-local orders of Y/X and Z/X. Equal centers would force a common-field
compatible local equivalence, carrying that unit back to X and contradicting
orders 1 and 2. Its generic local-equivalence and unit-ratio proofs already
pass; the actual coordinate specialization is separate ongoing work.
Residue degrees, completeness above (T), and the general norm/product
formula remain afterward. The fresh Mazur root frontier stays at no sorryAx
and exactly the same three custom axioms.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Checks use one shared
gate per invocation, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler
seconds and synthesis budget 200,000. Elapsed times may include waiting.
No broad build or new premise in the production target was introduced.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-LOCALIZATIONS-r28-manifest.json
