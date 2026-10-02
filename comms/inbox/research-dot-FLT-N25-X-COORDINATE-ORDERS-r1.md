# Actual X-boundary coordinate orders

TASK_ID: FLT-N25-X-COORDINATE-ORDERS
REVISION: 1
TYPE: RESULT
STATUS: SOURCE-CANDIDATE-AND-SELECTIVE-CHECK-PASS
PARENT_SCOPE: FLT-N25-AFFINE-DEGREE, continuing r14's boundary-order task
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 11c72e9feb3d47fb022469a40198ec85fdec3097
DISPATCH_COMMIT: c429fb036a24ff9059775c742fb745abdcd36951
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none

## New exact result

Candidate: comms/candidates/N25F_XCoordinateOrders.lean
Namespace: MazurProof.N25F_XCoordinateOrders

    def xYGerm : XLocalRing := algebraMap XChartRing XLocalRing xY
    def xZGerm : XLocalRing := algebraMap XChartRing XLocalRing xZ
    theorem xYGerm_ord_eq_one : Ring.ord XLocalRing xYGerm = 1
    theorem xZGerm_ord_eq_two : Ring.ord XLocalRing xZGerm = 2

There are no additional production premises. The rings, point prime,
coordinates and W/X order-three theorem are the existing source objects.
The accepted X-local DVR structure is used unchanged.

## Genuine local calculation

In the actual X chart, the cubic says
Y/X * Z/X = -(W/X)*(1+Y/X+Z/X+(Y/X)(Z/X)+(Z/X)^2+(Z/X)(W/X)).
The parenthesized coefficient evaluates to one at [1:0:0:0], hence its germ
is a unit. The two coordinate orders therefore sum to three. Both germs
are nonunits because their actual point values are zero.

The quadric says (Z/X)*(1+Y/X+W/X) = -(W/X+(Y/X)^2).
Its coefficient is likewise a unit. The DVR order inequality gives
min(3,2*ord(Y/X)) <= ord(Z/X), which forces the orders to be one and two.
The proof uses both actual defining equations. It is not an assumption
about valuations or an arbitrary local model.

## Exact validation scope

PASS: generic DVR argument at the fixed Mathlib pin, 5.203s,
2,908,960KiB peak child RSS, standard-three audit.
PASS: selective source harness with actual X-chart quotient, actual
source xChartEval/xPrime and actual local ring, 15.533s,
2,944,528KiB peak child RSS; both new order theorems audit to exactly
propext/Classical.choice/Quot.sound, no sorryAx.
The harness keeps only the previously accepted W Dedekind structure and
the existing xWGerm_ord_eq_three theorem as explicit parameters. The actual
point evaluator is copied from source, not replaced by an arbitrary point.
Its final elaborated signatures are in actual-02.log. That log also records
benign unused-section-variable warnings in the fixture.

NOT RUN locally: parameter-free production module with full FLT imports;
lead validation file ActualXCoordinateOrdersCheck.lean audits all four
public declarations. No full build was launched here.

The defining chart source was independently fetched at immutable
56bed095c61c28fda99ad99e8bf0cb74542058ad (r14 adds only the independent
YZ DVR candidate). Its Git blob is recorded in source-provenance.json.
The generic helper, production source, fixture and exact receipts are
attached with hashes and the reproducible generation/runner scripts.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per bounded
invocation, one CPU/thread,3072MiB Lean cap,60s compiler limit;
synthInstance.maxHeartbeats200000 retained.

## Continuation

These orders will give the common affine function qz pole order one at X,
using the accepted coordinate-rigid fraction map; that signed-field lemma
is the next small step. The parallel YZ signed orders are separately owned
within the same N25 lane. The projective product formula is still open.
The last fresh Mazur root closure remains no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion, and the
N49 raw obstruction exclusion. No root change is inferred from this module.

Manifest: comms/inbox/research-dot-FLT-N25-X-COORDINATE-ORDERS-r1-manifest.json
