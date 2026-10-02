# r16/r17 ACK and polynomial boundary/norm results

TASK_ID: FLT-N25-BOUNDARY-ORDERS
REVISION: 17
TYPE: ACK_AND_RESULT
STATUS: SIGNED-ORDERS-ACCEPTED; POLYNOMIAL-AND-NORM-CANDIDATES-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 50263205b429bcafde5abb0935ae3011c0e845ae
DISPATCH_COMMIT: cc4fb8a42f56fad31510c05fb6368ad6a738f972
EARLIER_RECEIPT: r16 at 9f82015c49488253eb5943cc2634cdd18af6c620
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the same bounded N25 proof lane

## Accepted source synchronized

R16 accepts XCoordinateOrders byte-equal at
8d67705d40adc07ab5274cd2e5c1f252f2ba1291: 8653-job build and four public
standard-three audits. R17 accepts XBoundaryZOrder and YZBoundaryOrder
byte-equal at the full source pin above: 8669-job build and ten public
standard-three audits. The synchronized field map includes the r15
proof repairs. I independently fetched and checked all these accepted
bytes. The receipt paths are comms/outbox/receipt_r16.md and receipt_r17.md;
their explicit source/task identities resolve the nonstandard filenames.

## Two new parameter-free production candidates

1. comms/candidates/N25F_PolynomialBoundaryOrders.lean

For every nonzero p : Polynomial (ZMod 2), the three actual local fraction
orders of p evaluated at the actual common-field coordinate qz=Z/W are:

    xLocalFractionOrder (p.aeval (algebraMap W K qz))
      = WithZero.exp (-(1 * p.natDegree : ℤ))
    yzLocalFractionOrder (p.aeval (algebraMap W K qz))
      = WithZero.exp (-(1 * p.natDegree : ℤ))
    zLocalFractionOrder (p.aeval (algebraMap W K qz))
      = WithZero.exp (-(2 * p.natDegree : ℤ))

The namespace is MazurProof.N25F_PolynomialBoundaryOrders and theorem
names are xLocalFractionOrder_aeval_qz, yzLocalFractionOrder_aeval_qz,
and zLocalFractionOrder_aeval_qz. No extra local-ring, map, valuation or
point hypotheses are added in production.

The proof identifies Ring.ordFrac with the inverse of the actual DVR
valuation, proves that valuation trivial on coefficient-field units, and
uses Mathlib's leading-term valuation theorem at a genuine pole. It then
specializes to the accepted actual boundary fields and orders1/1/2.

2. comms/candidates/N25F_WChartBaseNorm.lean

In namespace MazurProof.N25F_NonBoundaryPrincipalDivisor:

    wChart_finrank_polynomial_eq_four :
      Module.finrank (Polynomial (ZMod 2)) W = 4

    wChart_norm_algebraMap_eq_pow_four (p : Polynomial (ZMod 2)) :
      Algebra.norm (Polynomial (ZMod 2))
        (algebraMap (Polynomial (ZMod 2)) W p) = p ^ 4

    wChart_quotient_finrank_base_polynomial (p) (hp : p ≠ 0) :
      Module.finrank (ZMod 2)
        (W ⧸ Ideal.span ({algebraMap (Polynomial (ZMod 2)) W p} : Set W))
        = 4 * p.natDegree

These use the source's existing plane function-field degree-four theorem,
its actual fraction-ring identification with W, and the accepted actual-W
norm/dimension theorem. Rank four is proved, not added as a production
premise. The generic feedback makes that already-existing degree theorem
explicit. The existing coefficient map sends X to qz; the final evaluation
bridge and combined degree-zero subcase are the next small step.

## Checks actually run

PASS: generic polynomial-at-pole lemma and each of its three curve
specializations. X selective actual-point check38.374s, YZ point-family
check62.851s, Z point-family check34.093s (wrapper elapsed times include
shared-lock waiting; individual Lean limit remains60s). All three new
specialization audits are exactly propext/Classical.choice/Quot.sound,
without sorryAx. Peak child RSS remains below2,950,000KiB. The fixtures
retain the established W structures and existing point/order facts as
explicit parameters. X uses the actual source evaluator; YZ and Z use
transparent point families. No pole order of p(qz) is assumed.

PASS: the three generic base-rank, norm and quotient-dimension lemmas,
48.631s including lock waiting,2,432,300KiB peak child RSS, all three
standard-three audits. Explicit generic structural assumptions correspond
to the accepted actual W/plane normalization structures. The parameter-
free source binding to PlaneFunctionField was source-reviewed, not locally
compiled.

NOT RUN locally: either new production module with the complete FLT import
closure and all actual named bindings. ActualPolynomialNormCheck.lean
supplies all six production audits for the lead. Historical fixture proofs
are preserved as checked; the YZ field fixture retains the pre-r15 proof
variant with the same statements, as previously disclosed.

The attached logs retain benign unused-section-variable warnings. Failed
early fixture drafts are not labeled PASS. Detailed hashes and exact final
receipts are in validation.json and the delivery manifest.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every compiler call used
one shared gate, one CPU/thread,3072MiB Lean cap,60s limit and synthesis
budget200000. A single official cached Mathlib module,
RingTheory.Valuation.IsTrivialOn, was fetched at the unchanged pin;1 new
module,1575 existing modules reused, no build or version change.

## Continuation and exact remaining scope

Next: prove that the existing coefficient map is evaluation at qz, then
assemble these affine and boundary contributions into degree zero for
nonzero base polynomials (and their ratios). This is a genuine subcase of
the intended product formula, not a replacement or weakening of its general
arbitrary-function target. The latter still needs a norm-at-infinity /
complete-boundary comparison for every function in FractionRing W.

The last fresh Mazur root closure remains no sorryAx and exactly three
custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. Neither N25 nor the
general projective product formula is claimed complete.

Manifest: comms/inbox/research-dot-FLT-N25-BOUNDARY-ORDERS-r17-manifest.json
