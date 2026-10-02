# r18 ACK and genuine principal-divisor base-polynomial subcase

TASK_ID: FLT-N25-POLYNOMIAL-BOUNDARY-ORDERS
REVISION: 18
TYPE: ACK_AND_RESULT
STATUS: POLYNOMIAL-NORM-ACCEPTANCE-VERIFIED; BASE-POLYNOMIAL-PRODUCT-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 0cfa6bc03768d157bd653173241a55c5a2f459f2
DISPATCH_COMMIT: e9d15549fdcc52a0c53a056e644402d54f43cc69
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; next bounded genuine result

## Acceptance synchronized

R18 accepts N25F_PolynomialBoundaryOrders and N25F_WChartBaseNorm
byte-equal from 5d2f42ad42a493c45c0323dce47a4fdcb82a7e4b:
8673-job build; all six public declarations have exactly the standard
three axioms. I resolved the full SHA and independently checked both
accepted files. Their actual production bindings/full imports are now
accepted, separately from their earlier local fixture receipts.

## New actual construction and exact theorem

Candidate: comms/candidates/N25F_ProjectivePrincipalDivisor.lean
Namespace: MazurProof.N25F_ProjectivePrincipalDivisor

The source constructs:

    projectivePrincipalDivisor :
      Additive ((FractionRing W)ˣ) →+ ProjectiveDivisor25Two

It uses the existing full divisor split, the three actual Ring.ordFrac-based
boundary homomorphisms, and the existing affine Dedekind principal divisor.
The map is defined for every nonzero function, has genuine finite support,
and adds no valuation, local-ring or degree-zero premise. Split and degree
formulas retain the exact X,YZ,Z and affine components.

The new nontrivial degree-zero theorem is the following explicit subcase:

    projectivePrincipalDivisor_degree_base_polynomial
      (p : Polynomial (ZMod 2)) (hp : p ≠ 0)
      (f : Additive ((FractionRing W)ˣ))
      (hf : (f.toMul : FractionRing W) =
        algebraMap W (FractionRing W)
          (algebraMap (Polynomial (ZMod 2)) W p)) :
      fullClosedPointGrading25Two.divisorDegree
        (projectivePrincipalDivisor f) = 0

The coefficient-map bridge is proved by polynomial ring-hom extensionality:
its variable is exactly qz. The accepted boundary contributions are
-deg(p),-deg(p),-2deg(p); the accepted affine quotient/degree contribution
is4deg(p), for the same function f. Their sum is zero. No arbitrary-function
product formula is supplied as an assumption or silently replaced by this
subcase.

## Validation ledger

PASS: polynomial-map evaluation bridge, bridge-02,51.245s total wrapper
time,2,034,740KiB peak child RSS, exactly the standard three axioms.
PASS: generic additive-equivalence principal-divisor assembly, split
identity and arithmetic cancellation, assembly-02,42.192s total wrapper
time,1,665,600KiB peak child RSS. All three audits use only propext and
Quot.sound. Neither final check contains sorryAx.

These generic feedback checks validate the new algebraic bridge and
assembly mechanics. They do not compile the actual six-declaration FLT
module or replace its source-specific proof dependencies by assumptions.
The production source supplies each component from the actual accepted
objects and source theorems. The source-specific combination was reviewed;
its full-import elaboration and six public audits are NOT RUN locally and
remain the lead's gate. ActualProjectivePrincipalCheck.lean is supplied.
Pinned source inputs were freshly fetched and Git-blob-verified.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One CPU/thread,3072MiB Lean
cap,60s active compiler limit, one shared gate per invocation; the elapsed
times above include lock waiting. Synthesis budget200000 retained. No
full project build, main write, PR or integration was performed here.

## Next exact gap

The general theorem that this same actual principal divisor has degree
zero for every nonzero function remains open. The next local prerequisite
is an actual reciprocal-qz element in each boundary ring (especially X),
followed by the finite normalization/norm comparison at infinity. This
must prove completeness and compatibility of the three boundary places;
it cannot be replaced by an opaque product-formula assumption.

The last fresh Mazur root audit remains no sorryAx and exactly three
custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. The base-polynomial
subcase does not discharge N25 or the arbitrary-function target.

Manifest: comms/inbox/research-dot-FLT-N25-POLYNOMIAL-BOUNDARY-ORDERS-r18-manifest.json
