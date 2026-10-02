# Actual qz pole order at X

TASK_ID: FLT-N25-X-BOUNDARY-Z-ORDER
REVISION: 1
TYPE: RESULT
STATUS: SOURCE-CANDIDATE-AND-SELECTIVE-CHECK-PASS
PARENT_SCOPE: FLT-N25-AFFINE-DEGREE boundary orders
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: d74efae7f82cdc56e4ee7f396fc0c0c1a2605c5a
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none
DEPENDENCY_CANDIDATE: N25F_XCoordinateOrders at fa094f11e2cf49c6c797c29c7d65ce28fb56bf15, full-import acceptance not yet observed

Candidate: comms/candidates/N25F_XBoundaryZOrder.lean
Namespace: MazurProof.N25F_XBoundaryZOrder

New exact result:

    xBoundaryOrder (Additive.ofMul (Units.mk0
      (algebraMap W (FractionRing W) qz) fraction_qz_ne_zero)) = -1

The theorem uses the already-defined genuine X-local Ring.ordFrac and
coordinate-rigid common-field embedding. The existing source field image
of Z/X is qz/qx. The preceding candidate proves its actual local order2;
W/X has the already accepted order3. Thus qz=(Z/X)/(W/X) has order2-3=-1.
Supporting theorems give that field image, nonzero germ, and field order2.
There are no added production hypotheses or abstract valuation premises.

PASS: selective actual-X-point harness, all four new public audits exactly
propext/Classical.choice/Quot.sound, no sorryAx. Wrapper time96.521s includes
shared-lock waiting; the Lean invocation remains capped60s. Peak child RSS
2,926,752KiB. Benign unused-section-variable fixture warnings are in the log.
Explicit fixture parameters are the accepted W Dedekind structure, existing
W/X order3 and accepted fraction_qz_ne_zero. The new Z/X order2 is proved
inside the same check, not supplied as a premise. Actual xChartEval and
xPrime are source-derived, not arbitrary point parameters.

NOT RUN locally: this parameter-free production module and its pending
X-coordinate-order dependency with complete FLT imports. The attached
ActualXBoundaryZOrderCheck.lean audits all four declarations for the lead.
The accepted YZ field-map proof repairs in r15 are unrelated dependencies;
they are synchronized in the accompanying r15 ACK rather than relabeled
byte-equal.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. One CPU/thread,3072MiB Lean
cap,60s compiler limit, shared gate per invocation, synth budget200000.
No broad build was launched here.

With the concurrent YZ order candidate and accepted Z order, qz has the
three actual signed boundary orders(-1,-1,-2). This is a function-specific
boundary calculation, not a general principal-divisor product formula.
The latter remains open, as does the N25 custom axiom. The three-custom-
axiom Mazur root frontier has not been changed by this local check.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r15-manifest.json
