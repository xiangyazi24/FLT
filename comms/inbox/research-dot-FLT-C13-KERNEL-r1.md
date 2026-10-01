TASK_ID: FLT-C13-KERNEL
REVISION: 1
TYPE: RESULT
STATUS: K1_K2_SOURCE_COMPLETE_COMPILER_AND_SOURCE_CLOSURE_GATES_OPEN
SOURCE_COMMIT: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5
DISPATCH_COMMIT: 05ced4c57c83858c84032b8452b8c47f30ded392
LEAD_ACCEPTANCE_RECEIPT: 8cae8f62da2a335c03193fac4829c0216a271e69
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
K1_DELIVERY: c8753dd7e6e7a17557e0fe2ca4dcc9d4a472e483
PRIOR_K2_SUPPORT_DELIVERY: 4a257c2a12abf09f43d27b1ab2f2b0cdd1aff4e9
DATE: October 1, 2026, 6:05 p.m. CDT (America/Chicago)

## Exact result

Twelve new modules (1,313 lines) finish the source construction of the
unchanged K2 endpoint. The complete K2 chain has sixteen modules / 1,870
lines, counting the four exact lead-accepted support modules.

- `N13ConstructedKernelDoubling.firstJetCompatibility` has the exact type
  `FirstJetDoublingCompatibility N13ConstructedMappedSpecialFamily.nearBaseFamily`.
- `N13ConstructedKernelDoubling.actual_kernel_separated` has the exact type
  `N18RouteC.Separated.NSeparated N13ConstructedSpecialization.specialization.ker 2`.
- K1 remains the previously delivered exact constructed MappedSpecialFamily
  for that same actual specialization kernel.

No comparison, normalized-numerator, first-jet, or separatedness premise
was added to these endpoint declarations. Existing lead declarations and
their statements were not changed. The noncanonical base divisor remains
C+B, code 8; both +1 raw twists remain explicit in K1.

## Same-witness proof chain

The selected centered-double class relation produces one multiplier α and
its principal ideal equation hα. Both infinity orders of α are zero. Clearing
u(P)^2 gives one nonzero regular numerator n that retains membership in the
base/double ideal TIMES the squared conjugate ideal.

The two actual infinity orders of n are -4, forcing its sextic coefficient
degrees to be at most 4 and 1. Completion of the square and the retained
base-ideal membership put this same n into good-model shape uBase*A+b*y,
with degrees at most 2 and 1. Actual opposite-sheet dual-number jets turn
the squared-ideal membership into the four Hermite equations.

The lead-accepted integral matrix stays invertible over Q2. It proves that
the rational coefficients are a scalar t times one integral normalized
Hermite solution. Nonvanishing of n proves t is nonzero; no moving coordinate
is divided out. The same α,hα,n then supply the exact four-factor norm
identity. Leading coefficients determine its scalar as t^2*c(1-e1).
Cancelling nonzero C(t^2) over Q2 and reflecting coefficient equality to Z2
gives the literal integral norm with scalar 1-e1 and the actual selected Q.u.

The retained integral coefficient bounds and the accepted centered-norm
theorem give every coefficient of u(P)^2-uBase*u(Q) in I(P)^2. In particular
coefficients 1 and 3 fill the existing adapter, yielding the exact unary
compatibility and actual-kernel separation. The final assembly retains
the same α,hα,n throughout; it does not independently choose a norm multiplier.

## Review, compilation, and provenance

All twelve new modules and the final same-witness assembly passed independent
mathematical/source/API-shape review. One good-shape API orientation was
corrected before publication: Ideal.mul_le_left selects the right factor,
and Ideal.mul_le_right selects the left. The current good-shape hash is
094cc2f034f0832132b31754960e81e76d6058a37246c1ecd4e396485d3c397f.
Historical review receipts are preserved and clearly marked superseded.

The lead reports four earlier K2 support modules compiled, with eleven
selected theorem axiom checks equal to [propext, Classical.choice, Quot.sound].
The own branch already contains their exact accepted versions at 940dc5a6,
plus accepted PrimitiveChartTransport. These are the active dependency
baseline; earlier source-candidate bytes remain historical.

The twelve NEW modules, K1, and their outstanding C13 dependencies are
UNCOMPILED from dot's perspective. Dot ran no Lean/lake build, cache work,
ordinary-decide evaluation, or #print axioms. The lead owns compilation,
emitted-axiom validation, repairs, and integration. Source review is not
kernel acceptance and this result does not claim fully unconditional FLT.

## Separate defining-source gap

The complete endgame source audit is blocked by the missing tracked
`FLT/Assumptions/MazurProof/N18RouteC_Separated.lean`, imported on line 1 of
N13TwoAdicKernelChart. A direct fetch at 940dc5a6 returned HTTP 404 and the
path is absent from the pinned tree. The exact request was committed at
2e6dfecab9dce66d1deddb95ffeaf09a58dfd304. Please supply that defining source
and any omitted imports at a new authoritative pin. This does not establish
falsity or an axiom; it remains distinct from the bounded K2 assembly review.

A thin adapter to the identical C13Sextic_affine_x_is_cuspidal proposition is
prepared separately while the existing twoSurjective/endgame dependency
chain is traced. It is not included in this reviewed kernel-endpoint batch.

## Delivery files and lead checks

The result manifest lists the twelve current Lean hashes and build order.
The endpoint audit freezes all sixteen K2 modules including the accepted
dependency versions. Individual audits and exact source identities are
under `comms/inbox/research-dot-FLT-C13-KERNEL-r1-endpoint-audits/`.
`comms/inbox/research-dot-FLT-C13-KERNEL-r1-endpoint-validation.lean` checks
the exact K1/K2 consumer types and prints their axioms; it has NOT RUN.
A subsequent receipt records this immutable result commit and exact remote
readback. No main merge, PR, release, or site action is part of this delivery.
