# Actual W regular lifts and residue-degree-weighted affine condition costs

TASK_ID: FLT-N25-W-AFFINE-CONDITION-COST
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-AFFINE-REGULAR-LIFT-KERNEL-AND-WEIGHTED-COST-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 4d3482cbd4e6212f7097371dc3388f8934793c51
SUPERSEDES: none

Three modules prove fourteen public declarations.

N25F_DedekindOrderMembership proves the reverse direction of the genuine
fractional-ideal order comparison. Nonnegative counts imply an integral
fractional ideal; count inequalities imply inclusion; all nonnegative affine
orders give a unique real ring preimage; and membership in a nonzero
fractional ideal is equivalent to its full count inequalities, for nonzero
functions. Zero cases are kept explicit.

N25F_WRegularSectionLift proves that every actual f in L(nH) has a unique
W-chart representative, because H has no affine support and all affine
principal orders are nonnegative. The actual lift has its exact common-field
image and forms an injective F2-linear map L(nH) -> W.

N25F_WAffineConditionCost composes that producer with W -> W/I. It proves the
kernel is exactly the actual ideal-membership condition, equivalently zero
or all the ideal-order inequalities. For every nonzero actual ideal I,

    dim L(nH) <= dim ker(condition map) + dim_F2(W/I)
              = dim ker(condition map)
                + sum_P multiplicity(P,I) * dim_F2(W/P).

The last sum keeps every residue-field degree. The finite quotient instance
is proved from the actual Dedekind finite-type W chart; no assumed finite
quotient or abstract linear-system model is substituted.

## Current-source check

The old local file N25F_WChartIdealDegree.lean is absent at accepted r34 and
is not treated as integrated. The needed general weighted formula is
present in N25F_DedekindFactorDegree.lean at blob
8fbc4b58fda1005453cdf6075bfd65dff22867b8. Its complete current source is included
in the final cost family, and production closes the specialization directly
with DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors.

## Validation

PASS: membership-02, four generic audits, exit 0, 30.149 seconds, peak RSS
2,792,072 KiB. SHA-256:
8d26a5eaac4642875e9fb9e5d892bffd9b7b021cabecea41e868f4c40d1fa2a8.
It composes exact generic proof bodies with the unchanged accepted
CurveDedekindDivisor source. One warning is the supported but deprecated
mul_le_mul_right' alias.

PASS: regular-family-01, five audits, exit 0, 11.119 seconds, peak RSS
2,841,144 KiB. SHA-256:
cb2b86c1e01606e272d36ba5ce0ff50aaa81346fcda0b8c539953b6d0fe1b70d.
It includes the genuine section carrier and full Dedekind integrality proof;
the established nonboundary/prime equivalence and coefficient identity are
explicit family data, closed by the actual names in production.

PASS: cost-family-01, five audits, exit 0, 15.127 seconds, peak RSS
2,859,368 KiB. SHA-256:
ebe3182e90e17c05599261932300fa79db2a2a296c5a4bf3f47094f088e25be3.
It composes the actual-style regular lift and exact accepted weighted
quotient proof. The previously proved finite section-space instance is an
explicit family parameter, closed by the actual global instance in production.
The quotient finiteness proof itself is checked. Besides the inherited
deprecation warning, one generic finite-type instance is unused in a kernel
identity theorem.

All fourteen final audits are exactly [propext, Classical.choice, Quot.sound],
without sorryAx. All generators reproduce passing bytes exactly. The initial
membership check's wrong namespace/explicit-submonoid arguments and rejected
downstream sorryAx prints are isolated under failed/.

NOT RUN: three full named FLT imports and fourteen production audits. Pending
candidate integration and the fresh root aggregate audit remain with the
lead. No root custom-axiom elimination is inferred. Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1; Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per invocation,
one CPU/thread, 3072 MiB Lean cap, 60 active seconds. No broad build.

## Next owned concrete step

Attach the nonzero integral ideal to the shifted divisor's nonpositive
affine coefficients and identify its quotient cost with the full affine
degree. Add the genuine binary residue filtration bounds at YZ and Z as
well as X, then impose the three boundary costs. This is still required to
identify the final kernel with L(D') and cancel the exact complement degree
4n-deg D against the uniform base-pole lower bound.

The general divisor lower bound, high-degree effectiveness, Picard finiteness
and sharp genus-four RR identity remain open. The actual source producers
in this packet discharge the affine regularity and weighted quotient-cost
inputs, not those later conclusions.

Manifest: comms/inbox/research-dot-FLT-N25-W-AFFINE-CONDITION-COST-r1-manifest.json
