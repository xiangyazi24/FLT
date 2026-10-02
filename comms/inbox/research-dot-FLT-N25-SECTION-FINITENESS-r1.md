# Actual section spaces are finite in every degree

TASK_ID: FLT-N25-SECTION-FINITENESS
REVISION: 1
TYPE: RESULT
STATUS: FULL-GRADING-SECTION-FINITENESS-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: cbc18db13c9d5c3219c54407ff43aa84d4e01334
SUPERSEDES: none

N25F_SectionFiniteness.lean constructs the actual map

    {f : fullRiemannRochSpace25Two D // f ≠ 0}
      -> fullClosedPointGrading25Two.EffDivOfDegree (divisorDegree D).toNat

by f -> D+div(f). It proves the exact coefficient-cast identity and injectivity
using the previously proved binary constant kernel. Fixed-degree effective
divisor finiteness then proves Finite for nonzero sections and all sections,
and Module.Finite (ZMod 2) for the genuine bounded-pole submodule L(D).
The seven declarations apply to every signed divisor D without new hypotheses.

## Full-grading producer checked

CurveZetaEffectiveDivisors.effDivOfDegreeFinite is uniform for every natural
n: the bounded-table injection uses all points of degree <= n, not a fixed
low-degree truncation. The complete producer and its dependencies through
line 200 are included in the passing fixture. The actual full grading uses
fullClosedPointType25TwoFinite for every residue degree, including arbitrary
higher degrees. Its r34 source blob is ad7f3ea9e3562b2dbad55af27e07d80fc8233f06.
Degree<=4 comparisons later in that module are counting bridges only.

## Validation

PASS: family-01, exit 0, 5.934 seconds, peak RSS 2,037,428 KiB. The seven new
declarations and effDivOfDegreeFinite all audit exactly
[propext, Classical.choice, Quot.sound], with no warnings or sorryAx.
SHA-256: a3e87a3eee2c6be8b211b710469714196eaf2ca74e72058b42ddb54b6dcf5d9f.

This fixture contains the actual effective-divisor finiteness proof and the
genuine bounded-pole submodule construction. It exposes the previously proved
principal map, addition-order inequality, degree-zero theorem and injectivity
as explicit parameters. The production source closes each with its exact
named theorem. Parameterized instances are checked as the same propositions
with explicit letI dependencies; the production instances are closed.
Portable generator reproduces the checked bytes exactly.

NOT RUN locally: full named FLT import and its seven audits. The upstream
packets and this result remain pending lead acceptance. This is a genuine
bounded proof-family check, not a fresh root aggregate audit.
Lean 4.31.0-rc2 compiler 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Shared gate, one CPU/thread,
3072 MiB per Lean process, 60 active seconds. No broad build.

## Next owned step

Construct the exact bijection between nonzero L(D) and effective divisors in
the actual full class of D, then prove cardinality 2^finrank(L(D))-1. The sharper
degree+1 upper bound, Riemann--Roch lower/rank identity, Picard finiteness and
N25/root custom-axiom elimination remain separate open claims.

Manifest: comms/inbox/research-dot-FLT-N25-SECTION-FINITENESS-r1-manifest.json
