# Degree-zero constancy and the actual principal kernel

TASK_ID: FLT-N25-ZERO-DEGREE-CONSTANTS
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-CONSTANT-LINE-AND-PRINCIPAL-INJECTIVITY-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: e08cf8eeca5f5b55ec85cfb530f8b9f2701342ff
SUPERSEDES: none; proves the actual constant-function kernel

N25F_ZeroDegreeConstants.lean proves the exact statement

    a ∈ fullRiemannRochSpace25Two 0 ↔ a = 0 ∨ a = 1.

It then identifies this space with the span of 1, proves its finite-dimensional
instance and dimension 1, proves projectivePrincipalDivisor f=0 iff f=0 in
the additive unit group, and proves the actual full principal-divisor map
injective. Here f=0 means the multiplicative identity function 1. The result
is specific to the genuine binary constant field, whose only nonzero element
is one; it makes no analogous injectivity claim for the affine-only divisor.

## Genuine local/global proof

A nonzero globally regular function cannot have positive order at the actual
degree-one X point, since it would lie in the already vanishing space L(-X).
Its X-order is therefore zero. N25F_BinaryResidueOrder.lean derives a unit germ
from the actual ordFrac kernel, uses the actual residue map to the binary
field, and proves that f-1 has positive order unless f=1. But f-1 is still
globally regular, so the same L(-X) contradiction proves constancy.

The X residue equivalence is the accepted xLocalResidueRingEquivF2, not an
assumed constant-field assertion. Its current production source was read back
byte-equal at blob 18c50ccdb25902a9dc513699195381689946700e. The X atom and its
degree-one theorem are the existing full-grading objects.

Two modules contain nine public declarations: one exact generic DVR/residue
lemma and eight actual constancy, dimension and principal-kernel declarations.
No Riemann--Roch rank formula, Picard finiteness or arbitrary section-space
model is an input to the actual theorems.

## Validation

PASS: residue-01, exact complete generic production source plus its audit,
exit 0, 58.789 seconds wrapper elapsed, peak child RSS 2,907,044 KiB,
exactly [propext, Classical.choice, Quot.sound], no warnings or sorryAx.
SHA-256: 1b3e05fc5c4662fd4d4847c5c9ae50e80ba13be3bedfebc7f848386f8d3d7d86.

PASS: constants-family-04, exit 0, 14.350 seconds, peak child RSS
2,947,152 KiB. All eight final actual-theorem family audits are exactly the
standard three, with no warnings or sorryAx. SHA-256:
3ab542b14b2270bd48668aaa73994abe56ce01d173c134dced67f2f3898b862f.

The family imports/reproduces the genuine bounded-pole submodule and negative-
degree proof, then exposes the previously proved principal coefficient at X,
its degree-one fact, and the actual DVR/residue-field data. The production
proof closes each input with its exact existing name. The generic finite-
dimensional instance is checked as the same proposition with explicit data
parameters; the actual production instance has no such free parameters.
The portable generator reproduces the passing bytes exactly.

Earlier family failures were test-binding/doc placement and simplification
errors; their logs/receipts are isolated from PASS evidence. The six-declaration
constancy checkpoint passed before adding the two principal-kernel corollaries;
the final eight-declaration checkpoint supersedes it for this delivery.

NOT RUN locally: the two full named FLT imports and nine production audits.
ActualZeroDegreeConstantsCheck.lean lists that gate. The upstream packets and
this packet remain pending lead acceptance; no fresh root kernel audit is
inferred. All sources retain the fixed Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1 and Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per check, one
CPU/thread, 3,072 MiB cap, 60 active seconds. Wrapper times may include waiting.

## Next owned result

Over F2 this proved injectivity makes f -> D+div(f) injective on nonzero L(D).
The accepted full-grading producer effDivOfDegreeFinite is uniform in every
degree n. fullClosedPointGrading25Two supplies finite_closed at every residue
degree; the later degree<=4 equivalences are only point-count comparisons.
The next target is therefore actual section-space finiteness and the precise
effective-divisor class-fibre bijection, using the full grading throughout.

The sharper degree+1 upper bound, genuine Riemann--Roch lower/rank identity,
and Picard finiteness are separate remaining claims. N25/Mazur and the root
three-custom-axiom frontier remain open.

Manifest: comms/inbox/research-dot-FLT-N25-ZERO-DEGREE-CONSTANTS-r1-manifest.json
