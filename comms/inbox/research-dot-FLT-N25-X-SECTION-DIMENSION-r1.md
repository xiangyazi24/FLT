# Genuine X-residue filtration and the elementary section-dimension bound

TASK_ID: FLT-N25-X-SECTION-DIMENSION
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-X-FILTRATION-AND-DEGREE-UPPER-BOUND-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 6680617d4e0b866d1dad5ff6d246436df4ab7a6e
SUPERSEDES: none

Three modules prove nine declarations using the actual X point, its local
DVR, common-field embedding, and accepted binary residue-field equivalence.

1. N25F_BinaryResidueCancellation: distinct nonzero fractions of equal DVR
order have difference of strictly higher order when the residue field is F2.
This follows by taking their ratio, applying the actual unit-residue theorem,
and using multiplicativity of the signed order.

2. N25F_XSectionFiltration: L(D-X) is a subspace of L(D); membership in the
next step is exactly strict improvement of X order; any section outside it
has order -D(X); and two sections outside it have difference inside it.
The last theorem closes its local data using xLocalToFraction,
xLocalToFraction_isFractionRing and xLocalResidueRingEquivF2. It does not
assume an abstract leading-coefficient map or codimension premise.

3. N25F_XSectionDimension: any section outside L(D-X) spans the one possible
new direction, giving dim L(D)<=dim L(D-X)+1. Induction using degree(X)=1 and
the proved negative-degree vanishing yields

    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D)
      <= (fullClosedPointGrading25Two.divisorDegree D + 1).toNat.

The actual quotient by the submodule L(D-X) also has dimension at most one.
The statement covers every signed divisor and uses the genuine previously
proved finite-dimensional instances.

## Validation

PASS: cancellation-01, the exact generic cancellation body composed with the
unchanged proved binary-residue lemma. Exit 0, 6.479 seconds, peak RSS
2,879,756 KiB. SHA-256:
dd88968ea17e258d7f49ac6ed15ed2d99ddf4155cd10be11cfc2b0f091e9a246.

PASS: filtration-01, four declaration audits, genuine bounded-pole carrier
and full DVR/residue proof. Exit 0, 59.282 seconds wrapper elapsed, peak RSS
2,922,700 KiB. SHA-256:
f6414b41d7b20f3fb5c6f6c9baf98639b5a0a935765535dcfe85926b55cec56f.

PASS: dimension-03, four final audits including the actual quotient formula.
Exit 0, 11.549 seconds, peak RSS 2,266,516 KiB. SHA-256:
1b391a9e4dc49a75971528e1871d9cee60b98ac18c77a63aa7df3b7026db9254.
All nine final audits are exactly [propext, Classical.choice, Quot.sound],
with no warnings or sorryAx. All generators reproduce the passing bytes.

The filtration fixture exposes the already proved principal coefficient at
X and the actual DVR/residue data as explicit parameters. The dimension
fixture includes the genuine section/finiteness constructions and exposes
the separately checked inclusion/cancellation statements plus degree(X)=1.
Production closes every such parameter using its exact named theorem.

FAIL: dimension-01 used lattice inclusions before specifying their submodule
membership interpretation. Its failed source and rejected downstream sorryAx
logs are isolated under failed/. The prior three-declaration dimension-02
PASS is retained under prior/, superseded by dimension-03's four audits.

NOT RUN: the three full named FLT imports and nine production audits. Lead
integration and the fresh root aggregate audit remain pending; no upstream
candidate acceptance or axiom elimination is inferred from these checks.
Lean 4.31.0-rc2 compiler 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per check,
one CPU/thread, 3072 MiB per Lean process, 60 active seconds. Elapsed times
can include gate wait. No broad build or dependency rebuild.

## Mathematical boundary

This proves the elementary upper bound, not Riemann--Roch's lower bound,
the genus-four residual rank identity, or Picard finiteness. The exact full
class-fibre formula and representative-independent actual rank are in the
previous packet. N25/Mazur and the three-custom-axiom root frontier remain open.

Next owned refinement: construct the genuine X leading-residue functional
using the existing actual uniformizer and DVR integral lift, with kernel
L(D-X), to make the filtration's coefficient map explicit. The deeper
canonical/adjunction and RR lower-bound inputs remain separate.

Manifest: comms/inbox/research-dot-FLT-N25-X-SECTION-DIMENSION-r1-manifest.json
