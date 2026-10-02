# An actual degree-one full Picard class

TASK_ID: FLT-N25-FULL-PICARD-BASE
REVISION: 1
TYPE: RESULT
STATUS: DEGREE-ONE-CLASS-AND-FIBRE-TRANSLATION-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: d7822bff78034fa127f596ef37d18031ece6bd47
SUPERSEDES: none; removes the abstract base-class input on the full quotient

N25F_FullPicardBasePoint.lean chooses the class of the existing actual
X-boundary closed point fullBoundaryAtomOfTag .X, with multiplicity one.
The accepted source proves that point has residue degree one. The candidate
proves that its class has degree one in the actual full principal quotient,
that class degree is surjective onto the integers, and constructs

    fullProjectivePicDegreeEquivZero25Two (n : ℤ) : Pic^n ≃ Pic^0

using translation by minus n copies of that actual class. The Lean type uses
fullClosedPointGrading25Two.PicDegree with the actual principal subgroup and
its proved degree-kernel inclusion. No finite Picard type, abstract base class,
or truncated closed-point carrier is substituted.

PASS: family-01 exit 0, 5.491 seconds wrapper elapsed, peak child RSS
1,793,440 KiB. All four audits exactly [propext, Classical.choice, Quot.sound],
with no warnings or sorryAx. SHA-256:
8d3d461bf5f0280c6cf25d8e476d2ea64bce6c4ff58d3219e9166f9e490b1dcf.

The fixture extracts the exact ClosedPointGrading, divisor/class-degree,
PicDegree and translation definitions from the current repository sources.
It exposes the previously proved principal degree-zero fact and the accepted
degree-one atom fact. Production supplies the actual maps and X atom by name.
The generator and source inputs are attached, so no alternate Picard model
is hidden in the check.

NOT RUN locally: full named FLT import and the four production audits.
ActualFullPicardBasePointCheck.lean enumerates them. The upstream product
formula, full Picard-degree packet and this packet remain pending lead
acceptance. Dispatch was rechecked and is still r34.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared-gate
acquisition, one CPU/thread, 3,072 MiB cap, 60 active compiler seconds.
No broad build, source weakening or change to accepted production files.

The remaining substantive inputs for the full-grading class-number route
are Picard finiteness, complete-linear-system fibre cardinalities, and the
genus-four Riemann--Roch rank formula, including the genuine canonical class.
The degree-one class and fibre translation do not prove those inputs or
remove the order-25 axiom. The root three-custom-axiom frontier is unchanged.

Manifest: comms/inbox/research-dot-FLT-N25-FULL-PICARD-BASE-r1-manifest.json
