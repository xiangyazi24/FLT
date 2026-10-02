# Fixed rank-four W basis with one genuine uniform pole bound

TASK_ID: FLT-N25-W-BASIS-POLE-BOUND
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-BASIS-IN-UNIFORM-SECTION-SPACE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 77ceeb2555eb82aef5c5e889f0e6493012980752
SUPERSEDES: none

N25F_WBasisPoleBound.lean fixes an actual Fin 4 basis of the existing W chart
as a module over its established F2[z] action. The basis is constructed from
the proved finite torsion-free module structure and exact rank-four theorem;
it is not a guessed monomial basis or an assumed field basis. The current
rank source was fetched at blob c98235ce39e3f417b29fcc68afb5f4f8f177b299.

A single natural B is the finite sum, over the four fixed basis functions,
of the negative parts of their actual X,YZ,Z orders. Thus B depends only on
this fixed curve/basis. It contains no divisor or divisor-representative
argument. Every basis function has X and YZ order >=-B and Z order >=-2B.
The weights 1,1,2 are those of the established base coordinate Z/W.

N25F_WBasisPoleSections.lean constructs the full divisor H=X+YZ+2Z, proves
deg H=4, and proves all four basis functions belong to the genuine L(B H).
Its more general regular-function lemma discharges every nonboundary
condition using the actual Dedekind principal-ideal factor multiplicities.
No affine coefficient nonnegativity premise is assumed. The only supplied
bounds are the three displayed boundary orders.

These two modules have nine public declarations. They provide a uniform
starting section space for a coarse lower-bound argument, independent of
all later divisor representatives.

## Validation

PASS: basis-04, five audits, exit 0, 4.196 seconds, peak RSS 2,228,284 KiB.
SHA-256: 00317521a9d1c28fd27056da6aaea23cb9e3e570a6c8023865fbab790a60bbc1.

PASS: sections-03, four audits, exit 0, 8.954 seconds, peak RSS 2,775,144 KiB.
SHA-256: f7289745a75b3e4173ed73e33e73f4ddc4b5190d480e32bb4a807e229c76ef15.
All nine final audits are exactly [propext, Classical.choice, Quot.sound],
with no warnings or sorryAx. Both portable generators reproduce checked bytes.

The first family retains the actual polynomial base and fraction-field
construction, exposing the existing finite torsion-free W data and rank-four
fact. The second contains the genuine bounded-pole carrier, Dedekind divisor
and regular coefficient proofs. It exposes the already proved full atom
partition/coefficient identifications and the separately checked fixed basis
bound. Production closes these data with their exact current names.

FAIL: basis-01/02/03 corrected namespace/import, Unicode fixture substitution,
sum scope and explicit summand inference. sections-01/02 corrected a generic
function argument grouping, match reduction and degree-homomorphism unfolding.
Their failed sources and rejected downstream sorryAx prints are isolated
under failed/ and excluded from PASS evidence.

NOT RUN: full named FLT imports and nine production audits. All pending
candidate dependencies and this packet await lead integration/fresh aggregate
acceptance. No root axiom elimination is inferred from bounded checks.
Lean 4.31.0-rc2 compiler 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per check,
one CPU/thread, 3072 MiB Lean cap, 60 active seconds. No broad build.

## Next owned concrete proof

Use the actual polynomial monomial basis and the fixed four-element W basis
to construct 4(n+1) independent functions in L((B+n)H). Then impose affine
ideal conditions with their full residue-degree-weighted quotient dimensions,
and all three boundary constraints. Effectiveness of every sufficiently
high-degree class requires a uniform final constant independent of its
representative; that is not yet proved. Picard finiteness and the sharp
genus-four Riemann--Roch identity remain open and distinct.

Manifest: comms/inbox/research-dot-FLT-N25-W-BASIS-POLE-BOUND-r1-manifest.json
