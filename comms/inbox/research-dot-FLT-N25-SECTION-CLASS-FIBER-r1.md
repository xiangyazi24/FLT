# Exact actual section/class-fibre correspondence

TASK_ID: FLT-N25-SECTION-CLASS-FIBER
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-BIJECTION-AND-RANK-CARDINALITY-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 7975db007a36d2c9f295bbb2b321d19ee41fac19
SUPERSEDES: none

N25F_SectionClassFiber.lean constructs an exact equivalence between nonzero
members of the actual bounded-pole space L(D) and effective full divisors of
degree (deg D).toNat whose actual class equals [D]. Its map is f -> D+div(f).
Surjectivity takes a genuine function from the principal-subgroup equality
and proves its field value lies in L(D). Injectivity uses the already proved
binary constant kernel. There is no assumed projective-section model.

The actual finite-dimensional space has cardinality 2^finrank(L(D)), and the
class fibre has cardinality 2^finrank(L(D))-1. These statements hold for every
signed full divisor D; negative-degree fibres are automatically empty.
All point carriers and divisor classes remain on the full grading.

## Validation

PASS: family-04, eight declarations, exit 0, 22.286 seconds wrapper elapsed,
peak child RSS 2,229,936 KiB. All eight audits exactly
[propext, Classical.choice, Quot.sound], no warnings or sorryAx.
SHA-256: c14829b5b578119be5610af212bbe41e4a5b091e26d3fb5939357744a029e1da.
The portable generator reproduces these exact bytes.

The fixture composes the genuine bounded-pole submodule, complete all-degree
effective-divisor finiteness producer, and the current section-finiteness
proofs. It exposes the established principal homomorphism, addition-order
inequality, zero degree and injectivity as explicit proof parameters. Actual
production uses their exact names without additional hypotheses. Quotient
class equality is proved by the actual subgroup range definition.

FAIL: family-01/02 used an incorrect namespace for the option-cardinality
lemma; family-03 needed an explicit abbreviation conversion before natural
subtraction. All failed fixtures/logs are isolated under failed/, and are
excluded from PASS evidence. Their downstream sorryAx prints reflect the
failed theorem elaboration, not an accepted imported source assumption.

NOT RUN: full named FLT import and eight production audits. Acceptance of
this and pending dependencies belongs to the lead; no fresh root axiom audit
is inferred. Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1; Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. Shared gate, one CPU/thread,
3072 MiB per Lean process, 60 active seconds. No broad build.

## Next owned proof

Multiplication by a genuine principal representative gives a linear
equivalence L(D) -> L(E), proving representative-independent section rank on
the full Picard quotient. This supplies the actual rank for the existing
full-grading counting interface. The degree+1 upper bound, Riemann--Roch
lower/rank identity, Picard finiteness, and N25/root closure remain open.

Manifest: comms/inbox/research-dot-FLT-N25-SECTION-CLASS-FIBER-r1-manifest.json
