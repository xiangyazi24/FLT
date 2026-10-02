# Actual polynomial windows and a uniform lower bound along H

TASK_ID: FLT-N25-W-POLYNOMIAL-WINDOW
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-INDEPENDENT-WINDOW-AND-UNIFORM-H-LOWER-BOUND-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 8f549b054f5b43b3137220d58b72726fb09c6cc9
SUPERSEDES: none

Four modules prove eleven declarations. They multiply the fixed four-element
actual W basis by the first n+1 monomials in its existing F2[z] base, embed
these actual W elements into the common field, and prove

    4*(n+1) <= dim L((B+n)H)
    4*n <= dim L(nH) + 4*B.

Here H=X+YZ+2Z is the actual full pole-weight divisor of degree four, and B is
the previously constructed fixed-basis constant. Both statements use genuine
bounded-pole spaces, and B is independent of n and of every divisor class.

N25F_PolynomialBasisWindow proves independence from the polynomial monomial
basis and the actual scalar-tower basis construction. N25F_SectionMultiplication
proves monotonicity and multiplication of the genuine section spaces.
N25F_BasePolePowers puts actual powers of Z/W into L(nH), using all three
established boundary orders and the proved affine positivity check.
N25F_WPolynomialWindow combines these with the fixed-basis membership, proves
all 4(n+1) functions lie in the required full section space, and derives both
uniform dimension inequalities.

## Validation

PASS: window-generic-03, one audit, exit 0, 7.722 seconds, peak RSS 1,823,648 KiB.
SHA-256: 708ca4f183911e847949370aae3ace660d83b19cc363e8bdfd4ffe79c09a7181.
The tiny Polynomial.Basis cache module was absent, so this check includes its
exact unchanged pinned source definition/theorem and imports its cached
dependencies. It checks the production generic proof body; its named module
import is still part of the lead gate. No cache or dependency build was run.

PASS: powers-family-03, five audits, exit 0, 18.485 seconds, peak RSS
2,719,008 KiB. SHA-256:
cb15c62a81da0fabd35520744051d7f71a2bae31c5bdc1a7a0d4c90c532edb93.
It composes the genuine regular-function pole-space proof with the existing
exact three Z/W orders and the actual principal-homomorphism multiplication.

PASS: window-family-02, five audits, exit 0, 25.244 seconds, peak RSS
2,295,940 KiB. SHA-256:
13606b61c9fbd7d7f77ed60bcdf3d8d5ea8d27f6ec84e0f3b89ae611cf74c90d.
The family uses the canonical fraction-field scalar action, matching the
actual source, and the genuine section-finiteness construction. Previously
proved power/basis membership and positivity are explicit family inputs;
production closes them with the exact names from this and earlier packets.
Two linter warnings concern an unused generic IsDomain instance in source-
comparison/independence helpers. They are not missing hypotheses or axioms.

All eleven final audits are exactly [propext, Classical.choice, Quot.sound],
without sorryAx. All three portable generators reproduce the checked bytes.
Failed namespace/type-annotation/argument-grouping attempts and the initial
noncanonical fraction-module fixture are isolated under failed/ with their
rejected downstream sorryAx provenance. PASS evidence excludes those attempts.

NOT RUN: all four full named FLT imports and eleven production audits. Lead
integration and fresh aggregate acceptance remain pending. No root custom-
axiom elimination is inferred. Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1; Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. Shared gate, one CPU/thread,
3072 MiB Lean cap, 60 active seconds. No broad build.

## Exact remaining domination issue and next owned proof

The proved lower bounds concern L(nH), not arbitrary L(D). Since H is only
supported at the boundary, nH cannot dominate arbitrary positive affine
coefficients. Ignoring those coefficients would invalidate a uniform
bound in deg D.

The next actual producer is a principal representative shift. For a signed
affine divisor, take its genuine nonzero fractional ideal product and choose
a nonzero element f. Dedekind count monotonicity should prove div(f)>=D_aff
at every affine prime. Thus D'=D-div(f) has nonpositive affine coefficients;
the already proved projective product formula preserves its full degree.
Only after this shift can an nH dominate D'. The affine condition costs must
retain residue-degree weights, and all three boundary costs must be included.

The final general lower bound, high-degree effectiveness and Picard finiteness
are still open. The sharp genus-four RR identity/canonical geometry remain
separate. No general-Picard claim is made by this packet.

Manifest: comms/inbox/research-dot-FLT-N25-W-POLYNOMIAL-WINDOW-r1-manifest.json
