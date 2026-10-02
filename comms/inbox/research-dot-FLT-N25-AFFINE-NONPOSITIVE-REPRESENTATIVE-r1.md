# Genuine principal shift before domination by the base-pole divisor

TASK_ID: FLT-N25-AFFINE-NONPOSITIVE-REPRESENTATIVE
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-SAME-DEGREE-REPRESENTATIVE-AND-DOMINATION-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 9684f1558ee05f7a388c76c181d06e5d9688f050
SUPERSEDES: none

This closes the actual representative-shift issue: nH cannot dominate a
full divisor with positive affine coefficients, so those coefficients must
be handled by a genuine principal transformation first.

N25F_DedekindPrincipalMajorant.lean constructs, for every signed finitely
supported height-one divisor, its nonzero fractional ideal product. A real
nonzero regular element in that ideal has principal coefficients at least
all the specified values, by count_finsuppProd and count_mono. Its existence
is proved, not an approximation hypothesis.

N25F_AffineNonpositiveRepresentative.lean restricts the actual full divisor D
to every affine height-one prime via the established nonboundary equivalence,
constructs the actual function f, and defines D'=D-div(f). It proves:
- every nonboundary coefficient of D' is nonpositive;
- the full weighted degree of D' equals deg D, by the actual product formula;
- D' has exactly the same actual Picard class and genuine section dimension;
- some natural n>=B satisfies D'<=nH at every full closed point;
- deg(nH-D')=4n-deg D exactly.

The bound n may depend on the representative. B remains the fixed basis
constant from the earlier packet. Every affine point is included, and all
three boundary coefficients are checked. No positive affine contribution
was discarded from the degree accounting.

The packet contains nine public declarations in two production modules.

## Validation

PASS: majorant-01, exact complete Mathlib-only source plus its audit. Exit 0,
18.930 seconds, peak RSS 2,740,316 KiB. SHA-256:
5c1f4446f6395ab9e8862a2458e32022a3d956e7994de37bc364e09682e378e6.
One harmless warning flags the unused name of the existential nonzero proof.

PASS: representative-family-04, eight audits, exit 0, 13.648 seconds, peak RSS
2,868,612 KiB. SHA-256:
30629cb224492de154d5ba076905a17364b3d7df1b3f548d95dac290411bf8fb.
It includes the actual signed fractional-ideal construction, the genuine
section/class-rank proof family and full point/height-one reindexing. Existing
point partition, coefficient identifications and product-formula facts are
explicit family parameters; production closes their exact existing names.
One additional linter warning is an unused generic binary-field Algebra
instance in the affine majorant theorem.

All nine final audits are exactly [propext, Classical.choice, Quot.sound],
without sorryAx. Both portable generators reproduce passing bytes exactly.
Earlier named-argument/ring-variable fixture substitutions, a quotient-lemma
application and integer-cast/simp normalization failures are preserved under
failed/ with their rejected downstream sorryAx provenance.

NOT RUN: two full named FLT imports and nine production audits. Pending
candidate integration and the fresh root aggregate audit remain with the
lead. No root custom-axiom elimination or general Riemann--Roch conclusion
is inferred. Lean 4.31.0-rc2 compiler
5e44d5f905127c78a2da7a015fe7a47840c95eb1; Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per invocation,
one CPU/thread, 3072 MiB Lean cap, 60 active seconds; wrapper elapsed times
may include lock wait. No broad build.

## Next owned actual condition-cost step

The previously proved lower bound 4n<=dim L(nH)+4B can now start from a real
representative D' dominated by nH. The remaining theorem must prove that
imposing nH-D' loses at most its full weighted degree: recover genuine W
regular elements from nonnegative affine orders, map them to the actual
finite ideal quotient, retain each residue degree in its dimension, and
impose all three binary boundary conditions. Only then can 4n cancel against
4n-deg D to give a representative-independent general lower bound.

That condition-cost theorem, general high-degree effectiveness and Picard
finiteness are still open. The sharp genus-four RR identity and canonical
geometry are separate. N25/Mazur and the root three custom axioms remain open.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-NONPOSITIVE-REPRESENTATIVE-r1-manifest.json
