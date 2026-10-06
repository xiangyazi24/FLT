# N25 high-degree effective representative: source-only candidate

TASK_ID: FLT-N25-HIGH-DEGREE-EFFECTIVE
REVISION: 1
TYPE: RESULT
STATUS: SOURCE-ONLY; UNCOMPILED; ACTUAL-GEOMETRY-CLOSURE-NOT_CONFIRMED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
CANDIDATE_SOURCE_COMMIT: bebaf732e868c6cd34b2072135cf9879c69bd123
EXISTING_COARSE_BUNDLE_COMMIT: 1cb8d721bde52b4adf8bf73722e9f071d355939a
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none
SCOPE: Source-only narrow corollary from the existing actual N25 characteristic-two coarse lower bound to nonzero sections and a linearly equivalent effective representative. No predecessor is replaced.
ACCEPTANCE: Static handoff only. Kernel acceptance requires separate authorized validation of the exact actual-geometry import closure and new declarations; this envelope is not a build or Slurm request.

## New result

For arbitrary D : ProjectiveDivisor25Two, under the single explicit hypothesis

    4 * (wPolynomialBasisPoleBound25Two : ℤ)
      < fullClosedPointGrading25Two.divisorDegree D,

the candidate derives these four declarations in
MazurProof.N25F_HighDegreeEffective:

- finrank_pos_of_degree_gt_four_basis_bound
- nonzeroSection_nonempty_of_degree_gt_four_basis_bound
- riemannRochSpace_ne_bot_of_degree_gt_four_basis_bound
- exists_effective_representative_of_degree_gt_four_basis_bound

The final result returns E in the existing full EffDivOfDegree (deg D).toNat
with the same actual full Picard class as D. Because B is natural, the strict
threshold forces positive integer degree, so the toNat degree is exact.
The existing nonzeroSectionToFullClassFiber25Two map is reused unchanged.

The bound is the actual fixed basis-pole bound, with no claimed numerical
value. There are no extra geometric premises, no restriction to low-degree
closed points, and no substitution of a generic/formal section space.

## Candidate and imports

Candidate:
comms/candidates/N25F_HighDegreeEffective.UNCOMPILED.lean

Intended module:
FLT.Assumptions.MazurProof.N25F_HighDegreeEffective

Direct imports:
- FLT.Assumptions.MazurProof.N25F_CoarseLowerBound
- FLT.Assumptions.MazurProof.N25F_SectionClassFiber
- Mathlib.LinearAlgebra.Dimension.Finite
- Lean.Elab.Tactic.Omega

The same 43 already-published candidate predecessors are reused. Their exact
immutable source pin, Git blob IDs, UTF-8 byte counts and SHA-256 hashes are in
PREDECESSOR_SOURCE_HASHES.json. Static byte checks match all 43 Git blob IDs.
The import map stops at 20 production-pin boundary modules and is not a full
transitive production axiom audit. Adding this one module makes 44 candidate
modules in that overlay.

## Review and verification

PASS (source-only): immediate API shapes; mathematical implication; all four
declarations' full-divisor scope and sole degree hypothesis; effective
representative target; source duplication review; static forbidden-token scan;
43 predecessor source-byte identities; independent static review.

The independent review found no required repair. It reviewed candidate
SHA-256 1ded9a6818a558e0df8aeaf4a4342368c312e15f926a4eca5b9d4a0ab1749cdc.

NOT RUN: Lean elaboration, kernel proof checking, theorem-type readbacks,
transitive #print axioms, actual-geometry build, full project build,
dependency-cache acquisition, SSH, Slurm and integration.

NOT_CONFIRMED: actual geometric closure and all four new corollaries'
kernel acceptance. The prior ShiftedAffineIdeal, KernelSectionInjection and
CoarseLowerBound are not relabeled checked by this source derivation.
Historical generic checks are not actual-curve acceptance.

Toolchain declared by the source: Lean 4.31.0-rc2.
Mathlib source pin: 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
The prospective audit Lean file contains unexecuted commands only.

This handoff changes no old compile assignment, starts no job, republishes no
frozen predecessor bytes, and claims no high-degree kernel acceptance,
Picard finiteness, sharp Riemann--Roch, N25 completion or FLT completion.
Integration authority remains with the existing lead.

This is a new four-declaration source handoff along the resumed N25 task.
The current coordinator connection precheck was reported denied before an
actual run could be established, so actual compilation remains NOT RUN.
The existing 43-module compilation request is not recreated or resubmitted.

Manifest:
comms/inbox/research-dot-FLT-N25-HIGH-DEGREE-EFFECTIVE-r1-manifest.json

This result cannot contain its own eventual commit hash. Any publication
receipt must supply the subsequently verified immutable result commit.
