# N25 high-degree effectiveness: source-only candidate

Source-preparation status: LOCAL, UNCOMPILED. No Lean or Lake execution, kernel check, transitive
axiom check, dependency-cache acquisition, SSH or Slurm job was performed.
No Git mutation or publication was performed during that preparation. This does not accept or repair
the older actual-geometry candidates.

## Result and exact assumptions

For every D : ProjectiveDivisor25Two, with the sole explicit hypothesis

    4 * (wPolynomialBasisPoleBound25Two : ℤ)
      < fullClosedPointGrading25Two.divisorDegree D,

the candidate derives:

1. 0 < Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D).
2. Nonempty (NonzeroSection25Two D).
3. fullRiemannRochSpace25Two D ≠ ⊥.
4. An E in fullClosedPointGrading25Two.EffDivOfDegree (deg D).toNat
   whose effectiveToDivisor has the same fullProjectivePrincipalSubgroup25Two
   class as D.

All four statements have exactly the D and strict-degree arguments above.
There are no free type parameters, geometric hypotheses, bound hypotheses,
finite-dimensionality arguments, or model-substitution parameters.

The scalar field is the actual ZMod 2. The constant B is the existing natural
number wPolynomialBasisPoleBound25Two, constructed from the fixed rank-four
polynomial basis. It is not an arbitrary parameter and no numerical B is
claimed. D remains an arbitrary signed divisor on the full actual closed-point
carrier; it is not assumed effective, supported on the boundary, or bounded
in closed-point degree.

## Exact new imports

- FLT.Assumptions.MazurProof.N25F_CoarseLowerBound
- FLT.Assumptions.MazurProof.N25F_SectionClassFiber
- Mathlib.LinearAlgebra.Dimension.Finite
- Lean.Elab.Tactic.Omega

Intended module:
FLT.Assumptions.MazurProof.N25F_HighDegreeEffective

The .UNCOMPILED filename is a delivery label. An authorized checker would
place it at FLT/Assumptions/MazurProof/N25F_HighDegreeEffective.lean in an
isolated overlay with the exact existing predecessors. This task does not
create that build environment or run the prospective audit commands.

## Proof audit

### Positive rank

The existing degree_le_finrank_add_four_basis_bound D states exactly
deg D ≤ (finrank_F2 L(D) : ℤ) + 4B. Together with 4B < deg D this gives
positive finrank. The only new proof step is integer/natural arithmetic via
omega. The coefficient 4 and strict inequality are retained.

### Nonzero section

Pinned Mathlib/LinearAlgebra/Dimension/Finite.lean provides
Module.finrank_pos_iff_exists_ne_zero with parameters R and M. The existing
fullRiemannRochSpace25Two_moduleFinite D instance from SectionFiniteness
provides Module.Finite (ZMod 2) (fullRiemannRochSpace25Two D). The field/module
instances give StrongRankCondition, IsDomain and IsTorsionFree. The obtained
f : fullRiemannRochSpace25Two D with f ≠ 0 is packaged using the existing
NonzeroSection25Two D abbreviation. No new finiteness assumption is inserted.

### Nonzero submodule

If the actual submodule were ⊥, rewriting its finrank by the pinned root
theorem finrank_bot gives zero, contradicting positive finrank.

### Effective representative

The candidate reuses nonzeroSectionToFullClassFiber25Two D f directly.
Its codomain FullEffectiveClassFiber25Two D is already the subtype of
effective divisors of degree (deg D).toNat whose actual full Picard class
equals that of D. Projecting its value and property is the complete final
proof. The conversion from sections to effective divisors is not redefined.

The existing source constructs E = D + div(f), with coefficientwise
nonnegativity from membership in the actual Riemann--Roch space and degree
preservation from the actual projective product formula. The subgroup is
the range of projectivePrincipalDivisor on Additive CurveFieldˣ; equality
of classes therefore has the genuine linear-equivalence meaning.

The natural-degree encoding loses nothing: B is natural, so the strict
threshold implies deg D > 0 and ((deg D).toNat : ℤ) = deg D. This is also
consistent with the existing degree_nonneg_of_nonzero_mem theorem and the
cast identity effectiveDivisorOfNonzeroSection25Two_cast.

## Source pins and inherited uncertainty

Production pin: 51bbb4f191ad0d3753b87123635c100a638ae580.
Collaboration pin: bebaf732e868c6cd34b2072135cf9879c69bd123.
Existing coarse candidate bundle: 1cb8d721bde52b4adf8bf73722e9f071d355939a.
Dispatch pin: 9700ca106515f04411193844fbb347d40d86e481.
Mathlib pin: 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
Toolchain declared by the repository: leanprover/lean4:v4.31.0-rc2.

Static import tracing reaches the same 43 existing candidate modules and
20 production-pin boundary modules. SectionClassFiber is already a transitive
dependency of CoarseLowerBound, through AffineNonpositiveRepresentative,
FullPicardSectionRank and SectionPrincipalTransport. The new candidate adds
one module, bringing that candidate overlay to 44 modules; it does not add
a new predecessor chain. CANDIDATE_IMPORT_MAP.json records the exact paths,
module names and Git blob IDs. Traversal stops at the production boundary,
so this is not a full transitive production-import or axiom audit.

The older ShiftedAffineIdeal, KernelSectionInjection and CoarseLowerBound
remain source-only actual-geometry candidates. Their historical generic
checks do not establish the actual geometric chain. This corollary's
compilation and semantic acceptance therefore remain NOT_CONFIRMED.

## Duplication and scope

The current COMMS protocol and the coarse-bound result envelope were read.
All 103 N25F candidate sources at the collaboration pin were searched for
the endpoint/threshold, and production and dispatch tree names were checked.
No existing high-degree corollary was found. The existing result envelope
explicitly says high-degree effectiveness is unestablished.
DUPLICATION_REVIEW.json records the search scope. This is not an exhaustive
semantic-equivalence search over every repository declaration.

The four declarations add no sorry, admit, axiom, unsafe, native_decide or
sorryAx token. The same comment-stripped textual scan found none in the
43 inherited candidate modules. This is a static text check only, not a
claim about their accepted proofs or transitive axiom sets.

No Picard-finiteness theorem, sharp Riemann--Roch theorem, characteristic-three
analogue, numerical threshold, or FLT endpoint closure is claimed.

## Verification status

- PASS (source-only): interfaces, mathematical implication, strict threshold,
  full-divisor scope, exact effective-class target, dependency-source lookup,
  duplication review, forbidden-token scan.
- NOT RUN: Lean elaboration, all four theorem-type readbacks, kernel checking,
  prospective #print axioms commands, actual-geometry compilation, integration.
- NOT_CONFIRMED: transitive actual-geometry acceptance.

N25F_HighDegreeEffectiveAudit.UNCOMPILED.lean contains prospective type
readback and axiom-audit commands for the designated checker. It is not an
audit log and was not executed.
