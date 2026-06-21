# A6 DE-RISK PROTOTYPE BUILD — resultant=Δ² + projective height lower bound

You are building the de-risk prototype for the A6 height-based torsion-finiteness
campaign (Mazur |T|≤16, branch ai-scratch, repo ~/repos/flt-ai). The full 10-round
design is in scratch/A6_BUILD_SYNTHESIS.md (READ IT FIRST). The per-round full code:
- scratch/A6_R6_Resultant_Bezout_FULL.md  (resultant=Δ², near-complete Lean)
- scratch/A6_R5_EC_Duplication_FULL.md     (dupNumH/dupDenH defs)
- scratch/A6_R7_Base_Northcott_FULL.md     (not needed this round)

## GOAL (this round = de-risk ONLY, not the full discharge)
Create a STANDALONE new file `scratch/A6HeightProto.lean` and drive the build of it
to GREEN with 0 sorries on pieces (1)+(2). You are running ON uisai2 — build the new
target directly here with the repo's normal `lake build <target>` (incremental; Mathlib
is cached on this box; 64 cores, build freely). Do NOT edit any already-built file. Do
NOT wire into Torsion.lean. Isolated prototype to validate the algebraic backbone.

Pieces to land (in order):
1. **resultant_dupNum_dupDen : (dupNumPoly W).resultant (dupDenPoly W) 4 4 = W.Δ^2**
   Transcribe R6's approach: universal `MvPolynomial (Fin 4) ℤ` symbolic resultant `rawRes`
   proved once by `native_decide` (set_option maxHeartbeats 0 if needed — Mathlib
   native_decide can SIGTERM at default heartbeats), then specialize via aeval + reduce with
   `W.b_relation`. R6 gives the explicit rawRes polynomial and the cofactor certificate. If the
   exact Mathlib resultant API name/signature differs (Polynomial.resultant degree params,
   W.b_relation, W.Δ_ne_zero), RESOLVE by building — these are API-name fixes, grind them.
2. **resultant_dupNum_dupDen_ne_zero** [W.IsElliptic] via sq_ne_zero W.Δ_ne_zero.
3. **dup_projective_height_lower** (the RISKIEST piece per R8 adversarial — the de-risk target):
   a PURE binary-form lemma, NO elliptic-curve points. Statement: for the homogeneous forms
   F=dupNumH, G=dupDenH with resultant Δ²≠0, the two Bezout identities
       Δ²·X⁷ = A·F + B·G   and   Δ²·Z⁷ = A'·F + B'·G
   hold (from `Polynomial.exists_mul_add_mul_eq_C_resultant`), giving
   max(|F(X,Z)|,|G(X,Z)|) ≥ (|Δ²|/c)·max(|X|,|Z|)⁴ and gcd(F,G)∣Δ². The explicit constant
   C=2log|Δ|+log(2c₂) is hand-derived in A6_BUILD_SYNTHESIS.md "EXPLICIT lower-bound derivation".
   Prove as much of this as builds cleanly. If a sub-step needs a height API that doesn't exist
   yet, name it as a SINGLE clearly-labelled `sorry` seam (NOT an axiom) and report it — do not
   stop, push the algebra (the Bezout identities + gcd∣Δ²) which are pure ring facts.

## RULES
- NO axiom-escape. Named `sorry` seams only, clearly labelled.
- Standalone file; build only the new target directly on uisai2 with `lake build` (incremental;
  Mathlib is cached — do NOT trigger a full rebuild, do NOT touch core/built files).
- When green (or blocked on a named seam with the algebra landed), report: file path, what
  compiles, any named seam. (`#print axioms` not needed — prototype, unwired.)
- Unbounded grind on Mathlib API resolution. Only legitimate stop: the math is wrong, or the
  Mathlib resultant/height API genuinely does not exist.
