# A6 BUILD STEP 2 — close the projective height-lower seam

Repo ~/repos/flt-ai, branch ai-scratch. You are running ON uisai2 — build with the repo's
normal `lake build` / `lake env lean` directly here (incremental; Mathlib cached; do NOT
trigger a full rebuild, do NOT edit core/built files). NEVER a local mini build.

## Context (read these first)
- scratch/A6HeightProto.lean — the de-risk prototype, ALREADY COMPILES (commit 7cfb060,
  0 axiom, 1 sorry). It proves: `resultant_dupNum_dupDen` (=Δ²), `resultant_dupNum_dupDen_ne_zero`,
  and `dup_bezout_affine` (affine Bezout certificate from Polynomial.exists_mul_add_mul_eq_C_resultant).
  The single remaining `sorry` is `dup_projective_height_lower_height_api_seam`.
- scratch/A6_BUILD_SYNTHESIS.md — section "EXPLICIT lower-bound derivation" has the full hand-worked
  argument (the math is DONE; this is formalization, not discovery). Constant C = 2 log|Δ| + log(2c₂).
- scratch/A6_R7_Base_Northcott_FULL.md — full Lean for the ℙ¹(ℚ) height chart (Option ℚ chart,
  Projectivization.logHeight_mk, Rat.logHeight₁_eq_log_max). Use its API facts.

## GOAL
EXTEND scratch/A6HeightProto.lean (do NOT start a new file; do NOT edit other files) to CLOSE
`dup_projective_height_lower_height_api_seam` to 0 sorries, keeping the whole file compiling.

The argument (already hand-derived, transcribe + formalize):
1. From `dup_bezout_affine` (the resultant=Δ² Bezout in the single variable), homogenize to BOTH
   chart identities:  Δ²·X⁷ = A(X,Z)·F + B(X,Z)·G  and  Δ²·Z⁷ = A'(X,Z)·F + B'(X,Z)·G,
   where F=dupNumH, G=dupDenH (homogeneous deg 4), A,B,A',B' homogeneous deg 3. (Homogenization of
   the affine Bezout via the degree bookkeeping — this is what covers the infinity chart [1:0].)
2. Bound: |coeffs of A,B,A',B'| ≤ c₂·max(|X|,|Z|)³, giving
   |Δ²|·max(|X|,|Z|)⁷ ≤ 2c₂·max(|X|,|Z|)³·max(|F|,|G|)  ⇒  max(|F|,|G|) ≥ (|Δ²|/2c₂)·max(|X|,|Z|)⁴.
3. gcd control: g := gcd(F(X,Z),G(X,Z)) ∣ Δ² (g divides both Δ²X⁷ and Δ²Z⁷ and gcd(X⁷,Z⁷)=1 for
   primitive (X,Z)). So the reduced projective height loses at most log|Δ²|.
4. Net: naiveLogHeightP1Q (F) (G) ≥ 4·naiveLogHeightP1Q X Z − (log 2c₂ + log|Δ²|). Set C0 accordingly.

## RULES (campaign-critical)
- NO axiom-escape. If a genuinely-missing Mathlib height lemma blocks a sub-step, isolate it as ONE
  NEW clearly-named `sorry` seam (NOT axiom, NOT `theorem := sorry` hiding) and REPORT it precisely —
  do not stop, push every algebraic/arithmetic sub-step (the homogenization + the integer inequality
  + gcd∣Δ² are pure ring/Int facts, fully closeable).
- If the whole seam closes: report "SEAM CLOSED, file 0 sorries" + run `lake env lean scratch/A6HeightProto.lean`
  and paste the exit code. If partial: report exactly which sub-lemmas are closed and what the residual
  named seam needs.
- Unbounded grind on Mathlib API resolution. Only legitimate stop: math is wrong, or the needed
  Mathlib height API genuinely does not exist (then name the seam and say which API is missing).
