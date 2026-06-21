# A6 BUILD SYNTHESIS — 10-round design (R1–R8) consolidated, build-ready

**Status: design COMPLETE. Every piece has concrete Lean code or a named Mathlib lemma.**
This is the capstone of the 10-round ChatGPT adversarial design (Xiang's 大基建 rule).
Saved alongside the per-round roadmaps A6_R{2..8}_*.md in scratch/.

## The reframed target (key synthesis insight)

The repo uses `mordell_weil_fg` **only** through `rational_torsion_finite_alias`
(`torsion_set_finite_of_fg`) in `FLT/Assumptions/MazurProof/TorsionFinite.lean`.
It does **NOT** need full Mordell-Weil finite generation — it needs **torsion finiteness**.

The height argument (doubling lower bound + Northcott) proves **torsion finiteness DIRECTLY**,
without weak-Mordell-Weil descent. R8 (adversarial) confirmed: *"the chain is sound and does
not require canonical height or Mordell-Weil, provided R2/R3 are proved for a naive projective
x-height."*

→ **Discharge target: prove `rational_torsion_finite` directly from the height argument,
rewire the alias, DROP the `mordell_weil_fg` axiom entirely.** (2→1 custom axioms.)
More thorough AND more reusable than assuming full MW — meets Xiang's 彻底+可复用 criterion.

## The chain (6 pieces, all designed)

1. **EC projective duplication** (R5, full code in A6_R5_EC_Duplication_FULL.md):
   `xRep_two_nsmul_same_dup_affine : SameP1 ((2•P).xRep) ![dupNumH …, dupDenH …]`
   - `dupNumH W X Z = X⁴ − b₄X²Z² − 2b₆XZ³ − b₈Z⁴`
   - `dupDenH W X Z = 4X³Z + b₂X²Z² + 2b₄XZ³ + b₆Z⁴`
   - Proved by case split (0 / 2-torsion / tangent) with explicit `linear_combination`
     certificates against `W.Equation`. **SameP1 (projective) formulation handles the
     infinity chart [1:0] by construction** — answers R8's flagged "affine Z=1 misses ∞" worry.

2. **Resultant = Δ²** (R6, full code in A6_R6_Resultant_Bezout_FULL.md):
   `resultant_dupNum_dupDen : (dupNumPoly W).resultant (dupDenPoly W) 4 4 = W.Δ^2`
   - Universal `MvPolynomial (Fin 4) ℤ` symbolic resultant `rawRes` proved once by `native_decide`
     (explicit rawRes polynomial given), then specialize + reduce via `W.b_relation`
     (cofactor certificate `linear_combination 4 * rawResCofactor * hrel`).
   - `resultant_dupNum_dupDen_ne_zero` via `sq_ne_zero W.Δ_ne_zero` [W.IsElliptic].

3. **Bezout / bounded cancellation** (R6): Mathlib `Polynomial.exists_mul_add_mul_eq_C_resultant`
   → `R·X⁷`, `R·Z⁷` homogeneous identities → `gcd(dupNumH, dupDenH) ∣ Δ²` → cancellation bounded.
   This is the named Mathlib lemma R8 said the lower bound needs.

4. **Projective height LOWER bound** (R8's flagged RISKIEST piece — DE-RISK PROTOTYPE FIRST):
   `dup_projective_height_lower : xHeight (2•P) ≥ 4 • xHeight P − C`
   pure binary-form statement (NO elliptic points): for coprime quartic forms F,G with
   resultant R≠0, `logHeight [F(X,Z):G(X,Z)] ≥ 4·logHeight[X:Z] − C`.
   Ingredients now ALL in hand from (1)+(2)+(3). **Prototype this in isolation before the full build.**
   Also write helper `Northcott.comp_of_finite_fibers` (R3/R8 flagged; may not be in Mathlib; easy).

5. **Base ℙ¹(ℚ) Northcott** (R7, full code in A6_R7_Base_Northcott_FULL.md):
   finite sublevel sets via chart `ℙ¹(ℚ) ≃ Option ℚ` (none=[1:0], some q=[q:1]),
   using `Projectivization.logHeight_mk`, `Rat.logHeight₁_eq_log_max`, `Height.Northcott`.
   (Mathlib marks projective Northcott instance TODO — genuinely-new but routine chart layer.)

6. **Abstract finiteness lemma** (R4, A6_R4_AbstractLemma_ROADMAP.md):
   doubling lower bound (4) + bounded torsion height + base Northcott (5) →
   torsion points have bounded height → finitely many → `rational_torsion_finite`.
   A torsion P has 2ᵏP in a finite orbit ⇒ xHeight P bounded ⇒ Northcott ⇒ finite.

## Build order (de-risk first, per R8)

- **Step 0 (DE-RISK):** prototype piece (4) `dup_projective_height_lower` in isolation
  (pure binary-form, uses (2)+(3)). If it compiles, "the rest is bounded" (R8 verdict).
- Step 1: land (1) EC dup + (2) resultant=Δ² (both ~full code from R5/R6).
- Step 2: land (5) base Northcott chart (full code from R7).
- Step 3: assemble (6) abstract lemma → `rational_torsion_finite`.
- Step 4: rewire `rational_torsion_finite_alias`, drop `mordell_weil_fg` axiom,
  fresh-rebuild `#print axioms mazur_torsion_bound` → confirm 2→1.

## CPU discipline
uisai2 builds currently PAUSED for gamma sims (commit ddd9af7). Author files now (0 remote CPU);
run the single verifying `lake build` of the prototype when the gamma-sim load permits.
Do NOT spawn a parallel xhigh codex (load 12.4 + no-parallel-on-hard-problem rule + 06-21 contention lesson).

## EXPLICIT lower-bound derivation (hand-worked, de-risks R8's flagged piece 4)

Setup: P has x-coord [X:Z] ∈ ℙ¹(ℚ), primitive integer rep (gcd(X,Z)=1).
2P has x-coord [F(X,Z) : G(X,Z)], F=dupNumH, G=dupDenH, both homogeneous deg 4.
resultant(F,G)=Δ²≠0 ⇒ F,G coprime binary forms.

UPPER (easy): max(|F|,|G|) ≤ c₁·max(|X|,|Z|)⁴ ⇒ H(2P) ≤ 4 H(P) + log c₁.

LOWER (the riskiest piece, now explicit):
By `Polynomial.exists_mul_add_mul_eq_C_resultant` applied BOTH ways (homogenized to
both charts — this is what covers the infinity chart [1:0], answering R8):
  Δ²·X⁷ = A(X,Z)·F + B(X,Z)·G        (A,B homogeneous deg 3)
  Δ²·Z⁷ = A'(X,Z)·F + B'(X,Z)·G       (A',B' homogeneous deg 3)
Evaluate, bound coeffs by c₂·max(|X|,|Z|)³:
  |Δ²|·max(|X|,|Z|)⁷ ≤ 2c₂·max(|X|,|Z|)³·max(|F|,|G|)
  ⇒ max(|F|,|G|) ≥ (|Δ²|/2c₂)·max(|X|,|Z|)⁴.
Cancellation control: g := gcd(F(X,Z),G(X,Z)) divides Δ² (from the same Bezout identities,
since g ∣ both LHS Δ²·X⁷ and Δ²·Z⁷ and gcd(X⁷,Z⁷)=1 ⇒ g ∣ Δ²). So reducing [F:G] to
primitive form divides out at most |Δ²|. Net:
  H(2P) = log(max(|F|,|G|)/g) ≥ 4 H(P) − log(2c₂) − log|Δ²|.

⇒ **C = 2·log|Δ| + log(2c₂)**, a constant depending only on W. ∎

This is the complete, explicit `dup_projective_height_lower` argument. The prototype lemma
(pure binary-form, no EC points) is exactly the two-Bezout-identity + gcd∣Δ² bound above.
Codex brief: build (2)+(3) first, then this lemma — if green, "rest is bounded" (R8).
