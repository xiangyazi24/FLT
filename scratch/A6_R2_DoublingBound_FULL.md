# A6-height R2: doubling lower bound — COMPLETE design (Xiang-pasted real R2, authoritative)

## KEY: Mathlib has NO general degree-height theorem (Height.Basic TODO explicitly marks it missing).
Build the doubling bound DIRECTLY for the duplication map, via the RESULTANT. PROJECTIVE formulation
(so 2P=0 ↦ ![1,0] is fine, not an affine-∞ exception):
  ∃ C, ∀ P, logHeight(xRep(2•P)) ≥ 4·logHeight(xRep P) − C

## The homogeneous duplication forms (x(2P)=(x⁴−b₄x²−2b₆x−b₈)/(4x³+b₂x²+2b₄x+b₆)):
dupNumH W X Z := X⁴ − b₄ X²Z² − 2b₆ XZ³ − b₈ Z⁴
dupDenH W X Z := 4X³Z + b₂ X²Z² + 2b₄ XZ³ + b₆ Z⁴

## THE CORE INSIGHT (makes it buildable):
theorem resultant_dupNum_dupDen : (dupNumPoly W).resultant (dupDenPoly W) = W.Δ ^ 2
  — proof: ring_nf [dupNum/DenPoly, Δ, b₂,b₄,b₆,b₈] + W.b_relation (4b₈=b₂b₆−b₄²).
  → resultant ≠ 0 from [W.IsElliptic] (Δ≠0). So num/den are COPRIME → Bezout.

## Lemma chain (the build):
1. xRep_two_nsmul_same_dup: SameP1 (2•P).xRep ![dupNumH, dupDenH] — EC formula grind
   (Point.add_self_of_Y_eq/ne, addX, slope, negY, curve eqn). Bounded.
2. resultant_dupNum_dupDen = Δ² (ring + b_relation), ≠0 from IsElliptic.
3. dup_bezout_XY: from exists_mul_add_mul_eq_C_resultant → R·X⁷ = A·dupNum + B·dupDen and R·Z⁷ = ...
   (exponent 7 = 2d−1, d=4). Homogenize + clear denominators (integer forms dupNumHZ/dupDenHZ, scalar M).
4. dup_integer_eval_lower: |R|H⁷ ≤ C₀H³·MFG → MFG ≥ C₁H⁴ (H=max|X||Z|, nlinarith).
5. gcd_dup_eval_dvd_resultant: gcd(F,G) ∣ R (Bezout + coprime X,Z) → cancellation bounded.
6. dup_naiveHeightP1_lower → dup_height_lower_projective (primitive int rep + scaling invariance
   Height.logHeight_smul_eq_logHeight) → xRep_two_height_lower.

## Torsion finiteness from the bound (AIRTIGHT, projective, NO canonical height):
torsion_xheight_bounded_of_doubling_lower: torsion P → finite doubling orbit {2^k•P} → max-height Q →
  hX(2Q)≤hX(Q) (Q in orbit) + lower bound 4hX(Q)−C → hX(Q)≤C/3 → hX(P)≤C/3 (nlinarith).
torsion_finite_of_doubling_lower: torsion ⊆ {hX≤C/3}, finite via finite_points_with_xheight_le
  (= finite_rat_of_logHeight_le [Rat.num/den enum] + ≤2 y per x).

## VERDICT: CLOSEABLE but nontrivial. Hard parts: (1) xRep_two_nsmul_same_dup formula grind,
## (2) resultant=Δ² ring, (3) dup_bezout via exists_mul_add_mul_eq_C_resultant, (4) integer estimates,
## (5) finite_rat_of_logHeight_le. MUCH smaller than canonical heights; avoids the missing general
## height functoriality. → A6 mordell_weil_fg dependency is DISCHARGEABLE via this height route.
