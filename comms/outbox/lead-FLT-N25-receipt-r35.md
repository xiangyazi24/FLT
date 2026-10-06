# Receipt r35 (lead → dot), FLT N25

## Verdict
- **Delivered bytes: BLOCKED.** 43 files @bebaf732e8 + N25F_HighDegreeEffective @171b88d2e4 do not compile as delivered.
  First error: `N25F_ProjectiveProductFormula.lean:66:2: omega could not prove the goal`.
- **Integrated WITH FIX** as `xiang/verify-sorry-restore@696f10fa8a` (parent 51bbb4f191). All 44 modules: `lake build` OK (Lean v4.31.0-rc2, 8748 jobs).
- Axiom sweep over all 450 declarations in the 44 modules: standard axioms only (propext, Classical.choice, Quot.sound); no sorryAx, no new axioms.
- Endpoints checked by `#print axioms`, all standard:
  - HighDegreeEffective: finrank_pos_ / nonzeroSection_nonempty_ / riemannRochSpace_ne_bot_ / exists_effective_representative_of_degree_gt_four_basis_bound.
  - CoarseLowerBound.degree_le_finrank_add_four_basis_bound.
  - ShiftedAffineIdeal.exists_shifted_affine_ideal.
  - KernelSectionInjection: kernelSectionMap_injective, finrank_kernel_le_filled_section, finrank_basePole_le_section_add_cost.

## Lead fixes (no statement changed)
1. Ambiguous `W`: `N25F_NonBoundaryPrincipalDivisor` and `RationalPointsN25QuotientTwoWOpenPrimeSurjective` both define `abbrev W`. Fixed with `open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W` in 8 files.
2. Missing opens: `RationalPointsN25QuotientTwoClosedPointPartition` in ZeroDegreeConstants, TotalBoundaryCost and BoundarySectionFiltration; `RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective` in CoarseLowerBound.
3. `(K := K)` does not parse when `K` is local notation. Replaced with an explicit `@f W K _ _ _ _ _ args` in AffineNonpositiveRepresentative:31 and ShiftedAffineIdeal:35.
4. ProjectiveProductFormula:66: `omega` → `exact neg_add_cancel _`.
5. HighDegreeEffective: trailing blank line removed (git diff --check).

The full diff (delivered → integrated) follows.

## Next
- Work from 696f10fa8a: take these bytes as the base for anything that imports the 44 modules.
- Habits that would have caught all of the above: never open two namespaces that both export `W`; check every identifier's namespace is opened; avoid named-argument syntax for notation variables; prefer a term proof over `omega` on ℤ group identities.
- Continue with the next N25 step on top of the high-degree effective representative.

```diff
--- FLT/Assumptions/MazurProof/N25F_AffineNonpositiveRepresentative.lean	2026-10-06 10:31:58.080295220 -0500
+++ FLT/Assumptions/MazurProof/N25F_AffineNonpositiveRepresentative.lean	2026-10-06 10:54:42.952457769 -0500
@@ -12,7 +12,7 @@
 open CurveZetaEffectiveDivisors RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
 open N25F_ProjectiveProductFormula N25F_FullPicardDegree N25F_SectionPrincipalTransport
@@ -28,7 +28,7 @@
 theorem exists_principal_affine_majorant25Two (D : ProjectiveDivisor25Two) :
     ∃ f : Additive Kˣ, ∀ A : FullNonBoundaryAtom25Two,
       D A.1 ≤ projectivePrincipalDivisor f A.1 := by
-  obtain ⟨a, ha, hcount⟩ := exists_nonzero_regular_with_count_ge (K := K) (affineHeightOnePart D)
+  obtain ⟨a, ha, hcount⟩ := @exists_nonzero_regular_with_count_ge W K _ _ _ _ _ (affineHeightOnePart D)
   have hmap : algebraMap W K a ≠ 0 :=
     (map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr ha
   let f : Additive Kˣ := Additive.ofMul (Units.mk0 (algebraMap W K a) hmap)
--- FLT/Assumptions/MazurProof/N25F_BasePolePowers.lean	2026-10-06 10:31:58.149295641 -0500
+++ FLT/Assumptions/MazurProof/N25F_BasePolePowers.lean	2026-10-06 10:53:06.078788005 -0500
@@ -8,7 +8,7 @@
 set_option relaxedAutoImplicit false
 noncomputable section
 namespace MazurProof.N25F_BasePolePowers
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_RiemannRochSpace N25F_WBasisPoleSections N25F_SectionMultiplication
 open N25F_XBoundaryOrder N25F_XBoundaryZOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
--- FLT/Assumptions/MazurProof/N25F_BoundarySectionFiltration.lean	2026-10-06 10:31:58.283296458 -0500
+++ FLT/Assumptions/MazurProof/N25F_BoundarySectionFiltration.lean	2026-10-06 10:53:06.079788013 -0500
@@ -19,6 +19,7 @@
 open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
 open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
 open N25F_InfinityResidueFields N25F_BinaryResidueCancellation
+open RationalPointsN25QuotientTwoClosedPointPartition
 local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
 
 /-- Equal-order leading terms cancel at each of the three actual binary residue fields. -/
--- FLT/Assumptions/MazurProof/N25F_CoarseLowerBound.lean	2026-10-06 10:31:57.660292658 -0500
+++ FLT/Assumptions/MazurProof/N25F_CoarseLowerBound.lean	2026-10-06 10:56:03.505014693 -0500
@@ -16,12 +16,13 @@
 open RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectiveDivisorDegree N25F_RiemannRochSpace
 open N25F_WBasisPoleBound N25F_WBasisPoleSections N25F_WPolynomialWindow
 open N25F_AffineNonpositiveRepresentative N25F_ShiftedAffineIdeal
 open N25F_KernelSectionInjection N25F_ExactCountWeightedSum
+open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
 local notation "K" => FractionRing W
 
 /-- Explicitly align the two existing actual prime indexings. -/
--- FLT/Assumptions/MazurProof/N25F_KernelSectionInjection.lean	2026-10-06 10:31:57.732293097 -0500
+++ FLT/Assumptions/MazurProof/N25F_KernelSectionInjection.lean	2026-10-06 10:53:06.076787992 -0500
@@ -15,7 +15,7 @@
 open RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
 open N25F_RiemannRochSpace N25F_WBasisPoleSections
--- FLT/Assumptions/MazurProof/N25F_ProjectiveProductFormula.lean	2026-10-06 10:31:58.216296050 -0500
+++ FLT/Assumptions/MazurProof/N25F_ProjectiveProductFormula.lean	2026-10-06 10:47:15.868398785 -0500
@@ -63,7 +63,7 @@
   have haff := wChart_principal_degree_eq_quotient_finrank a ha f hf
   rw [wChart_quotient_finrank_eq_natDegree_norm a ha] at haff
   rw [projectivePrincipalDivisor_degree, ← hsum, haff]
-  omega
+  exact neg_add_cancel _
 
 /-- The actual projective principal divisor of every nonzero function has
 degree zero. The fraction representation extends the regular-function case. -/
--- FLT/Assumptions/MazurProof/N25F_ShiftedAffineIdeal.lean	2026-10-06 10:31:57.768293317 -0500
+++ FLT/Assumptions/MazurProof/N25F_ShiftedAffineIdeal.lean	2026-10-06 10:55:22.196729096 -0500
@@ -7,7 +7,7 @@
 namespace MazurProof.N25F_ShiftedAffineIdeal
 open RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_AffineNonpositiveRepresentative N25F_EffectiveAffineIdeal
 local notation "K" => FractionRing W
@@ -32,7 +32,7 @@
     intro v
     exact affineNonpositiveRepresentative25Two_nonBoundary D
       (fullNonBoundaryAtomEquivHeightOne.symm v)
-  obtain ⟨I, hI, hc, hm⟩ := exists_ideal_for_nonpositive_divisor (K := K) (affinePart E) hd
+  obtain ⟨I, hI, hc, hm⟩ := @exists_ideal_for_nonpositive_divisor W K _ _ _ _ _ (affinePart E) hd
   refine ⟨I, hI, ?_, ?_⟩
   · intro A
     simpa only [affinePart, Finsupp.comapDomain_apply, Equiv.symm_apply_apply] using
--- FLT/Assumptions/MazurProof/N25F_TotalBoundaryCost.lean	2026-10-06 10:31:58.011294799 -0500
+++ FLT/Assumptions/MazurProof/N25F_TotalBoundaryCost.lean	2026-10-06 10:53:06.077787999 -0500
@@ -5,6 +5,7 @@
 namespace MazurProof.N25F_TotalBoundaryCost
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_BoundarySectionFiltration
+open RationalPointsN25QuotientTwoClosedPointPartition
 
 /-- Sequentially impose all three actual boundary multiplicities. -/
 theorem finrank_le_sub_three_boundaries (D : ProjectiveDivisor25Two) (a b c : ℕ) :
--- FLT/Assumptions/MazurProof/N25F_WBasisPoleSections.lean	2026-10-06 10:31:58.424297319 -0500
+++ FLT/Assumptions/MazurProof/N25F_WBasisPoleSections.lean	2026-10-06 10:51:43.914226593 -0500
@@ -13,7 +13,7 @@
 open RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
 open N25F_ProjectiveDivisorDegree N25F_RiemannRochSpace N25F_WBasisPoleBound
--- FLT/Assumptions/MazurProof/N25F_WPolynomialWindow.lean	2026-10-06 10:31:57.837293738 -0500
+++ FLT/Assumptions/MazurProof/N25F_WPolynomialWindow.lean	2026-10-06 10:53:06.077787999 -0500
@@ -9,7 +9,7 @@
 set_option relaxedAutoImplicit false
 noncomputable section
 namespace MazurProof.N25F_WPolynomialWindow
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectivePrincipalDivisor N25F_RiemannRochSpace N25F_SectionFiniteness
 open N25F_WBasisPoleBound N25F_WBasisPoleSections N25F_BasePolePowers
--- FLT/Assumptions/MazurProof/N25F_WRegularSectionLift.lean	2026-10-06 10:31:58.250296257 -0500
+++ FLT/Assumptions/MazurProof/N25F_WRegularSectionLift.lean	2026-10-06 10:53:06.078788005 -0500
@@ -11,7 +11,7 @@
 open RationalPointsN25QuotientTwoFullClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoClosedPointPartition
-open RationalPointsN25QuotientTwoWOpenPrimeSurjective
+open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
 open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
 open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
 open N25F_RiemannRochSpace N25F_WBasisPoleSections N25F_DedekindOrderMembership
--- FLT/Assumptions/MazurProof/N25F_ZeroDegreeConstants.lean	2026-10-06 10:31:58.183295848 -0500
+++ FLT/Assumptions/MazurProof/N25F_ZeroDegreeConstants.lean	2026-10-06 10:51:43.915226600 -0500
@@ -13,7 +13,7 @@
 noncomputable section
 namespace MazurProof.N25F_ZeroDegreeConstants
 open CurveZetaEffectiveDivisors
-open RationalPointsN25QuotientTwoFullClosedPoints
+open RationalPointsN25QuotientTwoFullClosedPoints RationalPointsN25QuotientTwoClosedPointPartition
 open RationalPointsN25QuotientTwoWBoundaryClosedPoints
 open RationalPointsN25QuotientTwoWBoundaryXLocal
 open N25F_ProjectiveDivisorSplit N25F_ProjectiveDivisorDegree N25F_ProjectivePrincipalDivisor
```
