import FLT.Assumptions.MazurProof.N25F_KernelSectionInjection
import FLT.Assumptions.MazurProof.N25F_ShiftedAffineIdeal
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree
import FLT.Assumptions.MazurProof.N25F_ExactCountWeightedSum
import FLT.Assumptions.MazurProof.N25F_WPolynomialWindow
import FLT.Assumptions.MazurProof.DegreeReindex

/-! PRODUCTION-SHAPED CANDIDATE, UNCOMPILED actual-geometry import closure.
No new degree identity or geometric premise is assumed. DegreeReindex contains
only the separately checked finite-support lemma and arithmetic cancellation.
All projective divisors, ideals, residue fields, and section spaces below are
those of the actual characteristic-two N25 W-chart. -/
noncomputable section
open scoped nonZeroDivisors BigOperators
namespace MazurProof.N25F_CoarseLowerBound
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectiveDivisorDegree N25F_RiemannRochSpace
open N25F_WBasisPoleBound N25F_WBasisPoleSections N25F_WPolynomialWindow
open N25F_AffineNonpositiveRepresentative N25F_ShiftedAffineIdeal
open N25F_KernelSectionInjection N25F_ExactCountWeightedSum
local notation "K" => FractionRing W

/-- Explicitly align the two existing actual prime indexings. -/
def heightOneEquivMaximal : WHeightOne ≃ WChartMaximalIdeal :=
  fullNonBoundaryAtomEquivHeightOne.symm.trans fullNonBoundaryAtomEquivMaximalIdeal

@[simp] theorem heightOneEquivMaximal_val (v : WHeightOne) :
    (heightOneEquivMaximal v).1 = v.asIdeal := by
  change fullNonBoundaryPrimeIdeal (fullNonBoundaryAtomEquivHeightOne.symm v) = v.asIdeal
  simpa only [Equiv.apply_symm_apply] using
    (fullNonBoundaryAtomEquivHeightOne_asIdeal
      (fullNonBoundaryAtomEquivHeightOne.symm v)).symm

@[simp] theorem heightOneEquivMaximal_weight (v : WHeightOne) :
    wChartMaximalIdealDegree (heightOneEquivMaximal v) =
      Module.finrank (ZMod 2) (W ⧸ v.asIdeal) := by
  change Module.finrank (ZMod 2) (W ⧸ (heightOneEquivMaximal v).1) = _
  rw [heightOneEquivMaximal_val]

private theorem partition_symm_boundary (t : FullBoundaryTag25Two) :
    fullAtomEquivBoundaryNonBoundary.symm (Sum.inl t) = fullBoundaryAtomOfTag t := by
  apply fullAtomEquivBoundaryNonBoundary.injective
  simp only [Equiv.apply_symm_apply, fullAtomEquivBoundaryNonBoundary_boundary]

private theorem partition_symm_nonBoundary (A : FullNonBoundaryAtom25Two) :
    fullAtomEquivBoundaryNonBoundary.symm (Sum.inr A) = A.1 := by
  apply fullAtomEquivBoundaryNonBoundary.injective
  simp only [Equiv.apply_symm_apply, fullAtomEquivBoundaryNonBoundary_nonBoundary]

/-- Coefficients of the existing split are the original coefficients. -/
theorem split_boundary_coefficients (E : ProjectiveDivisor25Two) :
    (fullDivisorEquivBoundaryCoefficientsChart E).1 =
      (E (fullBoundaryAtomOfTag .X),
        (E (fullBoundaryAtomOfTag .YZ), E (fullBoundaryAtomOfTag .Z))) := by
  change (E (fullAtomEquivBoundaryNonBoundary.symm (Sum.inl .X)),
    (E (fullAtomEquivBoundaryNonBoundary.symm (Sum.inl .YZ)),
     E (fullAtomEquivBoundaryNonBoundary.symm (Sum.inl .Z)))) = _
  simp only [partition_symm_boundary]

theorem split_chart_coefficient (E : ProjectiveDivisor25Two) (m : WChartMaximalIdeal) :
    (fullDivisorEquivBoundaryCoefficientsChart E).2 m =
      E (fullNonBoundaryAtomEquivMaximalIdeal.symm m).1 := by
  change E (fullAtomEquivBoundaryNonBoundary.symm
    (Sum.inr (fullNonBoundaryAtomEquivMaximalIdeal.symm m))) = _
  rw [partition_symm_nonBoundary]

/-- The actual weighted ideal-factor cost from the existing affine inequality. -/
def affineCost (I : Ideal W) : ℕ :=
  ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
    (UniqueFactorizationMonoid.normalizedFactors I).count P *
      Module.finrank (ZMod 2) (W ⧸ P)

/-- Exact affine counts determine the genuine signed chart degree.
This is proved by prime-index transport and residue degrees, not a premise. -/
theorem affineCost_eq_neg_chart_degree (E : ProjectiveDivisor25Two)
    (I : Ideal W) (hI : I ≠ ⊥)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1) :
    (affineCost I : ℤ) =
      -wChartDivisorDegree (fullDivisorEquivBoundaryCoefficientsChart E).2 := by
  classical
  let C := (fullDivisorEquivBoundaryCoefficientsChart E).2
  let d : WHeightOne →₀ ℤ := -(Finsupp.domCongr heightOneEquivMaximal.symm C)
  have hd (v : WHeightOne) : d v = -C (heightOneEquivMaximal v) := by
    simp [d, Finsupp.domCongr]
  have hC (v : WHeightOne) :
      C (heightOneEquivMaximal v) = E (fullNonBoundaryAtomEquivHeightOne.symm v).1 := by
    simp [C, split_chart_coefficient, heightOneEquivMaximal]
  have hc (v : WHeightOne) :
      FractionalIdeal.count K v (I : FractionalIdeal W⁰ K) = d v := by
    rw [hd, hC]
    simpa only [Equiv.apply_symm_apply] using
      hcount (fullNonBoundaryAtomEquivHeightOne.symm v)
  have hreindex := weighted_sum_eq_of_exact_counts I hI d hc
    (fun P => (Module.finrank (ZMod 2) (W ⧸ P) : ℤ))
  have hsum := DegreeReindex.sum_neg_reindex heightOneEquivMaximal d C hd
    (fun m => (wChartMaximalIdealDegree m : ℤ))
  simp only [heightOneEquivMaximal_weight] at hsum
  rw [hreindex] at hsum
  simpa only [affineCost, Nat.cast_sum, Nat.cast_mul,
    wChartDivisorDegree_apply, C] using hsum

/-- Full projective degree after the actual affine-count identification. -/
theorem degree_eq_boundary_sub_affineCost (E : ProjectiveDivisor25Two)
    (I : Ideal W) (hI : I ≠ ⊥)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1) :
    fullClosedPointGrading25Two.divisorDegree E =
      E (fullBoundaryAtomOfTag .X) + E (fullBoundaryAtomOfTag .YZ) +
        E (fullBoundaryAtomOfTag .Z) - (affineCost I : ℤ) := by
  have hc := affineCost_eq_neg_chart_degree E I hI hcount
  have hs := divisorDegree_eq_boundary_add_chart E
  rw [split_boundary_coefficients, boundaryCoefficientDegree_apply] at hs
  dsimp only at hs
  omega

/-- The three genuine natural boundary deficits plus affine cost equal
exactly deg(nH-E). The coefficient of Z in H is TWO. -/
theorem affine_and_boundary_cost (E : ProjectiveDivisor25Two) (n : ℕ)
    (I : Ideal W) (hI : I ≠ ⊥)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1)
    (hdom : ∀ A, E A ≤ ((n : ℤ) • basePoleDivisor25Two) A) :
    (affineCost I : ℤ) + ((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat +
      ((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat +
      (2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat =
      4 * (n : ℤ) - fullClosedPointGrading25Two.divisorDegree E := by
  have hX := hdom (fullBoundaryAtomOfTag .X)
  have hY := hdom (fullBoundaryAtomOfTag .YZ)
  have hZ := hdom (fullBoundaryAtomOfTag .Z)
  simp [basePoleDivisor25Two, fullBoundaryAtomOfTag_injective.eq_iff,
    Finsupp.smul_apply, smul_eq_mul] at hX hY hZ
  have hdeg := degree_eq_boundary_sub_affineCost E I hI hcount
  omega

/-- The effective boundary divisor used by the three-boundary cost theorem. -/
def boundaryDeficitDivisor (E : ProjectiveDivisor25Two) (n : ℕ) : ProjectiveDivisor25Two :=
  (((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat : ℤ) •
      Finsupp.single (fullBoundaryAtomOfTag .X) 1 +
    (((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat : ℤ) •
      Finsupp.single (fullBoundaryAtomOfTag .YZ) 1 +
    ((2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat : ℤ) •
      Finsupp.single (fullBoundaryAtomOfTag .Z) 1

/-- All three boundary residue degrees are the existing source-derived one. -/
theorem boundaryDeficitDivisor_degree (E : ProjectiveDivisor25Two) (n : ℕ) :
    fullClosedPointGrading25Two.divisorDegree (boundaryDeficitDivisor E n) =
      (((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat : ℤ) +
        ((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat +
        (2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat := by
  simp [boundaryDeficitDivisor, map_add, map_zsmul,
    CurveZetaEffectiveDivisors.ClosedPointGrading.divisorDegree,
    fullBoundaryAtomOfTag_degree]

/-- Requested geometric cost identity for the actual shifted representative. -/
theorem shifted_affineCost_add_boundary_degree (D : ProjectiveDivisor25Two) (n : ℕ)
    (I : Ideal W) (hI : I ≠ ⊥)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -affineNonpositiveRepresentative25Two D A.1)
    (hdom : ∀ A, affineNonpositiveRepresentative25Two D A ≤
      ((n : ℤ) • basePoleDivisor25Two) A) :
    (affineCost I : ℤ) + fullClosedPointGrading25Two.divisorDegree
        (boundaryDeficitDivisor (affineNonpositiveRepresentative25Two D) n) =
      4 * (n : ℤ) - fullClosedPointGrading25Two.divisorDegree D := by
  rw [boundaryDeficitDivisor_degree]
  have h := affine_and_boundary_cost (affineNonpositiveRepresentative25Two D)
    n I hI hcount hdom
  rw [affineNonpositiveRepresentative25Two_degree] at h
  omega

/-- Unconditional coarse lower bound on the actual full Riemann--Roch space.
The only remaining qualification is verification status of production imports. -/
theorem degree_le_finrank_add_four_basis_bound (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.divisorDegree D ≤
      (Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) : ℤ) +
        4 * (wPolynomialBasisPoleBound25Two : ℤ) := by
  let E := affineNonpositiveRepresentative25Two D
  obtain ⟨n, hn, hdom⟩ := affineNonpositiveRepresentative25Two_le_basePole_multiple D
  obtain ⟨I, hI, hcount, _⟩ := exists_shifted_affine_ideal D
  have hdim := finrank_basePole_le_section_add_cost n I hI E hcount hdom
  have hbase := four_mul_le_finrank_basePole_add_constant n
  have hcost := affine_and_boundary_cost E n I hI hcount hdom
  have hdegree : fullClosedPointGrading25Two.divisorDegree E =
      fullClosedPointGrading25Two.divisorDegree D :=
    affineNonpositiveRepresentative25Two_degree D
  have hrank : Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) :=
    affineNonpositiveRepresentative25Two_finrank D
  change _ ≤ _ + affineCost I + _ + _ + _ at hdim
  rw [hdegree] at hcost
  rw [hrank] at hdim
  omega

#print axioms affineCost_eq_neg_chart_degree
#print axioms degree_eq_boundary_sub_affineCost
#print axioms affine_and_boundary_cost
#print axioms degree_le_finrank_add_four_basis_bound
end MazurProof.N25F_CoarseLowerBound
