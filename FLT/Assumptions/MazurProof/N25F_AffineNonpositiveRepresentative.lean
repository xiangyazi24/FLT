import FLT.Assumptions.MazurProof.N25F_DedekindPrincipalMajorant
import FLT.Assumptions.MazurProof.N25F_WPolynomialWindow
import FLT.Assumptions.MazurProof.N25F_FullPicardSectionRank

/-! Every actual full divisor has a linearly equivalent, same-degree
representative with nonpositive affine coefficients, dominated by a multiple of H. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_AffineNonpositiveRepresentative
open CurveZetaEffectiveDivisors RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
open N25F_ProjectiveProductFormula N25F_FullPicardDegree N25F_SectionPrincipalTransport
open N25F_RiemannRochSpace N25F_WBasisPoleBound N25F_WBasisPoleSections N25F_BasePolePowers
open N25F_DedekindPrincipalMajorant
local notation "K" => FractionRing W

private def affineHeightOnePart (D : ProjectiveDivisor25Two) : WHeightOne →₀ ℤ :=
  Finsupp.comapDomain (fun v => (fullNonBoundaryAtomEquivHeightOne.symm v).1) D
    (Subtype.coe_injective.comp fullNonBoundaryAtomEquivHeightOne.symm.injective).injOn

/-- A real nonzero function dominates every affine coefficient of the given full divisor. -/
theorem exists_principal_affine_majorant25Two (D : ProjectiveDivisor25Two) :
    ∃ f : Additive Kˣ, ∀ A : FullNonBoundaryAtom25Two,
      D A.1 ≤ projectivePrincipalDivisor f A.1 := by
  obtain ⟨a, ha, hcount⟩ := @exists_nonzero_regular_with_count_ge W K _ _ _ _ _ (affineHeightOnePart D)
  have hmap : algebraMap W K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr ha
  let f : Additive Kˣ := Additive.ofMul (Units.mk0 (algebraMap W K a) hmap)
  refine ⟨f, ?_⟩
  intro A
  rw [projectivePrincipalDivisor_apply_nonBoundary f A, nonBoundaryPrincipalDivisor_apply]
  have h := hcount (fullNonBoundaryAtomEquivHeightOne A)
  change (affineHeightOnePart D) (fullNonBoundaryAtomEquivHeightOne A) ≤
    CurveDedekindDivisor.principalDivisor f (fullNonBoundaryAtomEquivHeightOne A) at h
  simpa only [affineHeightOnePart, Finsupp.comapDomain_apply, Equiv.symm_apply_apply] using h

private def affinePrincipalShift (D : ProjectiveDivisor25Two) : Additive Kˣ :=
  Classical.choose (exists_principal_affine_majorant25Two D)

/-- The actual representative obtained by subtracting the constructed principal divisor. -/
def affineNonpositiveRepresentative25Two (D : ProjectiveDivisor25Two) : ProjectiveDivisor25Two :=
  D - projectivePrincipalDivisor (affinePrincipalShift D)

theorem affineNonpositiveRepresentative25Two_nonBoundary (D : ProjectiveDivisor25Two)
    (A : FullNonBoundaryAtom25Two) : affineNonpositiveRepresentative25Two D A.1 ≤ 0 := by
  exact sub_nonpos.mpr ((Classical.choose_spec (exists_principal_affine_majorant25Two D)) A)

/-- The genuine projective product formula preserves the full weighted degree. -/
theorem affineNonpositiveRepresentative25Two_degree (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.divisorDegree (affineNonpositiveRepresentative25Two D) =
      fullClosedPointGrading25Two.divisorDegree D := by
  rw [affineNonpositiveRepresentative25Two, map_sub, projectivePrincipalDivisor_degree_eq_zero, sub_zero]

theorem affineNonpositiveRepresentative25Two_classOf (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
      (affineNonpositiveRepresentative25Two D) =
    fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D := by
  have hz : fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
      (projectivePrincipalDivisor (affinePrincipalShift D)) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨affinePrincipalShift D, rfl⟩
  rw [affineNonpositiveRepresentative25Two, map_sub, hz, sub_zero]

theorem affineNonpositiveRepresentative25Two_finrank (D : ProjectiveDivisor25Two) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two (affineNonpositiveRepresentative25Two D)) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) :=
  finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq _ _
    (affineNonpositiveRepresentative25Two_classOf D)

/-- After the genuine principal shift, a multiple of H really dominates every coefficient. -/
theorem affineNonpositiveRepresentative25Two_le_basePole_multiple (D : ProjectiveDivisor25Two) :
    ∃ n : ℕ, wPolynomialBasisPoleBound25Two ≤ n ∧
      ∀ A, affineNonpositiveRepresentative25Two D A ≤ ((n : ℤ) • basePoleDivisor25Two) A := by
  classical
  let E := affineNonpositiveRepresentative25Two D
  let n := wPolynomialBasisPoleBound25Two + (E (fullBoundaryAtomOfTag .X)).toNat +
    (E (fullBoundaryAtomOfTag .YZ)).toNat + (E (fullBoundaryAtomOfTag .Z)).toNat
  refine ⟨n, by omega, ?_⟩
  intro A
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : IsFullBoundaryAtom A
  · obtain ⟨t, rfl⟩ := (isFullBoundaryAtom_iff_exists_fullBoundaryTag A).mp hA
    change E (fullBoundaryAtomOfTag t) ≤ (n : ℤ) * basePoleDivisor25Two (fullBoundaryAtomOfTag t)
    cases t <;> simp only [basePoleDivisor25Two, Finsupp.add_apply, Finsupp.single_apply,
      fullBoundaryAtomOfTag_injective.eq_iff] <;> simp only [reduceCtorEq, ↓reduceIte, add_zero,
      zero_add, mul_one] <;> omega
  · have hnon := affineNonpositiveRepresentative25Two_nonBoundary D ⟨A, hA⟩
    have hpos : 0 ≤ basePoleDivisor25Two A := by
      have h := basePoleDivisor25Two_nonneg
      change ∀ a, 0 ≤ basePoleDivisor25Two a at h
      exact h A
    exact hnon.trans (mul_nonneg (Int.natCast_nonneg n) hpos)

/-- Exact degree cost of imposing the effective complement after the shift. -/
theorem affineRepresentative_complement_degree (D : ProjectiveDivisor25Two) (n : ℕ) :
    fullClosedPointGrading25Two.divisorDegree
      ((n : ℤ) • basePoleDivisor25Two - affineNonpositiveRepresentative25Two D) =
      4 * (n : ℤ) - fullClosedPointGrading25Two.divisorDegree D := by
  rw [map_sub, map_zsmul, basePoleDivisor25Two_degree, affineNonpositiveRepresentative25Two_degree]
  simp only [zsmul_eq_mul, Int.cast_id, mul_comm]

end MazurProof.N25F_AffineNonpositiveRepresentative
