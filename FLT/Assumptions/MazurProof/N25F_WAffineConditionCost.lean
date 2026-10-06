import FLT.Assumptions.MazurProof.N25F_WRegularSectionLift
import FLT.Assumptions.MazurProof.N25F_SectionFiniteness
import FLT.Assumptions.MazurProof.N25F_DedekindFactorDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Zero

/-! Actual affine vanishing conditions as an ideal-quotient linear map.
The cost retains every prime's residue-field degree. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors BigOperators
namespace MazurProof.N25F_WAffineConditionCost
open N25F_NonBoundaryPrincipalDivisor N25F_RiemannRochSpace N25F_SectionFiniteness
open N25F_WBasisPoleSections N25F_WRegularSectionLift N25F_DedekindOrderMembership
local notation "K" => FractionRing W

/-- The real affine conditions map, using recovered W elements and the actual ideal quotient. -/
def wSectionIdealQuotient25Two (n : ℕ) (I : Ideal W) :
    fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) →ₗ[ZMod 2] W ⧸ I :=
  (Ideal.Quotient.mkₐ (ZMod 2) I).toLinearMap.comp (wRegularSectionLiftLinearMap25Two n)

theorem wSectionIdealQuotient25Two_eq_zero_iff (n : ℕ) (I : Ideal W)
    (f : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) :
    wSectionIdealQuotient25Two n I f = 0 ↔ wRegularSectionLift25Two n f ∈ I := by
  change Ideal.Quotient.mk I (wRegularSectionLift25Two n f) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The actual kernel imposes exactly all affine ideal-order inequalities, with zero handled honestly. -/
theorem wSectionIdealQuotient25Two_eq_zero_iff_orders (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (f : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) :
    wSectionIdealQuotient25Two n I f = 0 ↔
      (f : K) = 0 ∨ ∀ v : WHeightOne,
        FractionalIdeal.count K v (I : FractionalIdeal W⁰ K) ≤
          FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ (f : K)) := by
  rw [wSectionIdealQuotient25Two_eq_zero_iff]
  have hmem : wRegularSectionLift25Two n f ∈ I ↔ (f : K) ∈ (I : FractionalIdeal W⁰ K) := by
    constructor
    · intro h
      exact (FractionalIdeal.mem_coeIdeal W⁰).mpr
        ⟨wRegularSectionLift25Two n f, h, algebraMap_wRegularSectionLift25Two n f⟩
    · intro h
      obtain ⟨a, ha, he⟩ := (FractionalIdeal.mem_coeIdeal W⁰).mp h
      have hEq : a = wRegularSectionLift25Two n f :=
        IsFractionRing.injective W K (he.trans (algebraMap_wRegularSectionLift25Two n f).symm)
      exact hEq ▸ ha
  rw [hmem]
  by_cases hf : (f : K) = 0
  · simp [hf]
  rw [or_iff_right hf]
  exact mem_fractionalIdeal_iff_count_le _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI) _ hf

private theorem wIdealQuotient_finite (I : Ideal W) (hI : I ≠ ⊥) :
    Module.Finite (ZMod 2) (W ⧸ I) := by
  apply (Module.finite_iff_krullDimLE_zero (ZMod 2) (W ⧸ I)).2
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  exact hP.1.1.isMaximal (ne_bot_of_le_ne_bot hI hP.1.2)

/-- Imposing the actual affine ideal costs at most the dimension of its real quotient algebra. -/
theorem finrank_basePole_le_kernel_add_ideal_quotient (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥) :
    Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (wSectionIdealQuotient25Two n I)) +
        Module.finrank (ZMod 2) (W ⧸ I) := by
  letI := wIdealQuotient_finite I hI
  have hdim := (wSectionIdealQuotient25Two n I).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (wSectionIdealQuotient25Two n I))
  omega

/-- The affine condition cost is the full residue-degree-weighted prime multiplicity sum. -/
theorem finrank_basePole_le_kernel_add_weighted_affine_cost (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥) :
    Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (wSectionIdealQuotient25Two n I)) +
        ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          (UniqueFactorizationMonoid.normalizedFactors I).count P *
            Module.finrank (ZMod 2) (W ⧸ P) := by
  letI := wIdealQuotient_finite I hI
  have h := finrank_basePole_le_kernel_add_ideal_quotient n I hI
  rwa [DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors (ZMod 2) I hI] at h

end MazurProof.N25F_WAffineConditionCost
