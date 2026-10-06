import FLT.Assumptions.MazurProof.N25F_DedekindOrderMembership
import FLT.Assumptions.MazurProof.N25F_WPolynomialWindow

/-! Recover the actual W-chart element of every section with poles only in nH. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_WRegularSectionLift
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
open N25F_RiemannRochSpace N25F_WBasisPoleSections N25F_DedekindOrderMembership
local notation "K" => FractionRing W

private theorem basePoleDivisor_nonBoundary (A : FullNonBoundaryAtom25Two) :
    basePoleDivisor25Two A.1 = 0 := by
  have hn (t : FullBoundaryTag25Two) : fullBoundaryAtomOfTag t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom t)
  simp [basePoleDivisor25Two, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

/-- Every genuine nH section has a unique actual W-chart representative. -/
theorem existsUnique_wChart_lift_of_mem_basePole_space (n : ℕ) (f : K)
    (hf : f ∈ fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) :
    ∃! a : W, algebraMap W K a = f := by
  apply existsUnique_algebraMap_eq_of_count_nonneg
  intro v
  rcases hf with rfl | ⟨hf, hb⟩
  · simp only [FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero, le_refl]
  let A := fullNonBoundaryAtomEquivHeightOne.symm v
  have h := hb A.1
  rw [Finsupp.smul_apply, smul_eq_mul, basePoleDivisor_nonBoundary A, mul_zero, zero_add,
    projectivePrincipalDivisor_apply_nonBoundary _ A, nonBoundaryPrincipalDivisor_apply] at h
  change 0 ≤ FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
    (FractionalIdeal.spanSingleton W⁰ f) at h
  simpa only [A, Equiv.apply_symm_apply] using h

/-- The uniquely recovered actual regular W-chart element. -/
def wRegularSectionLift25Two (n : ℕ)
    (f : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) : W :=
  Classical.choose (existsUnique_wChart_lift_of_mem_basePole_space n f.1 f.2)

@[simp]
theorem algebraMap_wRegularSectionLift25Two (n : ℕ)
    (f : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) :
    algebraMap W K (wRegularSectionLift25Two n f) = (f : K) :=
  (Classical.choose_spec (existsUnique_wChart_lift_of_mem_basePole_space n f.1 f.2)).1

private theorem wRegularSectionLift_zero (n : ℕ) : wRegularSectionLift25Two n 0 = 0 := by
  apply IsFractionRing.injective W K
  rw [algebraMap_wRegularSectionLift25Two, map_zero]
  rfl

private theorem wRegularSectionLift_add (n : ℕ)
    (f g : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) :
    wRegularSectionLift25Two n (f + g) = wRegularSectionLift25Two n f + wRegularSectionLift25Two n g := by
  apply IsFractionRing.injective W K
  simp only [map_add, algebraMap_wRegularSectionLift25Two, Submodule.coe_add]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have hc : a.val = 0 ∨ a.val = 1 := by omega
  rcases hc with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- Recovery of the actual affine representative is F2-linear. -/
def wRegularSectionLiftLinearMap25Two (n : ℕ) :
    fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) →ₗ[ZMod 2] W where
  toFun := wRegularSectionLift25Two n
  map_add' := wRegularSectionLift_add n
  map_smul' r f := by
    rcases zmod_two_cases r with rfl | rfl
    · simp only [zero_smul, wRegularSectionLift_zero, map_zero]
    · simp only [map_one, one_smul]

theorem wRegularSectionLiftLinearMap25Two_injective (n : ℕ) :
    Function.Injective (wRegularSectionLiftLinearMap25Two n) := by
  intro f g h
  apply Subtype.ext
  have he := congrArg (algebraMap W K) h
  change algebraMap W K (wRegularSectionLift25Two n f) =
    algebraMap W K (wRegularSectionLift25Two n g) at he
  simpa only [algebraMap_wRegularSectionLift25Two] using he

end MazurProof.N25F_WRegularSectionLift
