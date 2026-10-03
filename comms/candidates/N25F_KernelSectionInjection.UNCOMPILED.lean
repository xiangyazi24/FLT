import FLT.Assumptions.MazurProof.N25F_WAffineConditionCost
import FLT.Assumptions.MazurProof.N25F_TotalBoundaryCost
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! PRODUCTION-SHAPED CANDIDATE, NOT COMPILED.
This file uses only the actual W, actual projective divisor, genuine principal
orders, genuine section submodule, and published ideal quotient map.
The exact ideal-count hypothesis is produced by exists_shifted_affine_ideal.
The boundary/nonboundary equalities below are coefficient identities, not
assumed order inequalities or a replacement section model. -/
noncomputable section
open scoped nonZeroDivisors BigOperators
namespace MazurProof.N25F_KernelSectionInjection
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
open N25F_RiemannRochSpace N25F_WBasisPoleSections
open N25F_WAffineConditionCost N25F_SectionFiniteness N25F_TotalBoundaryCost
local notation "K" => FractionRing W

/-- Identity-on-functions membership bridge, including f=0 explicitly. -/
theorem kernel_mem_section (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (E F : ProjectiveDivisor25Two)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1)
    (hboundary : ∀ t : FullBoundaryTag25Two,
      F (fullBoundaryAtomOfTag t) =
        ((n : ℤ) • basePoleDivisor25Two) (fullBoundaryAtomOfTag t))
    (haffine : ∀ A : FullNonBoundaryAtom25Two, F A.1 = E A.1)
    (f : fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two))
    (hf : wSectionIdealQuotient25Two n I f = 0) :
    (f : K) ∈ fullRiemannRochSpace25Two F := by
  by_cases hz : (f : K) = 0
  · exact Or.inl hz
  have ho := (wSectionIdealQuotient25Two_eq_zero_iff_orders n I hI f).mp hf
  have orders := ho.resolve_left hz
  rcases f.property with hzero | ⟨hne, hb⟩
  · exact (hz hzero).elim
  refine Or.inr ⟨hne, ?_⟩
  intro A
  by_cases hA : IsFullBoundaryAtom A
  · obtain ⟨t, rfl⟩ := (isFullBoundaryAtom_iff_exists_fullBoundaryTag A).mp hA
    rw [hboundary t]
    exact hb (fullBoundaryAtomOfTag t)
  · let B : FullNonBoundaryAtom25Two := ⟨A, hA⟩
    have h := orders (fullNonBoundaryAtomEquivHeightOne B)
    rw [hcount B] at h
    change 0 ≤ F B.1 +
      projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (f : K) hne)) B.1
    rw [haffine B, projectivePrincipalDivisor_apply_nonBoundary _ B,
      nonBoundaryPrincipalDivisor_apply]
    change 0 ≤ E B.1 + FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne B)
      (FractionalIdeal.spanSingleton W⁰ (f : K))
    omega

/-- Fill precisely the three boundary deficits; affine coefficients stay fixed. -/
def boundaryFilledDivisor (n : ℕ) (E : ProjectiveDivisor25Two) : ProjectiveDivisor25Two :=
  E + Finsupp.single (fullBoundaryAtomOfTag .X) ((n : ℤ) - E (fullBoundaryAtomOfTag .X)) +
    Finsupp.single (fullBoundaryAtomOfTag .YZ) ((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)) +
    Finsupp.single (fullBoundaryAtomOfTag .Z) (2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z))

theorem boundaryFilledDivisor_boundary (n : ℕ) (E : ProjectiveDivisor25Two)
    (t : FullBoundaryTag25Two) :
    boundaryFilledDivisor n E (fullBoundaryAtomOfTag t) =
      ((n : ℤ) • basePoleDivisor25Two) (fullBoundaryAtomOfTag t) := by
  classical
  cases t <;> simp [boundaryFilledDivisor, basePoleDivisor25Two,
    fullBoundaryAtomOfTag_injective.eq_iff, Finsupp.smul_apply, smul_eq_mul] <;> omega

theorem boundaryFilledDivisor_nonBoundary (n : ℕ) (E : ProjectiveDivisor25Two)
    (A : FullNonBoundaryAtom25Two) : boundaryFilledDivisor n E A.1 = E A.1 := by
  classical
  have hn (t : FullBoundaryTag25Two) : fullBoundaryAtomOfTag t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom t)
  simp [boundaryFilledDivisor, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

/-- Actual identity-on-functions linear injection from the affine kernel. -/
def kernelSectionMap (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (E : ProjectiveDivisor25Two)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1) :
    LinearMap.ker (wSectionIdealQuotient25Two n I) →ₗ[ZMod 2]
      fullRiemannRochSpace25Two (boundaryFilledDivisor n E) where
  toFun f := ⟨f.1.1, kernel_mem_section n I hI E (boundaryFilledDivisor n E)
    hcount (boundaryFilledDivisor_boundary n E) (boundaryFilledDivisor_nonBoundary n E) f.1 f.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem kernelSectionMap_injective (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (E : ProjectiveDivisor25Two)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1) :
    Function.Injective (kernelSectionMap n I hI E hcount) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : fullRiemannRochSpace25Two (boundaryFilledDivisor n E) => (z : K)) h

theorem finrank_kernel_le_filled_section (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (E : ProjectiveDivisor25Two)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1) :
    Module.finrank (ZMod 2) (LinearMap.ker (wSectionIdealQuotient25Two n I)) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two (boundaryFilledDivisor n E)) :=
  LinearMap.finrank_le_finrank_of_injective (kernelSectionMap_injective n I hI E hcount)

/-- Domination turns the signed fill into the three natural boundary costs. -/
theorem boundaryFilledDivisor_eq_natural_deficits (n : ℕ) (E : ProjectiveDivisor25Two)
    (hdom : ∀ A, E A ≤ ((n : ℤ) • basePoleDivisor25Two) A) :
    boundaryFilledDivisor n E = E +
      (((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat : ℤ) •
        Finsupp.single (fullBoundaryAtomOfTag .X) 1 +
      (((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat : ℤ) •
        Finsupp.single (fullBoundaryAtomOfTag .YZ) 1 +
      ((2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat : ℤ) •
        Finsupp.single (fullBoundaryAtomOfTag .Z) 1 := by
  classical
  have hX := hdom (fullBoundaryAtomOfTag .X)
  have hY := hdom (fullBoundaryAtomOfTag .YZ)
  have hZ := hdom (fullBoundaryAtomOfTag .Z)
  simp [basePoleDivisor25Two, fullBoundaryAtomOfTag_injective.eq_iff,
    Finsupp.smul_apply, smul_eq_mul] at hX hY hZ
  have ha : 0 ≤ (n : ℤ) - E (fullBoundaryAtomOfTag .X) := by omega
  have hb : 0 ≤ (n : ℤ) - E (fullBoundaryAtomOfTag .YZ) := by omega
  have hc : 0 ≤ 2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z) := by omega
  simp [boundaryFilledDivisor, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
    Int.toNat_of_nonneg hc, Finsupp.smul_single, smul_eq_mul]

/-- Complete dimension assembly up to the genuine affine-degree reindexing.
Only injection is used; no kernel equality or surjectivity is asserted. -/
theorem finrank_basePole_le_section_add_cost (n : ℕ) (I : Ideal W) (hI : I ≠ ⊥)
    (E : ProjectiveDivisor25Two)
    (hcount : ∀ A : FullNonBoundaryAtom25Two,
      FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
        (I : FractionalIdeal W⁰ K) = -E A.1)
    (hdom : ∀ A, E A ≤ ((n : ℤ) • basePoleDivisor25Two) A) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) +
        (∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          (UniqueFactorizationMonoid.normalizedFactors I).count P *
            Module.finrank (ZMod 2) (W ⧸ P)) +
        ((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat +
        ((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat +
        (2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat := by
  let a := ((n : ℤ) - E (fullBoundaryAtomOfTag .X)).toNat
  let b := ((n : ℤ) - E (fullBoundaryAtomOfTag .YZ)).toNat
  let c := (2 * (n : ℤ) - E (fullBoundaryAtomOfTag .Z)).toNat
  have hfill := boundaryFilledDivisor_eq_natural_deficits n E hdom
  have hremove : boundaryFilledDivisor n E -
      (a : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .X) 1 -
      (b : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .YZ) 1 -
      (c : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .Z) 1 = E := by
    rw [hfill]
    dsimp [a, b, c]
    abel
  have haff := finrank_basePole_le_kernel_add_weighted_affine_cost n I hI
  have hinj := finrank_kernel_le_filled_section n I hI E hcount
  have hbound := finrank_le_sub_three_boundaries (boundaryFilledDivisor n E) a b c
  rw [hremove] at hbound
  change _ ≤ _ + _ + a + b + c
  omega

#print axioms kernel_mem_section
#print axioms kernelSectionMap_injective
#print axioms finrank_kernel_le_filled_section
#print axioms boundaryFilledDivisor_eq_natural_deficits
end MazurProof.N25F_KernelSectionInjection
