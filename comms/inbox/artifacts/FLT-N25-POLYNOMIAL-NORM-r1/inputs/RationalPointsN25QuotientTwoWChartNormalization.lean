import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneNormalization
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCanonicalDifferentials
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Jacobson.Ring

/-!
# The canonical W-chart inside the plane function field

The canonical affine `w = 1` chart is finite and integral over both the
plane coordinate ring and the polynomial ring `F₂[z]`.  Its localization
away from the projection denominator agrees with the corresponding principal
open of the plane curve.  Consequently the chart embeds in the plane function
field and has that field as its fraction field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWChartNormalization

open scoped TensorProduct
open Polynomial
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoPlaneChartLocalization
open RationalPointsN25QuotientTwoPlaneChartDomain
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoAffineCanonicalDifferentials
open RationalPointsN25QuotientTwoPlaneChartClosedPoints
open RationalPointsN25QuotientTwoPlaneNormalization

local notation "k₂" => ZMod 2
local notation "Rz" => Polynomial k₂
local notation "K" => FractionRing Rz
local notation "Fz" => RatFunc k₂
local notation "A" => PlaneCoordinateRing
local notation "W" => ChartQuotient 3
local notation "L" => PlaneFunctionField

instance planeAlgebraW : Algebra A W :=
  planeCoordinateRingToCanonicalWChart.toAlgebra

/-- The plane coordinate ring embeds in the canonical `w = 1` chart. -/
theorem planeCoordinateRingToCanonicalWChart_injective :
    Function.Injective planeCoordinateRingToCanonicalWChart := by
  letI : FaithfulSMul W CanonicalWChartDOpen :=
    (faithfulSMul_iff_algebraMap_injective W CanonicalWChartDOpen).2
      canonicalWChartToDOpen_injective
  intro a b hab
  apply IsLocalization.injective
    (M := Submonoid.powers planeProjectionDenominator)
    (S := PlaneDOpen)
  · exact powers_le_nonZeroDivisors_of_noZeroDivisors
      planeProjectionDenominator_ne_zero
  apply planeDOpenEquivCanonicalWChartDOpen.injective
  simpa [planeDOpenEquivCanonicalWChartDOpen_apply,
    planeDOpenToCanonicalWChartDOpen_algebraMap] using
      congrArg (algebraMap W CanonicalWChartDOpen) hab

instance planeFaithfulW : FaithfulSMul A W :=
  (faithfulSMul_iff_algebraMap_injective A W).2
    planeCoordinateRingToCanonicalWChart_injective

instance kPlaneW : IsScalarTower k₂ A W :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

theorem canonicalWChartY_eq_mk :
    canonicalWChartY =
      Ideal.Quotient.mk (chartAffineEquationIdeal 3)
        (MvPolynomial.X planeAffineY) := by
  simp [canonicalWChartY, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, planeAffineY]

/-- The monic quadratic equation for the remaining chart generator over the
plane coordinate ring. -/
def canonicalWChartYPolynomial : A[X] :=
  X ^ 2 +
    C RationalPointsN25QuotientTwoPlaneFunctionField.planeZ * X +
    C planeProjectionDenominator

/-- The chart-generator equation is monic. -/
theorem canonicalWChartYPolynomial_monic :
    canonicalWChartYPolynomial.Monic := by
  unfold canonicalWChartYPolynomial
  monicity!

/-- The canonical `y` coordinate satisfies its quadratic equation. -/
theorem canonicalWChartYPolynomial_aeval :
    aeval canonicalWChartY canonicalWChartYPolynomial = 0 := by
  simp only [canonicalWChartYPolynomial, map_add, map_mul, map_pow, aeval_X,
    aeval_C]
  change canonicalWChartY ^ 2 +
      planeCoordinateRingToCanonicalWChart
          RationalPointsN25QuotientTwoPlaneFunctionField.planeZ *
        canonicalWChartY +
        planeCoordinateRingToCanonicalWChart planeProjectionDenominator = 0
  rw [planeCoordinateRingToCanonicalWChart_planeZ,
    planeCoordinateRingToCanonicalWChart_denominator]
  have hq := chartQuotientPoint_quadric (pivot := (3 : Fin 4))
  have hq' :
      RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
          (wChartPoint canonicalWChartX canonicalWChartY canonicalWChartZ) = 0 := by
    rw [wChartPoint_eq_canonicalWChartPoint]
    exact hq
  rw [canonicalQuadric_wChart] at hq'
  rw [canonicalWChartProjectionDenominator]
  linear_combination hq'

/-- The canonical `y` coordinate is integral over the plane coordinate ring. -/
theorem canonicalWChartY_isIntegral : IsIntegral A canonicalWChartY :=
  ⟨canonicalWChartYPolynomial,
    canonicalWChartYPolynomial_monic,
    canonicalWChartYPolynomial_aeval⟩

/-- The canonical chart is generated over the plane coordinate ring by its
`y` coordinate. -/
theorem canonicalWChart_adjoin_y_eq_top :
    Algebra.adjoin A ({canonicalWChartY} : Set W) = ⊤ := by
  apply Algebra.eq_top_iff.2
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  let S : Subalgebra A W := Algebra.adjoin A ({canonicalWChartY} : Set W)
  change Ideal.Quotient.mk (chartAffineEquationIdeal 3) p ∈ S
  induction p using MvPolynomial.induction_on with
  | C c =>
      change algebraMap k₂ W c ∈ S
      rw [IsScalarTower.algebraMap_apply k₂ A W]
      exact S.algebraMap_mem _
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      apply S.mul_mem hp
      have hiCases : i = planeAffineX ∨
          i = planeAffineY ∨ i = planeAffineZ := by
        have hval : i.1.val = 0 ∨ i.1.val = 1 ∨ i.1.val = 2 := by
          have hlt := i.1.isLt
          have hne : i.1.val ≠ 3 := fun h => i.2 (Fin.ext h)
          omega
        rcases hval with h0 | h1 | h2
        · exact Or.inl (Subtype.ext (Fin.ext h0))
        · exact Or.inr (Or.inl (Subtype.ext (Fin.ext h1)))
        · exact Or.inr (Or.inr (Subtype.ext (Fin.ext h2)))
      rcases hiCases with rfl | rfl | rfl
      · rw [
          ← canonicalWChartX_eq_mk,
          ← planeCoordinateRingToCanonicalWChart_planeX]
        exact S.algebraMap_mem planeX
      · rw [← canonicalWChartY_eq_mk]
        exact Algebra.subset_adjoin (Set.mem_singleton canonicalWChartY)
      · rw [
          ← canonicalWChartZ_eq_mk,
          ← planeCoordinateRingToCanonicalWChart_planeZ]
        exact S.algebraMap_mem
          RationalPointsN25QuotientTwoPlaneFunctionField.planeZ

/-- The canonical chart is integral over the plane coordinate ring. -/
instance canonicalWChart_isIntegral : Algebra.IsIntegral A W := by
  rw [← integralClosure_eq_top_iff]
  apply le_antisymm le_top
  rw [← canonicalWChart_adjoin_y_eq_top]
  exact Algebra.adjoin_le fun y hy => by
    change IsIntegral A y
    simpa only [Set.mem_singleton_iff.mp hy] using canonicalWChartY_isIntegral

/-- The canonical chart is of finite type over the plane coordinate ring. -/
instance canonicalWChart_finiteType : Algebra.FiniteType A W := by
  refine ⟨{canonicalWChartY}, ?_⟩
  simpa using canonicalWChart_adjoin_y_eq_top

/-- The canonical chart is finite over the plane coordinate ring. -/
instance canonicalWChart_finite : Module.Finite A W :=
  Algebra.IsIntegral.finite

instance rzAlgebraW : Algebra Rz W :=
  ((algebraMap A W).comp (algebraMap Rz A)).toAlgebra

instance rzAW : IsScalarTower Rz A W :=
  IsScalarTower.of_algebraMap_eq' rfl

instance planeCoordinateRing_finiteRz : Module.Finite Rz A :=
  planeSexticPolynomial_monic.finite_adjoinRoot

/-- The canonical chart is integral over `F₂[z]`. -/
instance canonicalWChart_isIntegralRz : Algebra.IsIntegral Rz W :=
  Algebra.IsIntegral.trans A

/-- The canonical chart is finite over `F₂[z]`. -/
instance canonicalWChart_finiteRz : Module.Finite Rz W :=
  Module.Finite.trans A W

/-- The principal plane open embeds in the plane function field. -/
def planeDOpenToFunctionField : PlaneDOpen →+* L :=
  IsLocalization.Away.lift planeProjectionDenominator
    (IsUnit.mk0 _ <|
      (map_ne_zero_iff (algebraMap A L)
        (FaithfulSMul.algebraMap_injective A L)).2
          planeProjectionDenominator_ne_zero)

/-- The principal-open map to the function field is injective. -/
theorem planeDOpenToFunctionField_injective :
    Function.Injective planeDOpenToFunctionField := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers planeProjectionDenominator)
    planeDOpenToFunctionField]
  intro a b
  constructor
  · intro hab
    exact congrArg planeDOpenToFunctionField hab
  · intro hab
    have habL : algebraMap A L a = algebraMap A L b := by
      simpa only [planeDOpenToFunctionField,
        IsLocalization.Away.lift_eq] using hab
    exact congrArg (algebraMap A PlaneDOpen)
      ((FaithfulSMul.algebraMap_injective A L) habL)

@[simp] theorem planeDOpenToFunctionField_algebraMap (a : A) :
    planeDOpenToFunctionField (algebraMap A PlaneDOpen a) =
      algebraMap A L a := by
  exact IsLocalization.Away.lift_eq planeProjectionDenominator _ a

theorem canonicalWChartToPlaneDOpen_injective :
    Function.Injective canonicalWChartToPlaneDOpen := by
  intro a b hab
  apply canonicalWChartToDOpen_injective
  apply planeDOpenEquivCanonicalWChartDOpen.symm.injective
  simpa [planeDOpenEquivCanonicalWChartDOpen_symm_apply,
    canonicalWChartDOpenToPlaneDOpen_algebraMap] using hab

@[simp] theorem canonicalWChartToPlaneDOpen_plane (a : A) :
    canonicalWChartToPlaneDOpen (algebraMap A W a) =
      algebraMap A PlaneDOpen a := by
  change canonicalWChartToPlaneDOpen
      (planeCoordinateRingToCanonicalWChart a) =
    algebraMap A PlaneDOpen a
  calc
    canonicalWChartToPlaneDOpen (planeCoordinateRingToCanonicalWChart a) =
        canonicalWChartDOpenToPlaneDOpen
          (algebraMap W CanonicalWChartDOpen
            (planeCoordinateRingToCanonicalWChart a)) := by
      rw [canonicalWChartDOpenToPlaneDOpen_algebraMap]
    _ = canonicalWChartDOpenToPlaneDOpen
          (planeDOpenToCanonicalWChartDOpen
            (algebraMap A PlaneDOpen a)) := by
      rw [planeDOpenToCanonicalWChartDOpen_algebraMap]
    _ = algebraMap A PlaneDOpen a := by
      exact DFunLike.congr_fun
        canonicalWChartDOpenToPlaneDOpen_comp_planeDOpenToCanonicalWChartDOpen
        (algebraMap A PlaneDOpen a)

/-- The canonical chart map to the plane function field. -/
def canonicalWChartToFunctionField : W →+* L :=
  planeDOpenToFunctionField.comp canonicalWChartToPlaneDOpen

@[simp] theorem canonicalWChartToFunctionField_plane (a : A) :
    canonicalWChartToFunctionField (algebraMap A W a) =
      algebraMap A L a := by
  simp [canonicalWChartToFunctionField]

/-- The canonical chart embeds in the plane function field. -/
theorem canonicalWChartToFunctionField_injective :
    Function.Injective canonicalWChartToFunctionField :=
  planeDOpenToFunctionField_injective.comp
    canonicalWChartToPlaneDOpen_injective

instance wAlgebraL : Algebra W L :=
  canonicalWChartToFunctionField.toAlgebra

instance aWL : IsScalarTower A W L :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (canonicalWChartToFunctionField_plane a).symm)

instance wFaithfulL : FaithfulSMul W L :=
  (faithfulSMul_iff_algebraMap_injective W L).2
    canonicalWChartToFunctionField_injective

/-- The plane function field is the fraction field of the canonical chart. -/
instance canonicalWChart_isFractionRing : IsFractionRing W L := by
  apply IsFractionRing.of_field
  intro q
  obtain ⟨a, b, hb, hq⟩ := IsFractionRing.div_surjective A q
  refine ⟨algebraMap A W a, algebraMap A W b, ?_⟩
  calc
    q = algebraMap A L a / algebraMap A L b := hq.symm
    _ = algebraMap W L (algebraMap A W a) /
        algebraMap W L (algebraMap A W b) := by
      rw [← canonicalWChartToFunctionField_plane a,
        ← canonicalWChartToFunctionField_plane b]
      rfl

/-!
## Normality of the canonical chart

The chart is smooth over `F₂`, and its global Kähler differentials are free of
rank one.  At a maximal ideal `m`, formal smoothness injects the cotangent space
into the residue-field base change of those differentials.  The latter is
one-dimensional, while the localization is not a field; hence its cotangent
space has dimension exactly one.  The local ring is therefore a DVR.  We keep
the conormal construction abstract in the local ring and residue field: this
avoids repeatedly unfolding the dependent localization and quotient types.
-/

private abbrev LocalAt (m : Ideal W) [m.IsPrime] := Localization.AtPrime m

private abbrev ResidueAt (m : Ideal W) [m.IsPrime] :=
  IsLocalRing.ResidueField (LocalAt m)

noncomputable local instance localizationAlgebra (m : Ideal W) [m.IsPrime] :
    Algebra k₂ (LocalAt m) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

local instance localizationTower (m : Ideal W) [m.IsPrime] :
    IsScalarTower k₂ W (LocalAt m) := inferInstance

local instance canonicalWChartFormallySmooth :
    Algebra.FormallySmooth k₂ W := by
  have h := (chartAffineQuotient_smooth 3).toAlgebra.formallySmooth
  have halg : (algebraMap k₂ W).toAlgebra =
      (inferInstance : Algebra k₂ W) := Subsingleton.elim _ _
  rw [halg] at h
  exact h

local instance localizationFormallySmooth (m : Ideal W) [m.IsPrime] :
    Algebra.FormallySmooth k₂ (LocalAt m) := by
  letI : Algebra.FormallySmooth W (LocalAt m) :=
    Algebra.FormallySmooth.of_isLocalization m.primeCompl
  exact Algebra.FormallySmooth.comp k₂ W (LocalAt m)

noncomputable local instance residueAlgebra (m : Ideal W) [m.IsPrime] :
    Algebra k₂ (ResidueAt m) :=
  @IsLocalRing.ResidueField.algebra (LocalAt m) _ _ k₂ _ inferInstance

noncomputable local instance residueLocalAlgebra
    (m : Ideal W) [m.IsPrime] :
    Algebra (LocalAt m) (ResidueAt m) :=
  @IsLocalRing.ResidueField.algebra
    (LocalAt m) _ _ (LocalAt m) _ inferInstance

local instance residueTower (m : Ideal W) [m.IsPrime] :
    IsScalarTower k₂ (LocalAt m) (ResidueAt m) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable local instance residueFiniteType (m : Ideal W) [m.IsMaximal] :
    Algebra.FiniteType k₂ (ResidueAt m) :=
  Algebra.FiniteType.of_surjective
    (IsScalarTower.toAlgHom k₂ W (ResidueAt m))
    m.algebraMap_residueField_surjective

noncomputable local instance residueFinite (m : Ideal W) [m.IsMaximal] :
    Module.Finite k₂ (ResidueAt m) :=
  finite_of_finite_type_of_isJacobsonRing k₂ (ResidueAt m)

noncomputable local instance residueFormallyEtale
    (m : Ideal W) [m.IsMaximal] :
    Algebra.FormallyEtale k₂ (ResidueAt m) :=
  Algebra.FormallyEtale.of_isSeparable k₂ (ResidueAt m)

local instance localizationDifferentialModule
    (m : Ideal W) [m.IsPrime] :
    Module (LocalAt m) Ω[LocalAt m⁄k₂] :=
  KaehlerDifferential.module' k₂ (LocalAt m) (R' := LocalAt m)

local instance localizationDifferentialTower
    (m : Ideal W) [m.IsPrime] :
    IsScalarTower W (LocalAt m) Ω[LocalAt m⁄k₂] :=
  KaehlerDifferential.isScalarTower_of_tower k₂ (LocalAt m)
    (R₁ := W) (R₂ := LocalAt m)

private noncomputable def localizedDifferentialEquiv
    (m : Ideal W) [m.IsPrime] :
    Ω[LocalAt m⁄k₂] ≃ₗ[LocalAt m] LocalAt m := by
  letI : SMulCommClass k₂ (LocalAt m) (LocalAt m) := inferInstance
  exact IsLocalizedModule.mapEquiv m.primeCompl
    (KaehlerDifferential.map k₂ k₂ W (LocalAt m))
    (Algebra.linearMap W (LocalAt m)) (LocalAt m)
    (chartKaehlerDifferentialEquiv 3)

private theorem residueMap_surjective (m : Ideal W) [m.IsPrime] :
    Function.Surjective (algebraMap (LocalAt m) (ResidueAt m)) := by
  change Function.Surjective
    (algebraMap (LocalAt m) (IsLocalRing.ResidueField (LocalAt m)))
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  exact IsLocalRing.residue_surjective

private noncomputable def residueKerCotangentEquiv
    (O : Type*) [CommRing O] [IsLocalRing O] :
    (RingHom.ker
      (algebraMap O (IsLocalRing.ResidueField O))).Cotangent ≃ₗ[O]
        IsLocalRing.CotangentSpace O := by
  apply Ideal.Cotangent.equivOfEq
  rw [IsLocalRing.ResidueField.algebraMap_eq,
    IsLocalRing.ker_residue]

private theorem rawConormal_injective
    (k O κ : Type*) [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [Algebra.FormallySmooth k O] [Algebra.FormallySmooth k κ]
    (hres : Function.Surjective (algebraMap O κ)) :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k O κ) :=
  (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    hres).mpr inferInstance

private noncomputable def conormalMap
    (k O κ : Type*) [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ] [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent ≃ₗ[O]
        IsLocalRing.CotangentSpace O) :
    IsLocalRing.CotangentSpace O →ₗ[κ]
      κ ⊗[O] Ω[O⁄k] :=
  ((KaehlerDifferential.kerCotangentToTensor k O κ).comp
    eKer.symm.toLinearMap).extendScalarsOfSurjective hres

private theorem conormalMap_injective
    (k O κ : Type*) [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ] [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent ≃ₗ[O]
        IsLocalRing.CotangentSpace O)
    (hraw : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k O κ)) :
    Function.Injective (conormalMap k O κ hres eKer) := by
  intro x y hxy
  have hmap :
      KaehlerDifferential.kerCotangentToTensor k O κ
          (eKer.symm.toLinearMap x) =
        KaehlerDifferential.kerCotangentToTensor k O κ
          (eKer.symm.toLinearMap y) := by
    simpa only [conormalMap,
      LinearMap.extendScalarsOfSurjective_apply,
      LinearMap.comp_apply] using hxy
  exact eKer.symm.injective (hraw hmap)

private noncomputable def canonicalCotangentMap
    (m : Ideal W) [m.IsMaximal] :
    IsLocalRing.CotangentSpace (LocalAt m) →ₗ[ResidueAt m]
      ResidueAt m ⊗[LocalAt m] Ω[LocalAt m⁄k₂] :=
  conormalMap k₂ (LocalAt m) (ResidueAt m)
    (residueMap_surjective m) (residueKerCotangentEquiv (LocalAt m))

private theorem canonicalCotangentMap_injective
    (m : Ideal W) [m.IsMaximal] :
    Function.Injective (canonicalCotangentMap m) :=
  conormalMap_injective k₂ (LocalAt m) (ResidueAt m)
    (residueMap_surjective m) (residueKerCotangentEquiv (LocalAt m))
    (rawConormal_injective k₂ (LocalAt m) (ResidueAt m)
      (residueMap_surjective m))

private noncomputable def cotangentTargetEquivOverLocal
    (m : Ideal W) [m.IsPrime] :
    ResidueAt m ⊗[LocalAt m] Ω[LocalAt m⁄k₂] ≃ₗ[LocalAt m]
      ResidueAt m :=
  ((localizedDifferentialEquiv m).lTensor (ResidueAt m)).trans
    (TensorProduct.rid (LocalAt m) (ResidueAt m))

private noncomputable def cotangentTargetEquiv
    (m : Ideal W) [m.IsPrime] :
    ResidueAt m ⊗[LocalAt m] Ω[LocalAt m⁄k₂] ≃ₗ[ResidueAt m]
      ResidueAt m :=
  (cotangentTargetEquivOverLocal m).extendScalarsOfSurjective
    (residueMap_surjective m)

private theorem cotangent_finrank_le_one (m : Ideal W) [m.IsMaximal] :
    Module.finrank (ResidueAt m)
        (IsLocalRing.CotangentSpace (LocalAt m)) ≤ 1 := by
  letI : Module.Finite (ResidueAt m)
      (ResidueAt m ⊗[LocalAt m] Ω[LocalAt m⁄k₂]) :=
    Module.Finite.equiv (cotangentTargetEquiv m).symm
  calc
    Module.finrank (ResidueAt m)
        (IsLocalRing.CotangentSpace (LocalAt m)) ≤
        Module.finrank (ResidueAt m)
          (ResidueAt m ⊗[LocalAt m] Ω[LocalAt m⁄k₂]) :=
      (canonicalCotangentMap m).finrank_le_finrank_of_injective
        (canonicalCotangentMap_injective m)
    _ = Module.finrank (ResidueAt m) (ResidueAt m) :=
      (cotangentTargetEquiv m).finrank_eq
    _ = 1 := Module.finrank_self (ResidueAt m)

private theorem cotangent_finrank_eq_one (m : Ideal W) [m.IsMaximal] :
    Module.finrank (ResidueAt m)
        (IsLocalRing.CotangentSpace (LocalAt m)) = 1 := by
  have hle := cotangent_finrank_le_one m
  have hnotfield : ¬ IsField (LocalAt m) :=
    IsLocalization.AtPrime.not_isField
      W (canonicalWChart_maximal_ne_bot m inferInstance) (LocalAt m)
  have hne : Module.finrank (ResidueAt m)
      (IsLocalRing.CotangentSpace (LocalAt m)) ≠ 0 := by
    exact IsLocalRing.finrank_cotangentSpace_eq_zero_iff.not.mpr hnotfield
  omega

/-- Every localization of the canonical chart at a maximal ideal is normal. -/
theorem canonicalWChart_localization_isIntegrallyClosed
    (m : Ideal W) [m.IsMaximal] :
    IsIntegrallyClosed (Localization.AtPrime m) := by
  letI : IsDiscreteValuationRing (LocalAt m) :=
    IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
      (cotangent_finrank_eq_one m)
  infer_instance

/-- The canonical affine `w = 1` chart is integrally closed. -/
instance canonicalWChart_isIntegrallyClosed : IsIntegrallyClosed W :=
  IsIntegrallyClosed.of_localization_maximal
    (fun m _ _ => canonicalWChart_localization_isIntegrallyClosed m)

instance rzWL : IsScalarTower Rz W L :=
  IsScalarTower.to₁₃₄ Rz A W L

/-- The canonical chart is the integral closure of `F₂[z]` in the plane
function field. -/
instance canonicalWChart_isIntegralClosure : IsIntegralClosure W Rz L :=
  IsIntegralClosure.of_isIntegrallyClosed W Rz L

/-- The intrinsic canonical chart and the pre-existing plane normalization
are the same `F₂[z]`-algebra inside the common function field. -/
noncomputable def canonicalWChartEquivPlaneNormalization :
    W ≃ₐ[Rz] PlaneNormalization :=
  (IsIntegralClosure.equiv Rz W L PlaneNormalization :
    W ≃ₐ[Rz] PlaneNormalization)

/-!
## Relative norms on the canonical chart

The separable quartic function-field extension descends to the canonical
fraction field of `F₂[z]` and transports to the canonical fraction field of
the chart.  Together with the integral-closure description above, this makes
the chart a Dedekind domain and identifies the exponent in the norm of every
maximal ideal with its inertia degree.
-/

attribute [local instance] FractionRing.liftAlgebra

/-- The plane function field is separable over the canonical fraction field
of `F₂[z]`. -/
instance planeFunctionField_fractionRingBase_isSeparable :
    Algebra.IsSeparable K L := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv Rz Fz).symm.toRingEquiv
    (AlgEquiv.refl : L ≃ₐ[W] L).toRingEquiv ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv Rz Fz).symm
    (AlgEquiv.refl : L ≃ₐ[W] L) _

/-- The canonical chart is torsion-free over `F₂[z]`. -/
instance canonicalWChart_isTorsionFree : Module.IsTorsionFree Rz W := by
  letI : Module.IsTorsionFree Rz L :=
    Module.IsTorsionFree.trans_faithfulSMul Rz K L
  exact IsIntegralClosure.isTorsionFree Rz L

/-- The canonical chart is a Dedekind domain. -/
instance canonicalWChart_isDedekindDomain : IsDedekindDomain W :=
  IsIntegralClosure.isDedekindDomain Rz K L W

/-- Separability transported to the canonical fraction-ring types used by
relative ideal norms. -/
instance canonicalWChart_fractionRing_isSeparable :
    Algebra.IsSeparable K (FractionRing W) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv Rz Fz).symm.toRingEquiv
    (FractionRing.algEquiv W L).symm.toRingEquiv ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv Rz Fz).symm
    (FractionRing.algEquiv W L).symm _

/-- Contract a maximal ideal of the canonical chart to `F₂[z]`. -/
def canonicalWChartBasePrime (P : Ideal W) : Ideal Rz :=
  P.comap (algebraMap Rz W)

/-- A maximal ideal of the canonical chart contracts to a maximal ideal of
`F₂[z]`. -/
instance canonicalWChartBasePrime_isMaximal
    (P : Ideal W) [P.IsMaximal] :
    (canonicalWChartBasePrime P).IsMaximal := by
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P

/-- A chart ideal lies over its explicit contraction to `F₂[z]`. -/
instance canonicalWChartBasePrime_liesOver (P : Ideal W) :
    P.LiesOver (canonicalWChartBasePrime P) := by
  rw [Ideal.liesOver_iff]
  rfl

/-- The norm of a maximal chart ideal is its contracted base prime raised to
the residue-field degree. -/
theorem canonicalWChart_relNorm_eq_basePrime_pow
    (P : Ideal W) [P.IsMaximal] :
    Ideal.relNorm Rz P = canonicalWChartBasePrime P ^
      (canonicalWChartBasePrime P).inertiaDeg P := by
  exact SeparableRelativeNorm.relNorm_eq_pow_of_isMaximal_of_isSeparable
    Rz W P (canonicalWChartBasePrime P)

end MazurProof.RationalPointsN25QuotientTwoWChartNormalization
