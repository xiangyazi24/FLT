import InfinityFieldCheck
import N25F_RationalBaseInversion
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The reciprocal rational base acts on the same actual curve function
field. Its action is the original one precomposed with the proved base
inversion, and its finite degree remains four. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityFunctionField

private theorem finite_finrank_twist
    {B L : Type*} [Field B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (e : B ≃+* B) :
    let n := Module.finrank B L
    letI : Algebra B L := ((algebraMap B L).comp e.toRingHom).toAlgebra
    Module.Finite B L ∧ Module.finrank B L = n := by
  let n := Module.finrank B L
  let φ := algebraMap B L
  let oldModule : Module B L := inferInstance
  let b := Module.finBasis B L
  have hsmul (c : B) (x : L) : c • x = φ c * x := Algebra.smul_def c x
  let newAlgebra : Algebra B L := (φ.comp e.toRingHom).toAlgebra
  letI : Algebra B L := newAlgebra
  let newModule : Module B L := @Algebra.toModule B L _ _ newAlgebra
  letI : Module B L := newModule
  let b' : @Module.Basis (Fin n) B L _ _ newModule :=
    @Module.Basis.mapCoeffs (Fin n) B L _ _ oldModule b B _ newModule e.symm (by
    intro c x
    rw [hsmul]
    change φ (e (e.symm c)) * x = φ c * x
    rw [e.apply_symm_apply])
  exact ⟨b'.finiteDimensional_of_finite, by simpa using Module.finrank_eq_card_basis b'⟩


open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_RationalBaseInversion N25F_InfinityBaseMaps
open N25F_ProjectivePrincipalDivisor
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing W
variable [Module.IsTorsionFree BasePolynomial W] [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable (hWrank : Module.finrank BasePolynomial W = 4)


def affinePolynomialBaseToField : BasePolynomial →ₐ[ZMod 2] CurveField :=
  Polynomial.aeval (algebraMap W CurveField qz)

theorem affinePolynomialBaseToField_injective :
    Function.Injective affinePolynomialBaseToField := by
  intro p q h
  apply FaithfulSMul.algebraMap_injective BasePolynomial W
  apply IsFractionRing.injective W CurveField
  rw [basePolynomial_inFunctionField, basePolynomial_inFunctionField]
  exact h

/-- The original rational-base action, with its coordinates fixed. -/
def affineRationalBaseToField : BaseField →ₐ[ZMod 2] CurveField :=
  IsFractionRing.liftAlgHom
    (R := ZMod 2) (A := BasePolynomial) (K := BaseField) (L := CurveField)
    (g := affinePolynomialBaseToField) affinePolynomialBaseToField_injective

@[simp]
theorem affineRationalBaseToField_algebraMap (p : BasePolynomial) :
    affineRationalBaseToField (algebraMap BasePolynomial BaseField p) =
      affinePolynomialBaseToField p := by
  simp [affineRationalBaseToField]

@[simp]
theorem affineRationalBaseToField_variable :
    affineRationalBaseToField baseVariable = algebraMap W CurveField qz := by
  change affineRationalBaseToField
    (algebraMap BasePolynomial BaseField Polynomial.X) = _
  rw [affineRationalBaseToField_algebraMap]
  exact Polynomial.aeval_X _

/-- The reciprocal rational-base action is an explicit coordinate change. -/
def infinityRationalBaseToField : BaseField →ₐ[ZMod 2] CurveField :=
  affineRationalBaseToField.comp baseInversion.toAlgHom

/-- Its restriction is exactly the already-constructed reciprocal polynomial base. -/
theorem infinityRationalBaseToField_comp_algebraMap :
    infinityRationalBaseToField.comp
      (IsScalarTower.toAlgHom (ZMod 2) BasePolynomial BaseField) =
      infinityBaseToField := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom, infinityBaseToField,
    Polynomial.aeval_X]
  change affineRationalBaseToField (baseInversion baseVariable) =
    1 / algebraMap W CurveField qz
  rw [baseInversion_variable, map_inv₀, affineRationalBaseToField_variable, one_div]

@[simp]
theorem infinityRationalBaseToField_algebraMap (p : BasePolynomial) :
    infinityRationalBaseToField (algebraMap BasePolynomial BaseField p) =
      infinityBaseToField p :=
  AlgHom.congr_fun infinityRationalBaseToField_comp_algebraMap p

include hWrank in
/-- The existing actual affine quartic degree, under the explicit old action. -/
theorem affineRationalBaseToField_finrank :
    letI : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
    Module.finrank BaseField CurveField = 4 := by
  letI : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
  letI : IsScalarTower BasePolynomial BaseField CurveField :=
    IsScalarTower.of_algebraMap_eq fun p => by
      calc
        algebraMap BasePolynomial CurveField p =
            algebraMap W CurveField (algebraMap BasePolynomial W p) :=
          IsScalarTower.algebraMap_apply BasePolynomial W CurveField p
        _ = affinePolynomialBaseToField p := basePolynomial_inFunctionField p
        _ = affineRationalBaseToField (algebraMap BasePolynomial BaseField p) :=
          (affineRationalBaseToField_algebraMap p).symm
  letI : Algebra.IsAlgebraic BasePolynomial W := Algebra.IsAlgebraic.of_finite _ _
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing BasePolynomial BaseField W CurveField]
  exact hWrank

include hWrank in
/-- The same actual curve function field is finite of degree four over the
reciprocal rational base, under the explicitly constructed action. -/
theorem infinityRationalBaseToField_finite_finrank :
    letI : Algebra BaseField CurveField := infinityRationalBaseToField.toRingHom.toAlgebra
    Module.Finite BaseField CurveField ∧ Module.finrank BaseField CurveField = 4 := by
  letI : Algebra BaseField CurveField := affineRationalBaseToField.toRingHom.toAlgebra
  letI : FiniteDimensional BaseField CurveField :=
    FiniteDimensional.of_finrank_pos (by rw [affineRationalBaseToField_finrank hWrank]; decide)
  have h := finite_finrank_twist (L := CurveField) baseInversion.toRingEquiv
  exact ⟨h.1, h.2.trans (affineRationalBaseToField_finrank hWrank)⟩


#check @affinePolynomialBaseToField
#print axioms affinePolynomialBaseToField
#check @affinePolynomialBaseToField_injective
#print axioms affinePolynomialBaseToField_injective
#check @affineRationalBaseToField
#print axioms affineRationalBaseToField
#check @affineRationalBaseToField_algebraMap
#print axioms affineRationalBaseToField_algebraMap
#check @affineRationalBaseToField_variable
#print axioms affineRationalBaseToField_variable
#check @infinityRationalBaseToField
#print axioms infinityRationalBaseToField
#check @infinityRationalBaseToField_comp_algebraMap
#print axioms infinityRationalBaseToField_comp_algebraMap
#check @infinityRationalBaseToField_algebraMap
#print axioms infinityRationalBaseToField_algebraMap
#check @affineRationalBaseToField_finrank
#print axioms affineRationalBaseToField_finrank
#check @infinityRationalBaseToField_finite_finrank
#print axioms infinityRationalBaseToField_finite_finrank
end MazurProof.N25F_InfinityFunctionField
