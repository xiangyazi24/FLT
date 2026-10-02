import InfinityNormalizationCheck
import CenterLocalizationCheck

/-! The localization comparison specialized to the actual reciprocal
normalization carrier; the named boundary bindings remain lead-checked. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityLocalizationsCheck
open N25F_InfinityNormalization N25F_CenterLocalization
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain InfinityNormalization]
variable [IsFractionRing InfinityNormalization CurveField]
variable {R : Type*} [CommRing R] [IsLocalRing R]
variable (p : Ideal InfinityNormalization) [p.IsPrime]
variable (f : InfinityNormalization →+* R)
variable (hp : p = (IsLocalRing.maximalIdeal R).comap f) (hp0 : p ≠ ⊥)
variable (g : R →+* CurveField) (hg : Function.Injective g)
variable (hcomp : g.comp f = algebraMap InfinityNormalization CurveField)

def infinityLocalizationEquiv :
    letI : Algebra InfinityNormalization R := f.toAlgebra
    Localization.AtPrime p ≃ₐ[InfinityNormalization] R :=
  centerLocalizationEquiv p f hp hp0 g hg hcomp

@[simp]
theorem infinityLocalizationEquiv_algebraMap (a : InfinityNormalization) :
    infinityLocalizationEquiv p f hp hp0 g hg hcomp
      (algebraMap InfinityNormalization (Localization.AtPrime p) a) = f a :=
  by
    letI : Algebra InfinityNormalization R := f.toAlgebra
    exact (infinityLocalizationEquiv p f hp hp0 g hg hcomp).commutes a

@[simp]
theorem localToField_localization_algebraMap (a : InfinityNormalization) :
    g (infinityLocalizationEquiv p f hp hp0 g hg hcomp
      (algebraMap InfinityNormalization (Localization.AtPrime p) a)) =
      (a : CurveField) := by
  rw [infinityLocalizationEquiv_algebraMap]
  exact RingHom.congr_fun hcomp a

#print axioms infinityLocalizationEquiv
#print axioms infinityLocalizationEquiv_algebraMap
#print axioms localToField_localization_algebraMap
end MazurProof.N25F_InfinityLocalizationsCheck
