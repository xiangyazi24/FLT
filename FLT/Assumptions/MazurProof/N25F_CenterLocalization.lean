import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import FLT.Assumptions.MazurProof.N25F_LocalValuationRigidity

/-! The actual local map induced by a center prime. No localness or
localization map is assumed: both are constructed from the center identity. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_CenterLocalization

variable {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing R]
variable (p : Ideal A) [p.IsPrime] (f : A →+* R)
variable (hp : p = (IsLocalRing.maximalIdeal R).comap f)

include hp in
private theorem map_primeCompl_isUnit (s : p.primeCompl) : IsUnit (f s) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  apply s.property
  exact (SetLike.ext_iff.mp hp (s : A)).mpr h

/-- Localizing at the center gives a map into the actual local ring. -/
def centerLocalizationMap : Localization.AtPrime p →+* R :=
  IsLocalization.lift (S := Localization.AtPrime p) (g := f)
    (map_primeCompl_isUnit p f hp)

@[simp]
theorem centerLocalizationMap_algebraMap (a : A) :
    centerLocalizationMap p f hp (algebraMap A (Localization.AtPrime p) a) = f a :=
  IsLocalization.lift_eq (map_primeCompl_isUnit p f hp) a

/-- The induced map is local because its source prime is the exact center. -/
instance centerLocalizationMap_isLocalHom : IsLocalHom (centerLocalizationMap p f hp) where
  map_nonunit x hx := by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff _ p a s).mpr
    intro ha
    have heq : f a = f s * centerLocalizationMap p f hp
        (IsLocalization.mk' (Localization.AtPrime p) a s) :=
      (IsLocalization.lift_mk'_spec (map_primeCompl_isUnit p f hp) a _ s).mp rfl
    have hunit : IsUnit (f a) := heq.symm ▸ (map_primeCompl_isUnit p f hp s).mul hx
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit (by rw [hp] at ha; exact ha)


variable [IsDedekindDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- The localization at a nonzero Dedekind center is the boundary local ring,
provided both embed compatibly in the fixed fraction field. -/
theorem centerLocalizationMap_bijective
    (hp0 : p ≠ ⊥) (g : R →+* K) (hg : Function.Injective g)
    (hcomp : g.comp f = algebraMap A K) :
    Function.Bijective (centerLocalizationMap p f hp) := by
  letI : Algebra (Localization.AtPrime p) K :=
    (g.comp (centerLocalizationMap p f hp)).toAlgebra
  letI : IsScalarTower A (Localization.AtPrime p) K :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A K a = g (centerLocalizationMap p f hp
        (algebraMap A (Localization.AtPrime p) a))
      rw [centerLocalizationMap_algebraMap]
      exact (RingHom.congr_fun hcomp a).symm
  letI : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isLocalization p.primeCompl
      (Localization.AtPrime p) K p.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp0
      (Localization.AtPrime p)
  exact N25F_LocalValuationRigidity.bijective_of_local_same_fraction_field
    (centerLocalizationMap p f hp) g hg rfl

/-- The coefficient-compatible local identification, with no assumed isomorphism. -/
def centerLocalizationEquiv
    (hp0 : p ≠ ⊥) (g : R →+* K) (hg : Function.Injective g)
    (hcomp : g.comp f = algebraMap A K) :
    letI : Algebra A R := f.toAlgebra
    Localization.AtPrime p ≃ₐ[A] R := by
  letI : Algebra A R := f.toAlgebra
  exact AlgEquiv.ofBijective
    { centerLocalizationMap p f hp with
      commutes' := centerLocalizationMap_algebraMap p f hp }
    (centerLocalizationMap_bijective p f hp hp0 g hg hcomp)

end MazurProof.N25F_CenterLocalization
