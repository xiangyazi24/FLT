import Mathlib

open scoped TensorProduct

namespace Q6367Check

private noncomputable def residueKerCotangentEquiv
    (O : Type*) [CommRing O] [IsLocalRing O] :
    (RingHom.ker (algebraMap O (IsLocalRing.ResidueField O))).Cotangent
      ≃ₗ[O] IsLocalRing.CotangentSpace O := by
  rw [IsLocalRing.ResidueField.algebraMap_eq,
    IsLocalRing.ker_residue]

private noncomputable def conormalMap
    (k O κ : Type*)
    [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent
        ≃ₗ[O] IsLocalRing.CotangentSpace O) :
    IsLocalRing.CotangentSpace O →ₗ[κ]
      κ ⊗[O] Ω[O⁄k] :=
  ((KaehlerDifferential.kerCotangentToTensor k O κ).comp
      eKer.symm.toLinearMap).extendScalarsOfSurjective hres

private theorem conormalMap_apply
    (k O κ : Type*)
    [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent
        ≃ₗ[O] IsLocalRing.CotangentSpace O)
    (x : IsLocalRing.CotangentSpace O) :
    conormalMap k O κ hres eKer x =
      KaehlerDifferential.kerCotangentToTensor k O κ (eKer.symm x) := by
  rfl

private theorem conormalMap_injective
    (k O κ : Type*)
    [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent
        ≃ₗ[O] IsLocalRing.CotangentSpace O)
    (hraw : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k O κ)) :
    Function.Injective (conormalMap k O κ hres eKer) := by
  intro x y hxy
  apply eKer.symm.injective
  apply hraw
  simpa only [conormalMap_apply] using hxy

private theorem rawConormal_injective
    (k O κ : Type*)
    [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [Algebra.FormallySmooth k O]
    [Algebra.FormallySmooth k κ]
    (hres : Function.Surjective (algebraMap O κ)) :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k O κ) :=
  (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    (R := k) (P := O) (A := κ) hres).2 inferInstance

private theorem conormalMap_injective_of_formallySmooth
    (k O κ : Type*)
    [CommRing k] [CommRing O] [Field κ]
    [Algebra k O] [Algebra O κ] [Algebra k κ]
    [IsScalarTower k O κ]
    [IsLocalRing O]
    [Module κ (IsLocalRing.CotangentSpace O)]
    [IsScalarTower O κ (IsLocalRing.CotangentSpace O)]
    [Algebra.FormallySmooth k O]
    [Algebra.FormallySmooth k κ]
    (hres : Function.Surjective (algebraMap O κ))
    (eKer :
      (RingHom.ker (algebraMap O κ)).Cotangent
        ≃ₗ[O] IsLocalRing.CotangentSpace O) :
    Function.Injective (conormalMap k O κ hres eKer) :=
  conormalMap_injective k O κ hres eKer
    (rawConormal_injective k O κ hres)

private noncomputable def atPrimeConormalMap
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (m : Ideal R) [m.IsPrime]
    [Algebra k (Localization.AtPrime m)]
    [IsScalarTower k R (Localization.AtPrime m)] :
    IsLocalRing.CotangentSpace (Localization.AtPrime m) →ₗ[
      IsLocalRing.ResidueField (Localization.AtPrime m)]
      IsLocalRing.ResidueField (Localization.AtPrime m) ⊗[
        Localization.AtPrime m]
        Ω[Localization.AtPrime m⁄k] :=
  conormalMap k
    (Localization.AtPrime m)
    (IsLocalRing.ResidueField (Localization.AtPrime m))
    (by
      simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_surjective :
          Function.Surjective
            (IsLocalRing.residue (Localization.AtPrime m))))
    (residueKerCotangentEquiv (Localization.AtPrime m))

private theorem atPrimeConormalMap_injective
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (m : Ideal R) [m.IsPrime]
    [Algebra k (Localization.AtPrime m)]
    [IsScalarTower k R (Localization.AtPrime m)]
    [Algebra.FormallySmooth k (Localization.AtPrime m)]
    [Algebra.FormallySmooth k
      (IsLocalRing.ResidueField (Localization.AtPrime m))] :
    Function.Injective (atPrimeConormalMap k R m) := by
  unfold atPrimeConormalMap
  apply conormalMap_injective_of_formallySmooth

end Q6367Check
