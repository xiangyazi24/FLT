import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Affine closed-fibre comparison

This file packages the first isomorphism theorem and the standard
tensor-with-a-quotient description needed to identify an affine chart of
a closed base change.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Algebra TensorProduct

namespace MazurProof.ClosedFiberAffineCore

universe u v w

/-- A surjection with kernel `I` identifies `A ⧸ I` with its target. -/
noncomputable def quotientEquivOfSurjectiveKerEq
    {A : Type u} {A₀ : Type v}
    [CommRing A] [CommRing A₀]
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (I : Ideal A)
    (hker : RingHom.ker ρ = I) :
    A ⧸ I ≃+* A₀ :=
  (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hρ)

@[simp]
theorem quotientEquivOfSurjectiveKerEq_mk
    {A : Type u} {A₀ : Type v}
    [CommRing A] [CommRing A₀]
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (I : Ideal A)
    (hker : RingHom.ker ρ = I)
    (a : A) :
    quotientEquivOfSurjectiveKerEq ρ hρ I hker
        (Ideal.Quotient.mk I a) = ρ a := by
  simp [quotientEquivOfSurjectiveKerEq]

/-- If `ρ : A → A₀` is onto and its kernel is the extension of
`I ⊂ R`, then `A ⊗[R] R/I` is `A₀`. -/
noncomputable def tensorQuotientEquivOfReduction
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀]
    [Algebra R A]
    (I : Ideal R)
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (hker :
      RingHom.ker ρ =
        I.map (algebraMap R A)) :
    A ⊗[R] (R ⧸ I) ≃+* A₀ :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toRingEquiv).trans
    (quotientEquivOfSurjectiveKerEq
      ρ hρ (I.map (algebraMap R A)) hker)

@[simp]
theorem tensorQuotientEquivOfReduction_tmul_one
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀]
    [Algebra R A]
    (I : Ideal R)
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (hker :
      RingHom.ker ρ =
        I.map (algebraMap R A))
    (a : A) :
    tensorQuotientEquivOfReduction I ρ hρ hker
        (a ⊗ₜ[R] (1 : R ⧸ I)) = ρ a := by
  change
    quotientEquivOfSurjectiveKerEq
        ρ hρ (I.map (algebraMap R A)) hker
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm
          (a ⊗ₜ[R] (1 : R ⧸ I))) =
      ρ a
  rw [show (1 : R ⧸ I) =
      Ideal.Quotient.mk I (1 : R) by simp]
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simpa only [one_smul, ← Ideal.Quotient.mk_eq_mk] using
    quotientEquivOfSurjectiveKerEq_mk
      ρ hρ (I.map (algebraMap R A)) hker a

/-- The closed base change of `Spec A` along `Spec(R/I) → Spec R`
is `Spec A₀`. -/
noncomputable def specPullbackIsoOfReduction
    {R A A₀ : Type u}
    [CommRing R] [CommRing A] [CommRing A₀]
    [Algebra R A]
    (I : Ideal R)
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (hker :
      RingHom.ker ρ =
        I.map (algebraMap R A)) :
    pullback
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R A)))
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (R ⧸ I)))) ≅
      Spec (CommRingCat.of A₀) :=
  pullbackSpecIso R A (R ⧸ I) ≪≫
    Scheme.Spec.mapIso
      (tensorQuotientEquivOfReduction
        I ρ hρ hker).symm.toCommRingCatIso.op

@[reassoc]
theorem specPullbackIsoOfReduction_hom_specMap
    {R A A₀ : Type u}
    [CommRing R] [CommRing A] [CommRing A₀]
    [Algebra R A]
    (I : Ideal R)
    (ρ : A →+* A₀)
    (hρ : Function.Surjective ρ)
    (hker :
      RingHom.ker ρ =
        I.map (algebraMap R A)) :
    (specPullbackIsoOfReduction I ρ hρ hker).hom ≫
        Spec.map (CommRingCat.ofHom ρ) =
      pullback.fst
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R A)))
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (R ⧸ I)))) := by
  rw [specPullbackIsoOfReduction, Iso.trans_hom, Category.assoc,
    ← pullbackSpecIso_hom_fst R A (R ⧸ I)]
  congr 1
  change
    Spec.map
          (CommRingCat.ofHom
            (tensorQuotientEquivOfReduction
              I ρ hρ hker).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ρ) =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap A (A ⊗[R] (R ⧸ I))))
  rw [← Spec.map_comp]
  congr 1
  ext a
  change
    (tensorQuotientEquivOfReduction I ρ hρ hker).symm
        (ρ a) =
      a ⊗ₜ[R] (1 : R ⧸ I)
  apply
    (tensorQuotientEquivOfReduction I ρ hρ hker).injective
  rw [RingEquiv.apply_symm_apply,
    tensorQuotientEquivOfReduction_tmul_one]

end MazurProof.ClosedFiberAffineCore
