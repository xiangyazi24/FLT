import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kahler differentials along algebra equivalences

An isomorphism of algebras transports their relative Kahler differential
modules.  The induced equivalence is semilinear over the underlying ring
equivalence, since the two modules have different coefficient rings.
-/

set_option autoImplicit false

noncomputable section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

namespace KaehlerDifferential

/-- A bijective algebra map induces a bijection on relative Kahler
differentials. -/
theorem map_bijective_of_bijective [Algebra A B] [IsScalarTower R A B]
    (h : Function.Bijective (algebraMap A B)) :
    Function.Bijective (KaehlerDifferential.map R R A B) := by
  refine ⟨?_, map_surjective_of_surjective R R A B h.2⟩
  rw [← LinearMap.ker_eq_bot]
  rw [ker_map_of_surjective R A B h.2]
  suffices hmap : Function.Injective
      ((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
        (Finsupp.lmapDomain A A (algebraMap A B))) by
    rw [LinearMap.ker_eq_bot.mpr hmap, Submodule.map_bot]
  exact
    (Finsupp.mapRange_injective (algebraMap A B) (map_zero _) h.1).comp
      (Finsupp.mapDomain_injective h.1)

/-- An algebra equivalence induces a semilinear equivalence of relative
Kahler differential modules. -/
noncomputable def mapAlgEquiv (e : A ≃ₐ[R] B) :
    haveI := RingHomInvPair.of_ringEquiv e.toRingEquiv
    haveI := RingHomInvPair.symm
      (↑e.toRingEquiv : A →+* B) (e.toRingEquiv.symm : B →+* A)
    Ω[A⁄R] ≃ₛₗ[(↑e.toRingEquiv : A →+* B)] Ω[B⁄R] := by
  letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI := RingHomInvPair.symm
    (↑e.toRingEquiv : A →+* B) (e.toRingEquiv.symm : B →+* A)
  letI : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  let f : Ω[A⁄R] →ₛₗ[(↑e.toRingEquiv : A →+* B)] Ω[B⁄R] :=
    { toFun := KaehlerDifferential.map R R A B
      map_add' := map_add (KaehlerDifferential.map R R A B)
      map_smul' := by
        intro a x
        rw [map_smul]
        change e a • KaehlerDifferential.map R R A B x = _
        rfl }
  exact LinearEquiv.ofBijective f
    (map_bijective_of_bijective (R := R) (A := A) (B := B) e.bijective)

@[simp]
theorem mapAlgEquiv_D (e : A ≃ₐ[R] B) (x : A) :
    letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
    letI := RingHomInvPair.symm
      (↑e.toRingEquiv : A →+* B) (e.toRingEquiv.symm : B →+* A)
    mapAlgEquiv e (D R A x) = D R B (e x) := by
  letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI := RingHomInvPair.symm
    (↑e.toRingEquiv : A →+* B) (e.toRingEquiv.symm : B →+* A)
  letI : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  change KaehlerDifferential.map R R A B (D R A x) = _
  rw [map_D]
  rfl

end KaehlerDifferential
