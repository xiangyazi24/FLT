import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.ZMod.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityResidueFields

/-- At a maximal prime, an explicit quotient field identification also
identifies the residue field of the localization. -/
def residueRingEquivOfQuotient {A R k : Type*} [CommRing A] [CommRing R]
    [Field k] (p : Ideal A) [p.IsMaximal] [Algebra A R]
    [IsLocalization.AtPrime R p] [IsLocalRing R] (e : A ⧸ p ≃+* k) :
    IsLocalRing.ResidueField R ≃+* k :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal p R).symm.trans e

/-- Equal primes have canonically isomorphic residue fields. -/
def residueRingEquivOfEq {A : Type*} [CommRing A]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (h : p = q) :
    p.ResidueField ≃+* q.ResidueField := by
  subst q
  exact RingEquiv.refl _

/-- Any extension between two binary fields has degree one, for its actual
Algebra action. No compatibility of separately chosen field equivalences
is needed: unital maps out of ZMod 2 are unique. -/
theorem finrank_eq_one_of_binary_ringEquivs {K L : Type*} [Field K] [Field L]
    [Algebra K L] (eK : K ≃+* ZMod 2) (eL : L ≃+* ZMod 2) :
    Module.finrank K L = 1 := by
  have hcomp : (eL.toRingHom.comp (algebraMap K L)).comp eK.symm.toRingHom =
      RingHom.id (ZMod 2) := RingHom.ext_zmod _ _
  have hs : Function.Surjective (algebraMap K L) := by
    intro x
    refine ⟨eK.symm (eL x), eL.injective ?_⟩
    exact RingHom.congr_fun hcomp (eL x)
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L)
    ⟨(algebraMap K L).injective, hs⟩
  simpa using e.toLinearEquiv.finrank_eq.symm


/-- An actual prime's inertia degree is one when both residue fields are binary. -/
theorem inertiaDeg_eq_one_of_binary_ringEquivs {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (p : Ideal B) [p.IsPrime]
    (eA : (p.under A).ResidueField ≃+* ZMod 2)
    (eB : p.ResidueField ≃+* ZMod 2) : p.inertiaDeg' A = 1 := by
  letI := Localization.AtPrime.algebraOfLiesOver (p.under A) p
  rw [Ideal.inertiaDeg'_def]
  exact finrank_eq_one_of_binary_ringEquivs eA eB

example : (Polynomial (ZMod 2) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod 2))}) ≃+* ZMod 2 := by
  exact (Ideal.quotEquivOfEq
    (I := Ideal.span {(Polynomial.X : Polynomial (ZMod 2))})
    (J := Ideal.span {Polynomial.X - Polynomial.C (0 : ZMod 2)}) (by simp)).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : ZMod 2)).toRingEquiv

private def sampleBasePrime : Ideal (Polynomial (ZMod 2)) := Ideal.span {Polynomial.X}
local instance : sampleBasePrime.IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X

private def sampleBaseResidueEquiv : sampleBasePrime.ResidueField ≃+* ZMod 2 :=
  residueRingEquivOfQuotient (R := Localization.AtPrime sampleBasePrime) sampleBasePrime (by
    change (Polynomial (ZMod 2) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod 2))}) ≃+* ZMod 2
    exact (Ideal.quotEquivOfEq
      (I := Ideal.span {(Polynomial.X : Polynomial (ZMod 2))})
      (J := Ideal.span {Polynomial.X - Polynomial.C (0 : ZMod 2)}) (by simp)).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : ZMod 2)).toRingEquiv)

example {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (f : A →ₐ[ZMod 2] ZMod 2) (hf : Function.Surjective f) :
    letI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
    IsLocalRing.ResidueField (Localization.AtPrime (RingHom.ker f.toRingHom)) ≃+* ZMod 2 := by
  letI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
  letI : (RingHom.ker f.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective f.toRingHom hf
  exact residueRingEquivOfQuotient
    (R := Localization.AtPrime (RingHom.ker f.toRingHom)) (RingHom.ker f.toRingHom)
    (RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf)

#print axioms sampleBaseResidueEquiv
#print axioms residueRingEquivOfQuotient
#print axioms residueRingEquivOfEq
#print axioms finrank_eq_one_of_binary_ringEquivs
#print axioms inertiaDeg_eq_one_of_binary_ringEquivs
end MazurProof.N25F_InfinityResidueFields
