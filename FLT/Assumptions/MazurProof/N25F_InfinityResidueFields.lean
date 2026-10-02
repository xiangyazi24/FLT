import FLT.Assumptions.MazurProof.N25F_InfinityPrimeContraction
import FLT.Assumptions.MazurProof.N25F_InfinityLocalizations
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
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


open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityLocalizations N25F_InfinityBoundaryAlgebras
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra
local instance : xPrime.IsMaximal := xPrime_isMaximal
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime
local instance : yzPrime.IsMaximal := yzPrime_isMaximal
local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime
local instance : zPrime.IsMaximal := zPrime_isMaximal
local instance : zPrime.IsPrime := zPrime_isMaximal.isPrime

/-- The actual X boundary local ring has the binary residue field. -/
def xLocalResidueRingEquivF2 : IsLocalRing.ResidueField XLocalRing ≃+* ZMod 2 :=
  residueRingEquivOfQuotient (R := XLocalRing) xPrime
    (RingHom.quotientKerEquivOfSurjective (f := xChartEval.toRingHom) xChartEval_surjective)

/-- The constructed normalization center has that same binary residue field. -/
def xInfinityResidueRingEquivF2 : xInfinityPrime.ResidueField ≃+* ZMod 2 :=
  (IsLocalRing.ResidueField.mapEquiv xInfinityLocalizationEquiv.toRingEquiv).trans
    xLocalResidueRingEquivF2

/-- The actual YZ boundary local ring has the binary residue field. -/
def yzLocalResidueRingEquivF2 : IsLocalRing.ResidueField YZLocalRing ≃+* ZMod 2 :=
  residueRingEquivOfQuotient (R := YZLocalRing) yzPrime
    (RingHom.quotientKerEquivOfSurjective (f := yzPointEval.toRingHom) yzPointEval_surjective)

/-- The constructed normalization center has that same binary residue field. -/
def yzInfinityResidueRingEquivF2 : yzInfinityPrime.ResidueField ≃+* ZMod 2 :=
  (IsLocalRing.ResidueField.mapEquiv yzInfinityLocalizationEquiv.toRingEquiv).trans
    yzLocalResidueRingEquivF2

/-- The actual Z boundary local ring has the binary residue field. -/
def zLocalResidueRingEquivF2 : IsLocalRing.ResidueField ZLocalRing ≃+* ZMod 2 :=
  residueRingEquivOfQuotient (R := ZLocalRing) zPrime
    (RingHom.quotientKerEquivOfSurjective (f := zPointEval.toRingHom) zPointEval_surjective)

/-- The constructed normalization center has that same binary residue field. -/
def zInfinityResidueRingEquivF2 : zInfinityPrime.ResidueField ≃+* ZMod 2 :=
  (IsLocalRing.ResidueField.mapEquiv zInfinityLocalizationEquiv.toRingEquiv).trans
    zLocalResidueRingEquivF2

/-- The reciprocal-coordinate prime (T) has residue field F2. -/
def infinityBaseResidueRingEquivF2 : infinityBasePrime.ResidueField ≃+* ZMod 2 :=
  residueRingEquivOfQuotient (R := Localization.AtPrime infinityBasePrime) infinityBasePrime (by
    change (BasePolynomial ⧸ Ideal.span {(Polynomial.X : BasePolynomial)}) ≃+* ZMod 2
    exact (Ideal.quotEquivOfEq
      (I := Ideal.span {(Polynomial.X : Polynomial (ZMod 2))})
      (J := Ideal.span {Polynomial.X - Polynomial.C (0 : ZMod 2)}) (by simp)).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : ZMod 2)).toRingEquiv)

/-- The actual inertia degree over the reciprocal polynomial base is one. -/
theorem xInfinityPrime_inertiaDeg_eq_one : xInfinityPrime.inertiaDeg' BasePolynomial = 1 :=
  inertiaDeg_eq_one_of_binary_ringEquivs (A := BasePolynomial) xInfinityPrime
    ((residueRingEquivOfEq xInfinityPrime_under).trans infinityBaseResidueRingEquivF2)
    xInfinityResidueRingEquivF2

/-- The actual inertia degree over the reciprocal polynomial base is one. -/
theorem yzInfinityPrime_inertiaDeg_eq_one : yzInfinityPrime.inertiaDeg' BasePolynomial = 1 :=
  inertiaDeg_eq_one_of_binary_ringEquivs (A := BasePolynomial) yzInfinityPrime
    ((residueRingEquivOfEq yzInfinityPrime_under).trans infinityBaseResidueRingEquivF2)
    yzInfinityResidueRingEquivF2

/-- The actual inertia degree over the reciprocal polynomial base is one. -/
theorem zInfinityPrime_inertiaDeg_eq_one : zInfinityPrime.inertiaDeg' BasePolynomial = 1 :=
  inertiaDeg_eq_one_of_binary_ringEquivs (A := BasePolynomial) zInfinityPrime
    ((residueRingEquivOfEq zInfinityPrime_under).trans infinityBaseResidueRingEquivF2)
    zInfinityResidueRingEquivF2

end MazurProof.N25F_InfinityResidueFields
