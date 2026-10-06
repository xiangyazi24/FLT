import FLT.Assumptions.MazurProof.N25F_LocalFactorOrder
import FLT.Assumptions.MazurProof.N25F_FractionOrderDifference
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The signed order at a Dedekind prime of a fraction in its canonical
fraction field is its numerator multiplicity minus its denominator multiplicity. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_LocalFractionFactorOrder
open UniqueFactorizationMonoid N25F_LocalFactorOrder N25F_FractionOrderDifference

theorem log_ordFrac_atPrime_div {A : Type*} [CommRing A] [IsDedekindDomain A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac (Localization.AtPrime p)
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) =
      ((normalizedFactors (Ideal.span {a})).count p : ℤ) -
      ((normalizedFactors (Ideal.span {b})).count p : ℤ) := by
  have hi := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have ha' : algebraMap A (Localization.AtPrime p) a ≠ 0 := (map_ne_zero_iff _ hi).mpr ha
  have hb' : algebraMap A (Localization.AtPrime p) b ≠ 0 := (map_ne_zero_iff _ hi).mpr hb
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A),
    log_ordFrac_div _ _ ha' hb', ord_algebraMap_eq_factor_count a ha p hp,
    ord_algebraMap_eq_factor_count b hb p hp]
  simp only [ENat.toNat_coe]

end MazurProof.N25F_LocalFractionFactorOrder
