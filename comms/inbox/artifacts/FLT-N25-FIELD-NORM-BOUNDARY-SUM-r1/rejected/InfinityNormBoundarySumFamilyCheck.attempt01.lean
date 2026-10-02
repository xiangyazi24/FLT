import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! Normalized ideal-factor counts are the genuine length orders at the
corresponding Dedekind localizations. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_LocalFactorOrder
open UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Local quotient length reads exactly the chosen prime-factor multiplicity. -/
theorem local_length_eq_factor_count (I : Ideal R) (hI : I ≠ ⊥)
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) =
      (normalizedFactors I).count p := by
  classical
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp
      (Localization.AtPrime p)
  obtain ⟨J, hcop, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI p
  have hnot : ¬ J ≤ p := by
    intro hle
    rw [sup_of_le_left hle] at hcop
    exact (inferInstance : p.IsPrime).ne_top hcop
  have hm : I.map (algebraMap R (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ (normalizedFactors I).count p := by
    conv_lhs => rw [hfac]
    rw [Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime p) hnot,
      Ideal.mul_top, Localization.AtPrime.map_eq_maximalIdeal]
  rw [hm, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- The actual order of a nonzero regular function is its principal ideal's
normalized-factor count, with no assumed valuation compatibility. -/
theorem ord_algebraMap_eq_factor_count (a : R) (ha : a ≠ 0)
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
      (normalizedFactors (Ideal.span {a})).count p := by
  have h := local_length_eq_factor_count (Ideal.span {a})
    (Ideal.span_singleton_eq_bot.not.mpr ha) p hp
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h

end MazurProof.N25F_LocalFactorOrder

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_FractionOrderDifference

/-- Compute the genuine signed fraction-field order using quotient lengths. -/
theorem log_ordFrac_div {R L : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R L a / algebraMap R L b)) =
      ((Ring.ord R a).toNat : ℤ) - ((Ring.ord R b).toNat : ℤ) := by
  have he (c : R) (hc : c ≠ 0) :
      Ring.ordFrac R (algebraMap R L c) =
        WithZero.exp ((Ring.ord R c).toNat : ℤ) := by
    have hc' : c ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hc
    rw [Ring.ordFrac_eq_ord R hc,
      Ring.ordMonoidWithZeroHom_eq_coe R hc'
        (ENat.coe_toNat (Ring.ord_ne_top hc')).symm]
    rfl
  rw [map_div₀, he a ha, he b hb, ← WithZero.exp_sub, WithZero.log_exp]

end MazurProof.N25F_FractionOrderDifference

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



variable {A N L : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing N] [IsDedekindDomain N] [Algebra A N]
  [Module.Finite A N] [Module.IsTorsionFree A N]
  [Field L] [Algebra A L] [Algebra N L] [IsScalarTower A N L]
  [IsIntegralClosure N A L] [IsFractionRing N L]
  [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
  [FiniteDimensional (FractionRing A) L]

namespace MazurProof.N25F_InfinityNormFraction
/-- Integral and fixed-field norms agree under the exact reciprocal action. -/
theorem infinity_norm_normalization (a : N) :
    Algebra.norm (FractionRing A) (algebraMap N L a) =
      algebraMap A (FractionRing A) (Algebra.intNorm A N a) :=
  (Algebra.algebraMap_intNorm (A := A) (B := N)
    (K := (FractionRing A)) (L := L) a).symm

/-- The norm of a normalization fraction is the quotient of its integral norms. -/
theorem infinity_norm_fraction (a b : N) :
    Algebra.norm (FractionRing A) ((algebraMap N L a) / (algebraMap N L b)) =
      algebraMap A (FractionRing A) (Algebra.intNorm A N a) /
      algebraMap A (FractionRing A) (Algebra.intNorm A N b) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    infinity_norm_normalization, infinity_norm_normalization, ← div_eq_mul_inv]

/-- Every nonzero function admits nonzero numerator and denominator in the
actual reciprocal normalization, inside the same fixed function field. -/
theorem exists_normalization_fraction (f : L) (hf : f ≠ 0) :
    ∃ a b : N, a ≠ 0 ∧ b ≠ 0 ∧
      f = (algebraMap N L a) / (algebraMap N L b) := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective N f
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div] at h
    exact hf h.symm
  exact ⟨a, b, ha, mem_nonZeroDivisors_iff_ne_zero.mp hb, h.symm⟩

end MazurProof.N25F_InfinityNormFraction

namespace MazurProof.N25F_InfinityNormBoundarySum
open UniqueFactorizationMonoid N25F_LocalFactorOrder N25F_LocalFractionFactorOrder N25F_InfinityNormFraction
variable (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
variable (x y z : Ideal N) [x.IsPrime] [y.IsPrime] [z.IsPrime]
variable (hx : x ≠ ⊥) (hy : y ≠ ⊥) (hz : z ≠ ⊥)
variable (hmult : ∀ I : Ideal N, I ≠ ⊥ →
  (normalizedFactors (Ideal.relNorm A I)).count p =
  (normalizedFactors I).count x + (normalizedFactors I).count y + (normalizedFactors I).count z)
variable (xBoundaryOrder yzBoundaryOrder zBoundaryOrder : Additive Lˣ → ℤ)
variable (hxf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  xBoundaryOrder f = ((Ring.ord (Localization.AtPrime x)
    (algebraMap N (Localization.AtPrime x) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime x) (algebraMap N (Localization.AtPrime x) b)).toNat : ℤ))
variable (hyf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  yzBoundaryOrder f = ((Ring.ord (Localization.AtPrime y)
    (algebraMap N (Localization.AtPrime y) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime y) (algebraMap N (Localization.AtPrime y) b)).toNat : ℤ))
variable (hzf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  zBoundaryOrder f = ((Ring.ord (Localization.AtPrime z)
    (algebraMap N (Localization.AtPrime z) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime z) (algebraMap N (Localization.AtPrime z) b)).toNat : ℤ))
/-- The genuine fraction-field order at the actual reciprocal base prime (T). -/
def infinityBaseFractionOrder : (FractionRing A) →*₀ WithZero (Multiplicative ℤ) :=
  Ring.ordFrac (Localization.AtPrime p)

private theorem infinity_intNorm_ne_zero (a : N) (ha : a ≠ 0) :
    Algebra.intNorm A N a ≠ 0 := by
  have hI : (Ideal.span {a} : Ideal N) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  have hN : Ideal.relNorm A (Ideal.span {a}) ≠ ⊥ :=
    Ideal.relNorm_eq_bot_iff.not.mpr hI
  rw [Ideal.relNorm_singleton] at hN
  exact Ideal.span_singleton_eq_bot.not.mp hN

include hp hx hy hz hmult hxf hyf hzf in
/-- For the fixed function and exact reciprocal base action, the order of
its field norm is the sum of its genuine signed X, YZ and Z boundary orders. -/
theorem infinity_norm_boundary_order_sum (f : Additive Lˣ) :
    WithZero.log (infinityBaseFractionOrder p (Algebra.norm (FractionRing A) (f.toMul : L))) =
      xBoundaryOrder f + yzBoundaryOrder f + zBoundaryOrder f := by
  obtain ⟨a, b, ha, hb, hf⟩ := exists_normalization_fraction (f.toMul : L) (Units.ne_zero _)
  rw [hxf a b ha hb f hf,
    hyf a b ha hb f hf,
    hzf a b ha hb f hf]
  rw [hf, infinity_norm_fraction]
  change WithZero.log (Ring.ordFrac (Localization.AtPrime p)
    (algebraMap A (FractionRing A) (Algebra.intNorm A N a) /
      algebraMap A (FractionRing A) (Algebra.intNorm A N b))) = _
  rw [log_ordFrac_atPrime_div p hp _ _
    (infinity_intNorm_ne_zero a ha) (infinity_intNorm_ne_zero b hb)]
  rw [ord_algebraMap_eq_factor_count a ha _ hx,
    ord_algebraMap_eq_factor_count b hb _ hx,
    ord_algebraMap_eq_factor_count a ha _ hy,
    ord_algebraMap_eq_factor_count b hb _ hy,
    ord_algebraMap_eq_factor_count a ha _ hz,
    ord_algebraMap_eq_factor_count b hb _ hz]
  simp only [ENat.toNat_coe]
  have hma := hmult (Ideal.span {a}) (Ideal.span_singleton_eq_bot.not.mpr ha)
  have hmb := hmult (Ideal.span {b}) (Ideal.span_singleton_eq_bot.not.mpr hb)
  rw [Ideal.relNorm_singleton] at hma hmb
  rw [hma, hmb]
  simp only [Nat.cast_add]
  omega


#print axioms MazurProof.N25F_InfinityNormFraction.infinity_norm_normalization
#print axioms MazurProof.N25F_InfinityNormFraction.infinity_norm_fraction
#print axioms MazurProof.N25F_InfinityNormFraction.exists_normalization_fraction
#print axioms MazurProof.N25F_LocalFractionFactorOrder.log_ordFrac_atPrime_div
#print axioms infinityBaseFractionOrder
#print axioms infinity_norm_boundary_order_sum
end MazurProof.N25F_InfinityNormBoundarySum
