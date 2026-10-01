import FLT.Assumptions.MazurProof.N18RouteC_FieldArithmetic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The prime above three and its discrete valuation

The prime `(pi)` is the unique prime above `3`, with ramification index
three.  This file fixes the actual height-one-spectrum object used by the
formal-kernel filtration.
-/

namespace MazurProof.N18RouteC.ThreeAdic

open Polynomial FieldArithmetic
open scoped NumberField

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

theorem one_sub_pi_sq_mul_inverse :
    (1 - pi ^ 2) * (pi ^ 2 + 3 * pi + 1) = 1 := by
  have hpi4 : pi ^ 4 = 3 * pi - 3 * pi ^ 3 := by
    linear_combination pi * pi_relation
  ring_nf
  rw [hpi4, pi_cubed]
  ring

def oneSubPiSqInteger : OL :=
  ⟨1 - pi ^ 2, isIntegral_one.sub (pi_isIntegral.pow 2)⟩

def oneSubPiSqUnit : OLˣ where
  val := oneSubPiSqInteger
  inv := ⟨pi ^ 2 + 3 * pi + 1,
    ((pi_isIntegral.pow 2).add
      ((isIntegral_natCast 3).mul pi_isIntegral)).add isIntegral_one⟩
  val_inv := Subtype.ext one_sub_pi_sq_mul_inverse
  inv_val := Subtype.ext (by rw [mul_comm]; exact one_sub_pi_sq_mul_inverse)

theorem three_eq_pi_cubed_mul_inverse :
    (3 : L) = pi ^ 3 * (pi ^ 2 + 3 * pi + 1) := by
  calc
    (3 : L) = 3 * ((1 - pi ^ 2) * (pi ^ 2 + 3 * pi + 1)) := by
      rw [one_sub_pi_sq_mul_inverse, mul_one]
    _ = pi ^ 3 * (pi ^ 2 + 3 * pi + 1) := by
      rw [← mul_assoc, three_mul_one_sub_pi_sq]

def cubicModThree : (ZMod 3)[X] :=
  cubicPolyInt.map (Int.castRingHom (ZMod 3))

theorem cubicModThree_eq : cubicModThree = X ^ 3 := by
  norm_num [cubicModThree, cubicPolyInt]
  have hthree : (3 : (ZMod 3)[X]) = 0 := by
    rw [← Polynomial.C_ofNat 3, show (3 : ZMod 3) = 0 by decide]
    simp
  rw [hthree]
  ring

theorem monicFactorsMod_three :
    RingOfIntegers.monicFactorsMod piInteger 3 = {X} := by
  simp only [RingOfIntegers.monicFactorsMod, minpoly_piInteger]
  rw [show cubicPolyInt.map (Int.castRingHom (ZMod 3)) = cubicModThree by rfl,
    cubicModThree_eq]
  simp [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Polynomial.irreducible_X : Irreducible (X : (ZMod 3)[X])),
    Polynomial.Monic.normalize_eq_self (Polynomial.monic_X :
      Monic (X : (ZMod 3)[X]))]

theorem X_mem_monicFactorsMod_three :
    (X : (ZMod 3)[X]) ∈ RingOfIntegers.monicFactorsMod piInteger 3 := by
  rw [monicFactorsMod_three]
  simp

private theorem three_not_dvd_exponent :
    ¬ (3 : ℕ) ∣ RingOfIntegers.exponent piInteger := by
  rw [piInteger_exponent_eq_one]
  norm_num

def primeAboveThree : Ideal OL :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := L) (p := 3) three_not_dvd_exponent).symm
    ⟨X, X_mem_monicFactorsMod_three⟩ : Ideal OL)

theorem primeAboveThree_eq_span_pair :
    primeAboveThree = Ideal.span ({(3 : OL), piInteger} : Set OL) := by
  have hspan :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
      (K := L) (p := 3) (Q := (X : ℤ[X])) three_not_dvd_exponent
      (by simpa using X_mem_monicFactorsMod_three)
  simpa [primeAboveThree, aeval_X] using hspan

theorem three_mem_span_pi : (3 : OL) ∈ Ideal.span ({piInteger} : Set OL) := by
  rw [Ideal.mem_span_singleton]
  refine ⟨⟨pi ^ 2 * (pi ^ 2 + 3 * pi + 1),
    (pi_isIntegral.pow 2).mul
      (((pi_isIntegral.pow 2).add
        ((isIntegral_natCast 3).mul pi_isIntegral)).add
          isIntegral_one)⟩, ?_⟩
  apply Subtype.ext
  change (3 : L) = pi * (pi ^ 2 * (pi ^ 2 + 3 * pi + 1))
  calc
    (3 : L) = pi ^ 3 * (pi ^ 2 + 3 * pi + 1) :=
      three_eq_pi_cubed_mul_inverse
    _ = pi * (pi ^ 2 * (pi ^ 2 + 3 * pi + 1)) := by ring

theorem primeAboveThree_eq_span_pi :
    primeAboveThree = Ideal.span ({piInteger} : Set OL) := by
  rw [primeAboveThree_eq_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact three_mem_span_pi
    · exact Ideal.subset_span (Set.mem_singleton piInteger)
  · apply Ideal.span_mono
    exact Set.singleton_subset_iff.mpr (by simp)

theorem primeAboveThree_mem :
    primeAboveThree ∈
      Ideal.primesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) OL :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := L) (p := 3) three_not_dvd_exponent).symm
    ⟨X, X_mem_monicFactorsMod_three⟩).property

theorem primeAboveThree_isPrime : primeAboveThree.IsPrime := primeAboveThree_mem.1

theorem primeAboveThree_ne_bot : primeAboveThree ≠ ⊥ := by
  rw [primeAboveThree_eq_span_pi, ne_eq, Ideal.span_singleton_eq_bot]
  intro hpi
  have hpiL := congrArg (fun z : OL ↦ (z : L)) hpi
  simp only [piInteger_coe_L, map_zero] at hpiL
  have hrel := pi_relation
  rw [hpiL] at hrel
  norm_num at hrel

def p3 : IsDedekindDomain.HeightOneSpectrum OL where
  asIdeal := primeAboveThree
  isPrime := primeAboveThree_isPrime
  ne_bot := primeAboveThree_ne_bot

def v3 := p3.valuation L

/-- Additive order, with the harmless junk value `0` at the field zero.
All filtration uses below supply a nonzero hypothesis. -/
def ordPi (x : L) : ℤ := -WithZero.log (v3 x)

theorem v3_pi : v3 pi = WithZero.exp (-1 : ℤ) := by
  rw [v3, ← piInteger_coe_L,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
  · intro hpi
    have hpiL := congrArg (fun z : OL ↦ (z : L)) hpi
    simp only [piInteger_coe_L, map_zero] at hpiL
    have hrel := pi_relation
    rw [hpiL] at hrel
    norm_num at hrel
  · exact primeAboveThree_eq_span_pi

theorem ordPi_pi : ordPi pi = 1 := by
  simp [ordPi, v3_pi]

theorem v3_three : v3 (3 : L) = WithZero.exp (-3 : ℤ) := by
  rw [show (3 : L) = pi ^ 3 * (pi ^ 2 + 3 * pi + 1) from
    three_eq_pi_cubed_mul_inverse]
  have hunit : v3 (pi ^ 2 + 3 * pi + 1) = 1 := by
    rw [v3, ← show ((((oneSubPiSqUnit⁻¹ : OLˣ) : OL)) : L) =
      pi ^ 2 + 3 * pi + 1 by rfl,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    letI : primeAboveThree.IsPrime := primeAboveThree_isPrime
    exact Ideal.notMem_of_isUnit primeAboveThree (oneSubPiSqUnit⁻¹).isUnit
  rw [map_mul, map_pow, v3_pi, hunit]
  rw [← WithZero.exp_nsmul]
  norm_num

theorem ordPi_three : ordPi (3 : L) = 3 := by
  simp [ordPi, v3_three]

end

end MazurProof.N18RouteC.ThreeAdic
