import FLT.Assumptions.MazurProof.N18RouteC_CyclotomicValuation
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

open scoped NumberField

namespace MazurProof.N18RouteC.CyclotomicTwo

open Polynomial NumberField
open Cyclotomic CyclotomicUnits CyclotomicValuation

noncomputable section

def zetaInteger : OM := zeta_primitive.toInteger

@[simp] theorem zetaInteger_coe_M : ((zetaInteger : OM) : M) = zeta := rfl

theorem zetaInteger_minpoly : minpoly ℤ zetaInteger = cyclotomic 9 ℤ := by
  simpa [zetaInteger] using
    (RingOfIntegers.minpoly_coe zeta_primitive.toInteger).symm.trans
      (cyclotomic_eq_minpoly zeta_primitive (by norm_num)).symm

def cycloNineModTwo : (ZMod 2)[X] := X ^ 6 + X ^ 3 + 1

theorem cycloNineModTwo_eq :
    (cyclotomic 9 ℤ).map (Int.castRingHom (ZMod 2)) = cycloNineModTwo := by
  rw [show cyclotomic 9 ℤ = X ^ 6 + X ^ 3 + 1 by
    calc
      cyclotomic 9 ℤ = 1 + X ^ 3 + (X ^ 3) ^ 2 := by
        simpa [Finset.sum_range_succ] using
          (cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) Nat.prime_three)
      _ = X ^ 6 + X ^ 3 + 1 := by ring]
  simp [cycloNineModTwo]

theorem cycloNineModTwo_eq_cyclotomic :
    cycloNineModTwo = cyclotomic 9 (ZMod 2) := by
  rw [← map_cyclotomic_int]
  exact cycloNineModTwo_eq.symm

theorem cycloNineModTwo_monic : cycloNineModTwo.Monic := by
  rw [cycloNineModTwo]
  monicity!

theorem cycloNineModTwo_irreducible : Irreducible cycloNineModTwo := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree
      (p := 2) (n := 9) (by norm_num)
  · rw [cycloNineModTwo_eq_cyclotomic]
  · have hdeg : cycloNineModTwo.natDegree = 6 := by
      rw [cycloNineModTwo]
      compute_degree <;> norm_num
    have hroot : IsPrimitiveRoot ((2 : ℕ) : ZMod 9) 6 := by
      apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide)
      intro l hl hlt
      interval_cases l <;> decide
    rw [hdeg]
    calc
      6 = orderOf ((2 : ℕ) : ZMod 9) := hroot.eq_orderOf
      _ = orderOf (ZMod.unitOfCoprime 2
          (Nat.prime_two.coprime_iff_not_dvd.mpr (by norm_num : ¬2 ∣ 9))) := by
        simpa using (orderOf_injective _ Units.coeHom_injective
          (ZMod.unitOfCoprime 2
            (Nat.prime_two.coprime_iff_not_dvd.mpr (by norm_num : ¬2 ∣ 9))))

theorem monicFactorsMod_two :
    RingOfIntegers.monicFactorsMod zetaInteger 2 = {cycloNineModTwo} := by
  simp only [RingOfIntegers.monicFactorsMod, zetaInteger_minpoly]
  rw [cycloNineModTwo_eq,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      cycloNineModTwo_irreducible]
  rw [cycloNineModTwo_monic.normalize_eq_self]
  rfl

theorem cycloNineModTwo_mem :
    cycloNineModTwo ∈ RingOfIntegers.monicFactorsMod zetaInteger 2 := by
  rw [monicFactorsMod_two]
  simp

private theorem two_not_dvd_exponent :
    ¬ (2 : ℕ) ∣ RingOfIntegers.exponent zetaInteger := by
  change ¬(2 : ℕ) ∣ RingOfIntegers.exponent zeta_primitive.toInteger
  rw [RingOfIntegers.exponent_eq_one_iff.mpr <|
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top zeta_primitive]
  norm_num

def primeAboveTwo : Ideal OM :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := M) (p := 2) two_not_dvd_exponent).symm
    ⟨cycloNineModTwo, cycloNineModTwo_mem⟩ : Ideal OM)

theorem primeAboveTwo_eq_span_two :
    primeAboveTwo = Ideal.span ({(2 : OM)} : Set OM) := by
  have hspan :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
      (K := M) (p := 2) (Q := cyclotomic 9 ℤ) two_not_dvd_exponent
      (by rw [cycloNineModTwo_eq]
          exact cycloNineModTwo_mem)
  have heval : aeval zetaInteger (cyclotomic 9 ℤ) = 0 := by
    rw [← zetaInteger_minpoly]
    exact minpoly.aeval ℤ zetaInteger
  simpa [primeAboveTwo, cycloNineModTwo_eq_cyclotomic, heval] using hspan

theorem primeAboveTwo_mem :
    primeAboveTwo ∈
      Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) OM :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := M) (p := 2) two_not_dvd_exponent).symm
    ⟨cycloNineModTwo, cycloNineModTwo_mem⟩).property

def p2 : IsDedekindDomain.HeightOneSpectrum OM where
  asIdeal := primeAboveTwo
  isPrime := primeAboveTwo_mem.1
  ne_bot := by
    rw [primeAboveTwo_eq_span_two, ne_eq, Ideal.span_singleton_eq_bot]
    norm_num

theorem p2_asIdeal : p2.asIdeal = Ideal.span ({(2 : OM)} : Set OM) :=
  primeAboveTwo_eq_span_two

theorem ordAt_p2_two : ordAt p2 (2 : M) = 1 := by
  unfold ordAt
  rw [← show (((2 : OM) : M)) = (2 : M) by rfl,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton]
  · simp
  · norm_num
  · exact p2_asIdeal

theorem inertiaDeg_p2 :
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg p2.asIdeal = 6 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : p2.asIdeal.IsPrime := p2.isPrime
  letI : p2.asIdeal.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    primeAboveTwo_mem.2
  have hf := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (p := 2) (m := 9) (K := M) (P := p2.asIdeal) (by norm_num)
  have hroot : IsPrimitiveRoot ((2 : ℕ) : ZMod 9) 6 := by
    apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide)
    intro l hl hlt
    interval_cases l <;> decide
  calc
    (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg p2.asIdeal =
        orderOf ((2 : ℕ) : ZMod 9) := by simpa using hf
    _ = 6 := hroot.eq_orderOf.symm

theorem absNorm_p2 : Ideal.absNorm p2.asIdeal = 64 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : p2.asIdeal.IsPrime := p2.isPrime
  letI : p2.asIdeal.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    primeAboveTwo_mem.2
  rw [Ideal.absNorm_eq_pow_inertiaDeg' p2.asIdeal Nat.prime_two]
  have hdeg :
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg p2.asIdeal = 6 :=
    inertiaDeg_p2
  rw [show (Ideal.span ({((2 : ℕ) : ℤ)} : Set ℤ)).inertiaDeg p2.asIdeal = 6 by
    simpa using hdeg]
  norm_num

abbrev k2 := p2.asIdeal.ResidueField

noncomputable instance finite_k2 : Finite k2 := by
  letI : p2.asIdeal.IsPrime := p2.isPrime
  letI : p2.asIdeal.IsMaximal := p2.isMaximal
  apply Finite.of_surjective (algebraMap (OM ⧸ p2.asIdeal) k2)
  exact p2.asIdeal.bijective_algebraMap_quotient_residueField.surjective

theorem natCard_k2 : Nat.card k2 = 64 := by
  letI : p2.asIdeal.IsPrime := p2.isPrime
  letI : p2.asIdeal.IsMaximal := p2.isMaximal
  let f := algebraMap (OM ⧸ p2.asIdeal) k2
  let e : (OM ⧸ p2.asIdeal) ≃ k2 :=
    Equiv.ofBijective f p2.asIdeal.bijective_algebraMap_quotient_residueField
  calc
    Nat.card k2 = Nat.card (OM ⧸ p2.asIdeal) :=
      (Nat.card_congr e).symm
    _ = Ideal.absNorm p2.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = 64 := absNorm_p2

noncomputable instance charP_k2 : CharP k2 2 := by
  letI : Fintype k2 := Fintype.ofFinite k2
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply charP_of_card_eq_prime_pow (p := 2) (f := 6)
  rw [← Nat.card_eq_fintype_card, natCard_k2]
  norm_num

noncomputable def zetaBar : k2 := algebraMap OM k2 zetaInteger

theorem zetaBar_pow_nine : zetaBar ^ 9 = 1 := by
  rw [zetaBar, ← map_pow, show zetaInteger ^ 9 = 1 by
    apply NumberField.RingOfIntegers.ext
    simpa [zetaInteger] using zeta_primitive.pow_eq_one]
  simp

theorem zetaBar_pow_three_ne_one : zetaBar ^ 3 ≠ 1 := by
  intro hz3
  have hsum : zetaBar ^ 6 + zetaBar ^ 3 + 1 = 0 := by
    have hrel : zetaInteger ^ 6 + zetaInteger ^ 3 + 1 = 0 := by
      apply NumberField.RingOfIntegers.ext
      simpa [zetaInteger] using zeta_cubic_sum
    have hmap := congrArg (algebraMap OM k2) hrel
    simpa only [zetaBar, map_add, map_pow, map_one, map_zero] using hmap
  rw [show zetaBar ^ 6 = (zetaBar ^ 3) ^ 2 by ring, hz3] at hsum
  have htwo : (2 : k2) = 0 := by
    have hmap : algebraMap OM k2 (2 : OM) = 0 := by
      rw [Ideal.algebraMap_residueField_eq_zero, p2_asIdeal]
      exact Ideal.subset_span (Set.mem_singleton 2)
    simpa only [map_ofNat] using hmap
  have hone : (1 : k2) = 0 := by
    linear_combination hsum - htwo
  exact one_ne_zero hone

theorem zetaBar_pow_fin_three_eq_one_iff (e : Fin 3) :
    zetaBar ^ (3 * e.val) = 1 ↔ e = 0 := by
  fin_cases e
  · simp
  · simp only [Fin.isValue, Fin.val_one, mul_one]
    exact ⟨fun h ↦ (zetaBar_pow_three_ne_one h).elim, by simp⟩
  · simp only [Fin.isValue]
    constructor
    · intro h6
      norm_num at h6
      have h9 := zetaBar_pow_nine
      rw [show zetaBar ^ 9 = zetaBar ^ 6 * zetaBar ^ 3 by ring,
        h6, one_mul] at h9
      have h3 : zetaBar ^ 3 = 1 := h9
      exact (zetaBar_pow_three_ne_one h3).elim
    · simp

theorem zetaBar_mul_cube_pow_twenty_one
    (e : Fin 3) (d : k2) (hd : d ≠ 0) :
    (zetaBar ^ e.val * d ^ 3) ^ 21 = zetaBar ^ (3 * e.val) := by
  letI : Fintype k2 := Fintype.ofFinite k2
  have hcard : Fintype.card k2 = 64 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_k2
  have hd63 := FiniteField.pow_card_sub_one_eq_one d hd
  rw [hcard] at hd63
  calc
    (zetaBar ^ e.val * d ^ 3) ^ 21 =
        zetaBar ^ (21 * e.val) * d ^ 63 := by ring
    _ = zetaBar ^ (3 * e.val) := by
      rw [hd63, mul_one]
      conv_lhs => rw [show 21 * e.val = 9 * (2 * e.val) + 3 * e.val by omega]
      rw [pow_add]
      have hzblock : zetaBar ^ (9 * (2 * e.val)) = 1 := by
        rw [pow_mul, zetaBar_pow_nine, one_pow]
      rw [hzblock, one_mul]

end

end MazurProof.N18RouteC.CyclotomicTwo
