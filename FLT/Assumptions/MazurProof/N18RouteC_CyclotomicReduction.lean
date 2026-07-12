import FLT.Assumptions.MazurProof.N18RouteC_CyclotomicTwo

set_option maxHeartbeats 0

open scoped NumberField

namespace MazurProof.N18RouteC.CyclotomicReduction

open NumberField
open Cyclotomic CyclotomicValuation CyclotomicTwo

noncomputable section

def IntegralAtTwo (x : M) : Prop := p2.valuation M x ≤ 1

def Reduces (x : M) (r : k2) : Prop :=
  ∃ n : OM, ∃ d : p2.asIdeal.primeCompl,
    x * (algebraMap OM M d) = algebraMap OM M n ∧
      r * (algebraMap OM k2 d) = algebraMap OM k2 n

private theorem residue_den_ne_zero (d : p2.asIdeal.primeCompl) :
    algebraMap OM k2 d ≠ 0 := by
  rw [ne_eq, Ideal.algebraMap_residueField_eq_zero]
  exact d.property

theorem reduces_exists {x : M} (hx : IntegralAtTwo x) :
    ∃ r : k2, Reduces x r := by
  obtain ⟨n, d, hnd⟩ := p2.exists_primeCompl_mul_eq_of_integer x hx
  refine ⟨algebraMap OM k2 n / algebraMap OM k2 d, n, d, hnd, ?_⟩
  exact (div_mul_cancel₀ _ (residue_den_ne_zero d))

theorem reduces_unique {x : M} {r s : k2}
    (hr : Reduces x r) (hs : Reduces x s) : r = s := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  have hcrossM :
      algebraMap OM M (n * d') = algebraMap OM M (n' * d) := by
    simp only [map_mul]
    calc
      algebraMap OM M n * algebraMap OM M (d' : OM) =
          (x * algebraMap OM M (d : OM)) * algebraMap OM M (d' : OM) := by
            rw [hxd]
      _ = (x * algebraMap OM M (d' : OM)) * algebraMap OM M (d : OM) := by ring
      _ = algebraMap OM M n' * algebraMap OM M (d : OM) := by rw [hxd']
  have hcross : n * (d' : OM) = n' * (d : OM) :=
    (FaithfulSMul.algebraMap_injective OM M) hcrossM
  apply mul_right_cancel₀
    (mul_ne_zero (residue_den_ne_zero d) (residue_den_ne_zero d'))
  calc
    r * (algebraMap OM k2 d * algebraMap OM k2 d') =
        (r * algebraMap OM k2 d) * algebraMap OM k2 d' := by ring
    _ = algebraMap OM k2 n * algebraMap OM k2 d' := by rw [hrd]
    _ = algebraMap OM k2 (n * (d' : OM)) := by rw [map_mul]
    _ = algebraMap OM k2 (n' * (d : OM)) := by rw [hcross]
    _ = algebraMap OM k2 n' * algebraMap OM k2 d := by rw [map_mul]
    _ = (s * algebraMap OM k2 d') * algebraMap OM k2 d := by rw [hsd']
    _ = s * (algebraMap OM k2 d * algebraMap OM k2 d') := by ring

theorem reduces_existsUnique {x : M} (hx : IntegralAtTwo x) :
    ∃! r : k2, Reduces x r := by
  obtain ⟨r, hr⟩ := reduces_exists hx
  exact ⟨r, hr, fun s hs ↦
    (reduces_unique (x := x) (r := r) (s := s) hr hs).symm⟩

noncomputable def reduce (x : M) (hx : IntegralAtTwo x) : k2 :=
  Classical.choose (reduces_existsUnique hx)

theorem reduce_spec (x : M) (hx : IntegralAtTwo x) :
    Reduces x (reduce x hx) :=
  (Classical.choose_spec (reduces_existsUnique hx)).1

theorem reduce_eq_of_reduces {x : M} (hx : IntegralAtTwo x) {r : k2}
    (hr : Reduces x r) : reduce x hx = r :=
  reduces_unique (reduce_spec x hx) hr

theorem integralAtTwo_zero : IntegralAtTwo (0 : M) := by
  simp [IntegralAtTwo]

theorem integralAtTwo_one : IntegralAtTwo (1 : M) := by
  simp [IntegralAtTwo]

theorem IntegralAtTwo.add {x y : M}
    (hx : IntegralAtTwo x) (hy : IntegralAtTwo y) : IntegralAtTwo (x + y) := by
  exact (p2.valuation M).map_add x y |>.trans (max_le hx hy)

theorem IntegralAtTwo.neg {x : M} (hx : IntegralAtTwo x) :
    IntegralAtTwo (-x) := by simpa [IntegralAtTwo] using hx

theorem IntegralAtTwo.sub {x y : M}
    (hx : IntegralAtTwo x) (hy : IntegralAtTwo y) : IntegralAtTwo (x - y) := by
  simpa [sub_eq_add_neg] using
    IntegralAtTwo.add hx (IntegralAtTwo.neg hy)

theorem IntegralAtTwo.mul {x y : M}
    (hx : IntegralAtTwo x) (hy : IntegralAtTwo y) : IntegralAtTwo (x * y) := by
  unfold IntegralAtTwo at hx hy ⊢
  rw [map_mul]
  exact (mul_le_mul' hx hy).trans_eq (mul_one 1)

theorem IntegralAtTwo.pow {x : M} (hx : IntegralAtTwo x) (n : ℕ) :
    IntegralAtTwo (x ^ n) := by
  induction n with
  | zero => simpa using integralAtTwo_one
  | succ n ih => simpa [pow_succ] using ih.mul hx

theorem reduces_one : Reduces (1 : M) (1 : k2) := by
  refine ⟨1, 1, ?_, ?_⟩ <;> simp

theorem reduces_zero : Reduces (0 : M) (0 : k2) := by
  refine ⟨0, 1, ?_, ?_⟩ <;> simp

theorem Reduces.add {x y : M} {r s : k2}
    (hr : Reduces x r) (hs : Reduces y s) : Reduces (x + y) (r + s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * (d' : OM) + n' * (d : OM), d * d', ?_, ?_⟩
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (x + y) * (algebraMap OM M d * algebraMap OM M d') =
          (x * algebraMap OM M d) * algebraMap OM M d' +
            (y * algebraMap OM M d') * algebraMap OM M d := by ring
      _ = algebraMap OM M n * algebraMap OM M d' +
            algebraMap OM M n' * algebraMap OM M d := by rw [hxd, hxd']
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (r + s) * (algebraMap OM k2 d * algebraMap OM k2 d') =
          (r * algebraMap OM k2 d) * algebraMap OM k2 d' +
            (s * algebraMap OM k2 d') * algebraMap OM k2 d := by ring
      _ = algebraMap OM k2 n * algebraMap OM k2 d' +
            algebraMap OM k2 n' * algebraMap OM k2 d := by rw [hrd, hsd']

theorem Reduces.neg {x : M} {r : k2} (hr : Reduces x r) :
    Reduces (-x) (-r) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  refine ⟨-n, d, ?_, ?_⟩
  · simp only [map_neg]
    linear_combination -1 * hxd
  · simp only [map_neg]
    linear_combination -1 * hrd

theorem Reduces.mul {x y : M} {r s : k2}
    (hr : Reduces x r) (hs : Reduces y s) : Reduces (x * y) (r * s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * n', d * d', ?_, ?_⟩
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hxd, ← hxd']
    ring
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hrd, ← hsd']
    ring

theorem Reduces.pow {x : M} {r : k2} (hr : Reduces x r) (n : ℕ) :
    Reduces (x ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using reduces_one
  | succ n ih => simpa [pow_succ] using ih.mul hr

@[simp] theorem reduce_zero : reduce 0 integralAtTwo_zero = 0 :=
  reduce_eq_of_reduces integralAtTwo_zero reduces_zero

@[simp] theorem reduce_one : reduce 1 integralAtTwo_one = 1 :=
  reduce_eq_of_reduces integralAtTwo_one reduces_one

theorem reduce_add {x y : M} (hx : IntegralAtTwo x) (hy : IntegralAtTwo y) :
    reduce (x + y) (hx.add hy) = reduce x hx + reduce y hy :=
  reduce_eq_of_reduces (hx.add hy) ((reduce_spec x hx).add (reduce_spec y hy))

theorem reduce_neg {x : M} (hx : IntegralAtTwo x) :
    reduce (-x) hx.neg = -reduce x hx :=
  reduce_eq_of_reduces hx.neg (reduce_spec x hx).neg

theorem reduce_mul {x y : M} (hx : IntegralAtTwo x) (hy : IntegralAtTwo y) :
    reduce (x * y) (hx.mul hy) = reduce x hx * reduce y hy :=
  reduce_eq_of_reduces (hx.mul hy) ((reduce_spec x hx).mul (reduce_spec y hy))

theorem reduce_pow {x : M} (hx : IntegralAtTwo x) (n : ℕ) :
    reduce (x ^ n) (hx.pow n) = reduce x hx ^ n :=
  reduce_eq_of_reduces (hx.pow n) ((reduce_spec x hx).pow n)

theorem reduce_of_integer (n : OM) :
    reduce (algebraMap OM M n) (by
      simpa [IntegralAtTwo] using p2.valuation_le_one (K := M) n) =
      algebraMap OM k2 n := by
  apply reduce_eq_of_reduces
  refine ⟨n, 1, ?_, ?_⟩ <;> simp

theorem valuation_eq_exp_neg_ordAt {x : M} (hx : x ≠ 0) :
    p2.valuation M x = WithZero.exp (-ordAt p2 x) := by
  have hv : p2.valuation M x ≠ 0 :=
    (Valuation.ne_zero_iff (p2.valuation M)).2 hx
  calc
    p2.valuation M x = WithZero.exp (WithZero.log (p2.valuation M x)) :=
      (WithZero.exp_log hv).symm
    _ = WithZero.exp (-ordAt p2 x) := by
      congr 1
      simp [ordAt]

theorem integralAtTwo_of_ordAt_nonneg {x : M} (hx : x ≠ 0)
    (hord : 0 ≤ ordAt p2 x) : IntegralAtTwo x := by
  unfold IntegralAtTwo
  rw [valuation_eq_exp_neg_ordAt hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem valuation_eq_one_of_ordAt_eq_zero {x : M} (hx : x ≠ 0)
    (hord : ordAt p2 x = 0) : p2.valuation M x = 1 := by
  rw [valuation_eq_exp_neg_ordAt hx, hord]
  simp

theorem ordAt_zpow (x : M) (n : ℤ) :
    ordAt p2 (x ^ n) = n * ordAt p2 x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow]
  simp only [zsmul_eq_mul]
  simpa using
    (mul_neg n (WithZero.log (p2.valuation M x))).symm

theorem ordAt_two_zpow (n : ℤ) : ordAt p2 ((2 : M) ^ n) = n := by
  rw [ordAt_zpow, ordAt_p2_two]
  ring

theorem ordAt_two_zpow_mul {x : M} (hx : x ≠ 0) (n : ℤ) :
    ordAt p2 ((2 : M) ^ n * x) = n + ordAt p2 x := by
  rw [ordAt_mul p2 (zpow_ne_zero n (by norm_num : (2 : M) ≠ 0)) hx,
    ordAt_two_zpow]

theorem reduce_eq_zero_of_ordAt_pos {x : M} (hx : x ≠ 0)
    (hord : 0 < ordAt p2 x) :
    reduce x (integralAtTwo_of_ordAt_nonneg hx hord.le) = 0 := by
  let hxInt := integralAtTwo_of_ordAt_nonneg hx hord.le
  obtain ⟨n, d, hxd, hred⟩ := reduce_spec x hxInt
  have hdM : algebraMap OM M (d : OM) ≠ 0 :=
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective OM M)).not.mpr
      (fun hd ↦ d.property (hd ▸ Submodule.zero_mem _))
  have hdord : ordAt p2 (algebraMap OM M (d : OM)) = 0 := by
    have hv : p2.valuation M (algebraMap OM M (d : OM)) = 1 :=
      (p2.valuation_eq_one_iff_notMem (K := M)).2 d.property
    simp [ordAt, hv]
  have hnM : algebraMap OM M n ≠ 0 := by
    rw [← hxd]
    exact mul_ne_zero hx hdM
  have hnord : ordAt p2 (algebraMap OM M n) = ordAt p2 x := by
    rw [← hxd, ordAt_mul p2 hx hdM, hdord, add_zero]
  have hnmem : n ∈ p2.asIdeal :=
    mem_asIdeal_of_ordAt_algebraMap_ne_zero p2 n <| by
      rw [hnord]
      omega
  have hnbar : algebraMap OM k2 n = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hnmem
  rw [hnbar] at hred
  exact (mul_eq_zero.mp hred).resolve_right (residue_den_ne_zero d)

theorem reduce_ne_zero_of_ordAt_eq_zero {x : M} (hx : x ≠ 0)
    (hord : ordAt p2 x = 0) :
    reduce x (integralAtTwo_of_ordAt_nonneg hx (hord.ge)) ≠ 0 := by
  let hxInt := integralAtTwo_of_ordAt_nonneg hx hord.ge
  have hvx : p2.valuation M x = 1 :=
    valuation_eq_one_of_ordAt_eq_zero hx hord
  have hxInvInt : IntegralAtTwo x⁻¹ := by
    unfold IntegralAtTwo
    rw [map_inv₀, hvx, inv_one]
  let r := reduce x hxInt
  let s := reduce x⁻¹ hxInvInt
  have hrs : Reduces (1 : M) (r * s) := by
    simpa [r, s, mul_inv_cancel₀ hx] using
      (reduce_spec x hxInt).mul (reduce_spec x⁻¹ hxInvInt)
  have hrsOne : r * s = 1 := reduces_unique hrs reduces_one
  intro hr0
  change r = 0 at hr0
  rw [hr0, zero_mul] at hrsOne
  exact zero_ne_one hrsOne

@[simp] theorem conjRing_zetaInteger : conjRing zetaInteger = zetaInteger ^ 8 := by
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj M zeta = zeta ^ 8
  rw [complexConj_zeta]
  field_simp [zeta_ne_zero]
  simpa using zeta_primitive.pow_eq_one.symm

noncomputable def residueConjHom : OM →+* k2 :=
  (algebraMap OM k2).comp conjRing.toRingHom

noncomputable def residueFrobEightHom : OM →+* k2 :=
  (iterateFrobenius k2 2 3).comp (algebraMap OM k2)

theorem residueConjHom_eq_frobEight :
    residueConjHom = residueFrobEightHom := by
  letI : Algebra ℤ k2 := Ring.toIntAlgebra k2
  apply RingHom.toIntAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.Rat.adjoin_singleton_eq_top zeta_primitive)
  rw [Set.eqOn_singleton]
  change algebraMap OM k2 (conjRing zetaInteger) =
    (algebraMap OM k2 zetaInteger) ^ 8
  rw [conjRing_zetaInteger, map_pow]

theorem residue_conjRing (A : OM) :
    algebraMap OM k2 (conjRing A) = (algebraMap OM k2 A) ^ 8 := by
  have h := DFunLike.congr_fun residueConjHom_eq_frobEight A
  simpa [residueConjHom, residueFrobEightHom, iterateFrobenius_def] using h

theorem conjRing_not_mem_p2 {A : OM} (hA : A ∉ p2.asIdeal) :
    conjRing A ∉ p2.asIdeal := by
  rw [p2_asIdeal, Ideal.mem_span_singleton] at hA ⊢
  intro hdiv
  apply hA
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨conjRing b, ?_⟩
  have hc := congrArg conjRing hb
  have htwo : conjRing (2 : OM) = 2 := map_natCast conjRing.toRingHom 2
  simpa only [map_mul, conjRing_involutive, htwo] using hc

def conjPrimeCompl (d : p2.asIdeal.primeCompl) : p2.asIdeal.primeCompl :=
  ⟨conjRing d, conjRing_not_mem_p2 d.property⟩

theorem reduce_pow_eight_of_complexConj_eq {x : M}
    (hxInt : IntegralAtTwo x)
    (hfix : NumberField.IsCMField.complexConj M x = x) :
    reduce x hxInt ^ 8 = reduce x hxInt := by
  let r := reduce x hxInt
  obtain ⟨n, d, hxd, hrd⟩ := reduce_spec x hxInt
  let dC := conjPrimeCompl d
  have hxdC :
      x * algebraMap OM M (dC : OM) = algebraMap OM M (conjRing n) := by
    have hc := congrArg (NumberField.IsCMField.complexConj M) hxd
    simpa [dC, conjPrimeCompl, hfix, conjRing_coe] using hc
  have hrdC :
      r ^ 8 * algebraMap OM k2 (dC : OM) =
        algebraMap OM k2 (conjRing n) := by
    have hp := congrArg (fun z : k2 ↦ z ^ 8) hrd
    rw [mul_pow] at hp
    simpa [dC, conjPrimeCompl, residue_conjRing] using hp
  have hrC : Reduces x (r ^ 8) := ⟨conjRing n, dC, hxdC, hrdC⟩
  exact reduces_unique hrC (reduce_spec x hxInt)

theorem reduce_pow_seven_eq_one_of_complexConj_eq {x : M}
    (hx : x ≠ 0) (hord : ordAt p2 x = 0)
    (hfix : NumberField.IsCMField.complexConj M x = x) :
    reduce x (integralAtTwo_of_ordAt_nonneg hx hord.ge) ^ 7 = 1 := by
  let hxInt := integralAtTwo_of_ordAt_nonneg hx hord.ge
  let r := reduce x hxInt
  have hr8 : r ^ 8 = r := reduce_pow_eight_of_complexConj_eq hxInt hfix
  have hr0 : r ≠ 0 := reduce_ne_zero_of_ordAt_eq_zero hx hord
  apply mul_left_cancel₀ hr0
  simpa [r, ← pow_succ'] using hr8

theorem two_prime_OM : Prime (2 : OM) := by
  apply Ideal.prime_span_singleton_iff.mp
  rw [← p2_asIdeal]
  exact (Ideal.prime_iff_isPrime p2.ne_bot).2 p2.isPrime

theorem two_irreducible_OM : Irreducible (2 : OM) :=
  two_prime_OM.irreducible

@[simp] theorem conjRing_two : conjRing (2 : OM) = 2 := by
  exact map_natCast conjRing.toRingHom 2

theorem multiplicity_two_conjRing (A : OM) :
    multiplicity (2 : OM) (conjRing A) = multiplicity (2 : OM) A := by
  have hmap := multiplicity_map_eq conjRing (a := (2 : OM)) (b := A)
  simpa [conjRing_involutive] using hmap

theorem ordAt_p2_algebraMap_eq_multiplicity (A : OM) (hA : A ≠ 0) :
    ordAt p2 (algebraMap OM M A) = multiplicity (2 : OM) A := by
  unfold ordAt
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hA]
  rw [p2_asIdeal]
  change -(WithZero.log
    (WithZero.exp (-((multiplicity (Ideal.span {(2 : OM)})
      (Ideal.span {A}) : ℕ) : ℤ)))) = _
  rw [ideal_multiplicity_span_eq (2 : OM) A two_irreducible_OM hA]
  simp

theorem ordAt_p2_fraction_eq {A B : OM} (hA : A ≠ 0) (hB : B ≠ 0) :
    ordAt p2 (algebraMap OM M A / algebraMap OM M B) =
      (multiplicity (2 : OM) A : ℤ) - multiplicity (2 : OM) B := by
  rw [ordAt_div]
  · rw [ordAt_p2_algebraMap_eq_multiplicity A hA,
      ordAt_p2_algebraMap_eq_multiplicity B hB]
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hA
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hB

theorem ordAt_p2_complexConj {x : M} (hx : x ≠ 0) :
    ordAt p2 (NumberField.IsCMField.complexConj M x) = ordAt p2 x := by
  obtain ⟨A, B, hBmem, hAB⟩ := IsFractionRing.div_surjective OM x
  have hB : B ≠ 0 := nonZeroDivisors.ne_zero hBmem
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_div] at hAB
    exact hx hAB.symm
  have hxAB : x = algebraMap OM M A / algebraMap OM M B := hAB.symm
  have hconjAB :
      NumberField.IsCMField.complexConj M x =
        algebraMap OM M (conjRing A) / algebraMap OM M (conjRing B) := by
    rw [hxAB, map_div₀]
    congr 1 <;> rfl
  have hconjA : conjRing A ≠ 0 := by simpa using conjRing.injective.ne hA
  have hconjB : conjRing B ≠ 0 := by simpa using conjRing.injective.ne hB
  rw [hconjAB, hxAB, ordAt_p2_fraction_eq hconjA hconjB,
    ordAt_p2_fraction_eq hA hB]
  simp only [multiplicity_two_conjRing]

end

end MazurProof.N18RouteC.CyclotomicReduction
