import FLT.Assumptions.MazurProof.N18RouteC_CyclotomicUnits
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

open scoped NumberField
open UniqueFactorizationMonoid

namespace MazurProof.N18RouteC.CyclotomicValuation

open Cyclotomic CyclotomicUnits NumberField

noncomputable section

def lambda : OM := zeta_primitive.toInteger - 1

theorem lambda_prime : Prime lambda := by
  letI : IsCyclotomicExtension {3 ^ (1 + 1)} ℚ M := by
    norm_num
    exact cycloM
  exact zeta_primitive.zeta_sub_one_prime_of_ne_two (p := 3) (k := 1)
    (by norm_num)

theorem lambda_irreducible : Irreducible lambda := lambda_prime.irreducible

noncomputable def conjRing : OM ≃+* OM :=
  (NumberField.IsCMField.ringOfIntegersComplexConj M).toRingEquiv

@[simp] theorem conjRing_coe (x : OM) :
    ((conjRing x : OM) : M) =
      NumberField.IsCMField.complexConj M (x : M) := rfl

@[simp] theorem conjRing_involutive (x : OM) :
    conjRing (conjRing x) = x := by
  apply NumberField.RingOfIntegers.ext
  simp

theorem conjRing_lambda_associated : Associated (conjRing lambda) lambda := by
  let u : OMˣ := -zetaUnit
  refine ⟨u, ?_⟩
  apply NumberField.RingOfIntegers.ext
  change NumberField.IsCMField.complexConj M (zeta - 1) *
    (((u : OM) : M)) = zeta - 1
  rw [map_sub, complexConj_zeta, map_one]
  dsimp [u]
  push_cast
  simp only [zetaUnit_coe_M]
  field_simp [zeta_ne_zero]
  ring

theorem multiplicity_conjRing (A : OM) :
    multiplicity lambda (conjRing A) = multiplicity lambda A := by
  have hmap := multiplicity_map_eq conjRing (a := conjRing lambda) (b := A)
  have hassoc :
      multiplicity (conjRing lambda) A = multiplicity lambda A :=
    multiplicity_eq_of_associated_left conjRing_lambda_associated.symm
  simpa [conjRing_involutive, hassoc] using hmap

def qLambda : IsDedekindDomain.HeightOneSpectrum OM :=
  IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr lambda_prime)

def ordAt (q : IsDedekindDomain.HeightOneSpectrum OM) (x : M) : ℤ :=
  -WithZero.log (q.valuation M x)

private theorem val_ne_zero
    (q : IsDedekindDomain.HeightOneSpectrum OM) {x : M} (hx : x ≠ 0) :
    q.valuation M x ≠ 0 :=
  (Valuation.ne_zero_iff (q.valuation M)).2 hx

@[simp] theorem ordAt_one (q : IsDedekindDomain.HeightOneSpectrum OM) :
    ordAt q 1 = 0 := by simp [ordAt]

theorem ordAt_mul (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt q (x * y) = ordAt q x + ordAt q y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul (val_ne_zero q hx) (val_ne_zero q hy)]
  ring

theorem ordAt_div (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt q (x / y) = ordAt q x - ordAt q y := by
  unfold ordAt
  rw [map_div₀, WithZero.log_div (val_ne_zero q hx) (val_ne_zero q hy)]
  ring

theorem ordAt_pow (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x : M} (hx : x ≠ 0) (n : ℕ) :
    ordAt q (x ^ n) = n * ordAt q x := by
  unfold ordAt
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

@[simp] theorem ordAt_neg (q : IsDedekindDomain.HeightOneSpectrum OM)
    (x : M) : ordAt q (-x) = ordAt q x := by
  unfold ordAt
  rw [(q.valuation M).map_neg]

private theorem val_lt_of_ord_lt
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ordAt q x < ordAt q y) :
    q.valuation M y < q.valuation M x := by
  rw [← WithZero.log_lt_log (val_ne_zero q hy) (val_ne_zero q hx)]
  unfold ordAt at hxy
  omega

theorem ordAt_add_eq_left_of_lt
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ordAt q x < ordAt q y) :
    ordAt q (x + y) = ordAt q x := by
  unfold ordAt
  rw [(q.valuation M).map_add_eq_of_lt_left
    (val_lt_of_ord_lt q hx hy hxy)]

theorem ordAt_add_eq_right_of_lt
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0)
    (hyx : ordAt q y < ordAt q x) :
    ordAt q (x + y) = ordAt q y := by
  rw [add_comm]
  exact ordAt_add_eq_left_of_lt q hy hx hyx

theorem ideal_multiplicity_span_eq (p A : OM) (hp : Irreducible p)
    (hA : A ≠ 0) :
    multiplicity (Ideal.span {p}) (Ideal.span {A}) = multiplicity p A := by
  have hpPrime : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hpIdeal : Prime (Ideal.span ({p} : Set OM)) :=
    Ideal.prime_span_singleton_iff.mpr hpPrime
  have hspanA : Ideal.span ({A} : Set OM) ≠ 0 := by
    intro hspan
    apply hA
    apply Ideal.span_singleton_eq_bot.mp
    simpa using hspan
  have hfinI : FiniteMultiplicity (Ideal.span ({p} : Set OM))
      (Ideal.span ({A} : Set OM)) :=
    FiniteMultiplicity.of_prime_left hpIdeal hspanA
  have hfinE : FiniteMultiplicity p A :=
    FiniteMultiplicity.of_prime_left hpPrime hA
  have hem := Ideal.emultiplicity_eq_emultiplicity_span (a := p) (b := A)
  rw [hfinI.emultiplicity_eq_multiplicity,
    hfinE.emultiplicity_eq_multiplicity] at hem
  exact WithTop.coe_eq_coe.mp hem

theorem ordAt_qLambda_algebraMap_eq_multiplicity (A : OM) (hA : A ≠ 0) :
    ordAt qLambda (algebraMap OM M A) = multiplicity lambda A := by
  unfold ordAt
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hA]
  change -(WithZero.log
    (WithZero.exp (-((multiplicity (Ideal.span {lambda}) (Ideal.span {A}) : ℕ) : ℤ)))) = _
  rw [ideal_multiplicity_span_eq lambda A lambda_irreducible hA]
  simp

theorem ordAt_qLambda_fraction_eq
    {A B : OM} (hA : A ≠ 0) (hB : B ≠ 0) :
    ordAt qLambda
        (algebraMap OM M A / algebraMap OM M B) =
      (multiplicity lambda A : ℤ) - multiplicity lambda B := by
  rw [ordAt_div]
  · rw [ordAt_qLambda_algebraMap_eq_multiplicity A hA,
      ordAt_qLambda_algebraMap_eq_multiplicity B hB]
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hA
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hB

theorem ordAt_qLambda_complexConj {x : M} (hx : x ≠ 0) :
    ordAt qLambda (NumberField.IsCMField.complexConj M x) =
      ordAt qLambda x := by
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
  have hconjA : conjRing A ≠ 0 := by
    simpa using conjRing.injective.ne hA
  have hconjB : conjRing B ≠ 0 := by
    simpa using conjRing.injective.ne hB
  rw [hconjAB, hxAB,
    ordAt_qLambda_fraction_eq hconjA hconjB,
    ordAt_qLambda_fraction_eq hA hB]
  simp only [multiplicity_conjRing]

theorem mem_asIdeal_of_ordAt_algebraMap_ne_zero
    (q : IsDedekindDomain.HeightOneSpectrum OM) (A : OM)
    (hord : ordAt q (algebraMap OM M A) ≠ 0) : A ∈ q.asIdeal := by
  by_contra hmem
  have hv : q.valuation M (algebraMap OM M A) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := M)).2 hmem
  apply hord
  simp [ordAt, hv]

theorem q_eq_qLambda_of_three_mem
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    (hthree : (3 : OM) ∈ q.asIdeal) : q = qLambda := by
  let p3 : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hle : p3 ≤ q.asIdeal.under ℤ := by
    rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hthree
  have hp3Prime : p3.IsPrime := by
    rw [Ideal.span_singleton_prime]
    · exact Int.prime_three
    · norm_num
  have hp3Max : p3.IsMaximal := hp3Prime.isMaximal (by
    simp [p3, Ideal.span_singleton_eq_bot])
  have hunderPrime : (q.asIdeal.under ℤ).IsPrime := by
    exact q.isPrime.comap (algebraMap ℤ OM)
  have hunder : p3 = q.asIdeal.under ℤ :=
    hp3Max.eq_of_le hunderPrime.ne_top hle
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : q.asIdeal.LiesOver p3 := ⟨hunder⟩
  letI : IsCyclotomicExtension {3 ^ (1 + 1)} ℚ M := by
    norm_num
    exact cycloM
  have hideal := IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
    3 1 M zeta_primitive q.asIdeal
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact hideal

theorem q_eq_qLambda_of_ordAt_three_ne_zero
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    (hord : ordAt q (3 : M) ≠ 0) : q = qLambda := by
  apply q_eq_qLambda_of_three_mem
  apply mem_asIdeal_of_ordAt_algebraMap_ne_zero q (3 : OM)
  simpa only [map_ofNat] using hord

theorem ordAt_complexConj_of_ordAt_three_ne_zero
    (q : IsDedekindDomain.HeightOneSpectrum OM) {x : M}
    (hx : x ≠ 0) (hthree : ordAt q (3 : M) ≠ 0) :
    ordAt q (NumberField.IsCMField.complexConj M x) = ordAt q x := by
  rw [q_eq_qLambda_of_ordAt_three_ne_zero q hthree]
  exact ordAt_qLambda_complexConj hx

def qOfIrreducible (p : OM) (hp : Irreducible p) :
    IsDedekindDomain.HeightOneSpectrum OM :=
  IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp))

@[simp] theorem qOfIrreducible_asIdeal (p : OM) (hp : Irreducible p) :
    (qOfIrreducible p hp).asIdeal = Ideal.span {p} := rfl

theorem ordAt_algebraMap_eq_multiplicity
    (p A : OM) (hp : Irreducible p) (hA : A ≠ 0) :
    ordAt (qOfIrreducible p hp) (algebraMap OM M A) = multiplicity p A := by
  unfold ordAt
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hA]
  rw [qOfIrreducible_asIdeal, ideal_multiplicity_span_eq p A hp hA]
  simp

theorem exists_reduced_fraction {x : M} (hx : x ≠ 0) :
    ∃ A B : OM, A ≠ 0 ∧ B ≠ 0 ∧ IsRelPrime A B ∧
      x = algebraMap OM M A / algebraMap OM M B := by
  classical
  letI : GCDMonoid OM := IsBezout.toGCDDomain OM
  obtain ⟨A, B, hBmem, hAB⟩ := IsFractionRing.div_surjective OM x
  have hB : B ≠ 0 := nonZeroDivisors.ne_zero hBmem
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, map_zero, zero_div] at hAB
    exact hx hAB.symm
  obtain ⟨A', B', hAeq, hBeq, hgcd⟩ := extract_gcd A B
  have hd : gcd A B ≠ 0 := by
    intro hd
    rw [hd, zero_mul] at hBeq
    exact hB hBeq
  have hA' : A' ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hAeq
    exact hA hAeq
  have hB' : B' ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hBeq
    exact hB hBeq
  refine ⟨A', B', hA', hB', gcd_isUnit_iff_isRelPrime.mp hgcd, ?_⟩
  calc
    x = algebraMap OM M A / algebraMap OM M B := hAB.symm
    _ = algebraMap OM M (gcd A B * A') /
        algebraMap OM M (gcd A B * B') := by rw [← hAeq, ← hBeq]
    _ = algebraMap OM M A' / algebraMap OM M B' := by
      push_cast
      have hdM : (((gcd A B : OM) : M)) ≠ 0 := by
        exact (map_eq_zero_iff _
          (FaithfulSMul.algebraMap_injective OM M)).not.mpr hd
      field_simp [hdM]

private theorem not_dvd_right_of_isRelPrime {A B p : OM}
    (hrel : IsRelPrime A B) (hp : Irreducible p) (hpA : p ∣ A) :
    ¬p ∣ B := by
  intro hpB
  exact hp.not_isUnit (hrel hpA hpB)

theorem ordAt_reduced_fraction_eq
    {A B p : OM} (hA : A ≠ 0) (hB : B ≠ 0)
    (hp : Irreducible p) :
    ordAt (qOfIrreducible p hp)
        (algebraMap OM M A / algebraMap OM M B) =
      (multiplicity p A : ℤ) - multiplicity p B := by
  rw [ordAt_div]
  · rw [ordAt_algebraMap_eq_multiplicity p A hp hA,
      ordAt_algebraMap_eq_multiplicity p B hp hB]
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hA
  · exact (map_eq_zero_iff _
      (FaithfulSMul.algebraMap_injective OM M)).not.mpr hB

theorem field_unit_mul_cube_of_all_orders
    {x : M} (hx : x ≠ 0)
    (hall : ∀ q : IsDedekindDomain.HeightOneSpectrum OM,
      (3 : ℤ) ∣ ordAt q x) :
    ∃ eps : OMˣ, ∃ c : M,
      x = (((eps : OM) : M)) * c ^ 3 := by
  classical
  letI : NormalizationMonoid OM :=
    UniqueFactorizationMonoid.normalizationMonoid
  obtain ⟨A, B, hA, hB, hrel, hxAB⟩ := exists_reduced_fraction hx
  have hfacA : ∀ p : OM, 3 ∣ factorization A p := by
    intro p
    by_cases hp0 : factorization A p = 0
    · simp [hp0]
    have hpNF : p ∈ normalizedFactors A := by
      simpa using (Finsupp.mem_support_iff.mpr hp0)
    have hpIrr : Irreducible p := irreducible_of_normalized_factor p hpNF
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpA : p ∣ A := dvd_of_mem_normalizedFactors hpNF
    have hpB : ¬p ∣ B := not_dvd_right_of_isRelPrime hrel hpIrr hpA
    have hmultB : multiplicity p B = 0 := multiplicity_eq_zero.mpr hpB
    have hord := hall (qOfIrreducible p hpIrr)
    rw [hxAB, ordAt_reduced_fraction_eq hA hB hpIrr, hmultB,
      Nat.cast_zero, sub_zero] at hord
    have hfacEq : factorization A p = multiplicity p A := by
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hA, hpNorm]
    have hnat : 3 ∣ multiplicity p A := by exact_mod_cast hord
    rwa [hfacEq]
  have hfacB : ∀ p : OM, 3 ∣ factorization B p := by
    intro p
    by_cases hp0 : factorization B p = 0
    · simp [hp0]
    have hpNF : p ∈ normalizedFactors B := by
      simpa using (Finsupp.mem_support_iff.mpr hp0)
    have hpIrr : Irreducible p := irreducible_of_normalized_factor p hpNF
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpB : p ∣ B := dvd_of_mem_normalizedFactors hpNF
    have hpA : ¬p ∣ A := by
      intro hpA
      exact hpIrr.not_isUnit (hrel hpA hpB)
    have hmultA : multiplicity p A = 0 := multiplicity_eq_zero.mpr hpA
    have hord := hall (qOfIrreducible p hpIrr)
    rw [hxAB, ordAt_reduced_fraction_eq hA hB hpIrr, hmultA,
      Nat.cast_zero, zero_sub] at hord
    have hmult : (3 : ℤ) ∣ (multiplicity p B : ℤ) := dvd_neg.mp hord
    have hnat : 3 ∣ multiplicity p B := by exact_mod_cast hmult
    have hfacEq : factorization B p = multiplicity p B := by
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hB, hpNorm]
    rwa [hfacEq]
  obtain ⟨epsA, cA, hAcube⟩ :=
    unit_mul_cube_of_factorization_dvd hA hfacA
  obtain ⟨epsB, cB, hBcube⟩ :=
    unit_mul_cube_of_factorization_dvd hB hfacB
  have hcB : (cB : M) ≠ 0 := by
    intro hcB
    have hcB' : cB = 0 := by exact_mod_cast hcB
    rw [hcB', zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] at hBcube
    exact hB hBcube
  refine ⟨epsA * epsB⁻¹, (cA : M) / (cB : M), ?_⟩
  rw [hxAB, hAcube, hBcube]
  push_cast
  field_simp
  simp

set_option maxHeartbeats 0 in
/-- Away from the prime over three, the two conjugate factors of a cube
norm force each individual order to be divisible by three. -/
theorem cube_order_of_conj_norm_outside_three
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    {h hc xi X : M}
    (hh : h ≠ 0) (hhc : hc ≠ 0) (hxi : xi ≠ 0) (hX0 : X ≠ 0)
    (hnorm : h * hc = X ^ 3)
    (hdiff : h - hc = 3 * xi * qM)
    (hX : X = xi + 3)
    (hthree : ordAt q (3 : M) = 0) :
    (3 : ℤ) ∣ ordAt q h := by
  let e : ℤ := ordAt q h
  let f : ℤ := ordAt q hc
  let u : ℤ := ordAt q xi
  let xord : ℤ := ordAt q X
  have hnormOrd : e + f = 3 * xord := by
    have hmul := ordAt_mul q hh hhc
    have hpow := ordAt_pow q hX0 3
    rw [hnorm] at hmul
    dsimp [e, f, xord]
    omega
  by_cases hef : e = f
  · have hdiv : (3 : ℤ) ∣ 2 * e := by
      refine ⟨xord, ?_⟩
      omega
    rcases Int.prime_three.dvd_mul.mp hdiv with hthreeTwo | hthreeE
    · norm_num at hthreeTwo
    · simpa [e] using hthreeE
  · have h3 : (3 : M) ≠ 0 := by norm_num
    have hdiff0 : h - hc ≠ 0 := by
      rw [hdiff]
      exact mul_ne_zero (mul_ne_zero h3 hxi) qM_ne_zero
    have hqord : ordAt q qM = 0 := by
      have hp := ordAt_pow q qM_ne_zero 2
      rw [qM_sq, ordAt_neg] at hp
      omega
    let m : ℤ := min e f
    have hdiffOrd : ordAt q (h - hc) = m := by
      rcases lt_or_gt_of_ne hef with hef' | hfe'
      · have hadd := ordAt_add_eq_left_of_lt q hh (neg_ne_zero.mpr hhc) <| by
          simpa [e, f] using hef'
        change ordAt q (h - hc) = min e f
        rw [min_eq_left hef'.le]
        simpa [sub_eq_add_neg, e] using hadd
      · have hadd := ordAt_add_eq_right_of_lt q hh (neg_ne_zero.mpr hhc) <| by
          simpa [e, f] using hfe'
        change ordAt q (h - hc) = min e f
        rw [min_eq_right hfe'.le]
        simpa [sub_eq_add_neg, f] using hadd
    have hu : u = m := by
      have h3xi : ordAt q ((3 : M) * xi) = ordAt q (3 : M) + u := by
        simpa [u] using ordAt_mul q h3 hxi
      have hprod : ordAt q ((3 : M) * xi * qM) =
          ordAt q ((3 : M) * xi) + ordAt q qM :=
        ordAt_mul q (mul_ne_zero h3 hxi) qM_ne_zero
      rw [hdiff] at hdiffOrd
      rw [hprod, h3xi, hthree, hqord] at hdiffOrd
      omega
    have hmzero : m = 0 := by
      by_contra hm0
      rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
      · have hxi3 : ordAt q xi < ordAt q (3 : M) := by
          rw [hthree]
          simpa [u, hu] using hmneg
        have hsum := ordAt_add_eq_left_of_lt q hxi h3 hxi3
        have hxord : xord = m := by
          have hsum' : ordAt q X = ordAt q xi := by
            rw [hX]
            exact hsum
          simpa [xord, u, hu] using hsum'
        have hminle : m ≤ e ∧ m ≤ f := by
          exact ⟨min_le_left _ _, min_le_right _ _⟩
        omega
      · have h3xi : ordAt q (3 : M) < ordAt q xi := by
          rw [hthree]
          simpa [u, hu] using hmpos
        have hsum := ordAt_add_eq_right_of_lt q hxi h3 h3xi
        have hxord : xord = 0 := by
          have hsum' : ordAt q X = ordAt q (3 : M) := by
            rw [hX]
            exact hsum
          simpa [xord, hthree] using hsum'
        have hminle : m ≤ e ∧ m ≤ f := by
          exact ⟨min_le_left _ _, min_le_right _ _⟩
        omega
    rcases le_total e f with hefle | hfele
    · have he0 : e = 0 := by
        change min e f = 0 at hmzero
        rw [min_eq_left hefle] at hmzero
        exact hmzero
      simpa [e, he0]
    · have hf0 : f = 0 := by
        change min e f = 0 at hmzero
        rw [min_eq_right hfele] at hmzero
        exact hmzero
      refine ⟨xord, ?_⟩
      omega

theorem cube_order_of_conj_norm_at_three
    (q : IsDedekindDomain.HeightOneSpectrum OM)
    {h X : M} (hh : h ≠ 0) (hX : X ≠ 0)
    (hnorm : h * NumberField.IsCMField.complexConj M h = X ^ 3)
    (hthree : ordAt q (3 : M) ≠ 0) :
    (3 : ℤ) ∣ ordAt q h := by
  have hhc : NumberField.IsCMField.complexConj M h ≠ 0 :=
    by simpa using (NumberField.IsCMField.complexConj M).injective.ne_iff.mpr hh
  have hconjOrd := ordAt_complexConj_of_ordAt_three_ne_zero q hh hthree
  have hmul := ordAt_mul q hh hhc
  have hpow := ordAt_pow q hX 3
  rw [hnorm] at hmul
  have hdiv : (3 : ℤ) ∣ 2 * ordAt q h := by
    refine ⟨ordAt q X, ?_⟩
    omega
  rcases Int.prime_three.dvd_mul.mp hdiv with hthreeTwo | hthreeH
  · norm_num at hthreeTwo
  · exact hthreeH

open Isogeny IsogenyPoints

private theorem ehat_residual_eq_zero_of_nonsingular
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    affineResidual Ehat0 xi eta = 0 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simpa [affineResidual] using heq

/-- The forward-isogeny Kummer factor in `M=L(sqrt(-3))`. -/
def phiKappa : Ehat0Point → M
  | .zero => 1
  | .some xi eta _ =>
      embedL (dualZ xi eta) + embedL ((3 / 2 : L) * xi) * qM

def phiKappaX : Ehat0Point → L
  | .zero => 1
  | .some xi _ _ => dualX xi

@[simp] theorem phiKappa_zero : phiKappa 0 = 1 := rfl

theorem complexConj_phiKappa (Q : Ehat0Point) :
    NumberField.IsCMField.complexConj M (phiKappa Q) =
      match Q with
      | .zero => 1
      | .some xi eta _ =>
          embedL (dualZ xi eta) - embedL ((3 / 2 : L) * xi) * qM := by
  cases Q with
  | zero => simp [phiKappa, phiKappaX]
  | some xi eta h =>
      simp only [phiKappa, map_add, map_mul, complexConj_embedL,
        complexConj_qM, map_one]
      ring

theorem phiKappa_norm (Q : Ehat0Point) :
    phiKappa Q * NumberField.IsCMField.complexConj M (phiKappa Q) =
      embedL (phiKappaX Q) ^ 3 := by
  cases Q with
  | zero => simp [phiKappa, phiKappaX]
  | some xi eta h =>
      rw [complexConj_phiKappa]
      change
        (embedL (dualZ xi eta) + embedL ((3 / 2 : L) * xi) * qM) *
          (embedL (dualZ xi eta) - embedL ((3 / 2 : L) * xi) * qM) =
        embedL (dualX xi) ^ 3
      have hres := ehat_residual_eq_zero_of_nonsingular h
      have hcomp := velu_completed_change_identity xi eta
      rw [hres, mul_zero] at hcomp
      have hL :
          dualZ xi eta ^ 2 + 3 * ((3 / 2 : L) * xi) ^ 2 =
            dualX xi ^ 3 := by
        unfold veluCompletedResidual dualX at hcomp
        unfold dualX
        linear_combination (1 / 4 : L) * hcomp
      have hmap3 : embedL (3 : L) = (3 : M) :=
        map_natCast embedL.toRingHom 3
      calc
        (embedL (dualZ xi eta) + embedL ((3 / 2 : L) * xi) * qM) *
            (embedL (dualZ xi eta) - embedL ((3 / 2 : L) * xi) * qM) =
          embedL (dualZ xi eta) ^ 2 -
            embedL ((3 / 2 : L) * xi) ^ 2 * qM ^ 2 := by ring
        _ = embedL (dualZ xi eta) ^ 2 +
            3 * embedL ((3 / 2 : L) * xi) ^ 2 := by rw [qM_sq]; ring
        _ = embedL (dualZ xi eta ^ 2 +
            3 * ((3 / 2 : L) * xi) ^ 2) := by
              simp only [map_add, map_mul, map_pow, hmap3]
        _ = embedL (dualX xi ^ 3) := by rw [hL]
        _ = embedL (dualX xi) ^ 3 := by rw [map_pow]

theorem phiKappa_ne_zero (Q : Ehat0Point) : phiKappa Q ≠ 0 := by
  intro hzero
  have hnorm := phiKappa_norm Q
  rw [hzero, zero_mul] at hnorm
  cases Q with
  | zero => simp [phiKappaX] at hnorm
  | some xi eta h =>
      have hX : dualX xi ≠ 0 := dualX_ne_zero_of_nonsingular h
      have hXM : embedL (dualX xi) ≠ 0 := by
        simpa using embedL.injective.ne hX
      exact (pow_ne_zero 3 hXM) hnorm.symm

theorem phiKappa_diff_conj
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    phiKappa (.some xi eta h) -
        NumberField.IsCMField.complexConj M (phiKappa (.some xi eta h)) =
      3 * embedL xi * qM := by
  rw [complexConj_phiKappa]
  change
    (embedL (dualZ xi eta) + embedL ((3 / 2 : L) * xi) * qM) -
      (embedL (dualZ xi eta) - embedL ((3 / 2 : L) * xi) * qM) =
        3 * embedL xi * qM
  simp only [map_mul, map_div₀, map_ofNat]
  ring

theorem phiKappa_order_dvd_three
    (Q : Ehat0Point) (q : IsDedekindDomain.HeightOneSpectrum OM) :
    (3 : ℤ) ∣ ordAt q (phiKappa Q) := by
  cases Q with
  | zero => simp [phiKappa]
  | some xi eta h =>
      let H : M := phiKappa (.some xi eta h)
      let HC : M := NumberField.IsCMField.complexConj M H
      let XM : M := embedL (dualX xi)
      have hH : H ≠ 0 := phiKappa_ne_zero (.some xi eta h)
      have hHC : HC ≠ 0 := by
        simpa [HC] using
          (NumberField.IsCMField.complexConj M).injective.ne_iff.mpr hH
      have hX : dualX xi ≠ 0 := dualX_ne_zero_of_nonsingular h
      have hXM : XM ≠ 0 := by
        simpa [XM] using embedL.injective.ne hX
      have hnorm : H * HC = XM ^ 3 := by
        simpa [H, HC, XM, phiKappaX] using phiKappa_norm (.some xi eta h)
      by_cases hthree : ordAt q (3 : M) = 0
      · by_cases hxi : xi = 0
        · have hHCeq : HC = H := by
            subst xi
            simp [HC, H, complexConj_phiKappa, phiKappa]
          have hmul := ordAt_mul q hH hHC
          have hpow := ordAt_pow q hXM 3
          rw [hHCeq] at hmul
          have hnorm' : H * H = XM ^ 3 := by simpa [hHCeq] using hnorm
          rw [hnorm'] at hmul
          have hdiv : (3 : ℤ) ∣ 2 * ordAt q H := by
            refine ⟨ordAt q XM, ?_⟩
            omega
          rcases Int.prime_three.dvd_mul.mp hdiv with hthreeTwo | hthreeH
          · norm_num at hthreeTwo
          · simpa [H] using hthreeH
        · apply cube_order_of_conj_norm_outside_three
              (h := H) (hc := HC) (xi := embedL xi) (X := XM)
              q hH hHC (by simpa using embedL.injective.ne hxi) hXM hnorm
          · simpa [H, HC] using phiKappa_diff_conj h
          · simp [XM, dualX,
              show embedL (3 : L) = (3 : M) from map_natCast embedL.toRingHom 3]
          · exact hthree
      · exact cube_order_of_conj_norm_at_three q hH hXM hnorm hthree

theorem phiKappa_unit_cube (Q : Ehat0Point) :
    ∃ eps : OMˣ, ∃ c : M,
      phiKappa Q = (((eps : OM) : M)) * c ^ 3 :=
  field_unit_mul_cube_of_all_orders (phiKappa_ne_zero Q)
    (phiKappa_order_dvd_three Q)

theorem phiKappa_global_candidate (Q : Ehat0Point) :
    ∃ e : Fin 3, ∃ c : M,
      phiKappa Q = zeta ^ e.val * c ^ 3 := by
  obtain ⟨eps, b, hb⟩ := phiKappa_unit_cube Q
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply phiKappa_ne_zero Q
    rw [hb, hbzero]
    norm_num
  let bC : M := NumberField.IsCMField.complexConj M b
  have hbC0 : bC ≠ 0 := by
    simpa [bC] using
      (NumberField.IsCMField.complexConj M).injective.ne_iff.mpr hb0
  let X : M := embedL (phiKappaX Q)
  have hX0 : X ≠ 0 := by
    cases Q with
    | zero => simp [X, phiKappaX]
    | some xi eta h =>
        simpa [X, phiKappaX] using
          embedL.injective.ne (dualX_ne_zero_of_nonsingular h)
  have hnorm' :
      ((((eps : OM) : M)) * b ^ 3) *
          (NumberField.IsCMField.complexConj M (((eps : OM) : M)) * bC ^ 3) =
        X ^ 3 := by
    calc
      _ = phiKappa Q *
          NumberField.IsCMField.complexConj M (phiKappa Q) := by
            rw [hb]
            simp [bC]
      _ = X ^ 3 := by simpa [X] using phiKappa_norm Q
  have hepsNorm :
      (((eps : OM) : M)) *
          NumberField.IsCMField.complexConj M (((eps : OM) : M)) =
        (X / (b * bC)) ^ 3 := by
    calc
      (((eps : OM) : M)) *
          NumberField.IsCMField.complexConj M (((eps : OM) : M)) =
        X ^ 3 / (b * bC) ^ 3 := by
          apply (eq_div_iff (pow_ne_zero 3 (mul_ne_zero hb0 hbC0))).2
          calc
            ((((eps : OM) : M)) *
                NumberField.IsCMField.complexConj M (((eps : OM) : M))) *
                  (b * bC) ^ 3 =
              ((((eps : OM) : M)) * b ^ 3) *
                (NumberField.IsCMField.complexConj M (((eps : OM) : M)) *
                  bC ^ 3) := by ring
            _ = X ^ 3 := hnorm'
      _ = (X / (b * bC)) ^ 3 := by rw [div_pow]
  obtain ⟨e, d, hd⟩ :=
    CyclotomicUnits.unit_norm_cube_classification eps
      (X / (b * bC)) hepsNorm
  refine ⟨e, d * b, ?_⟩
  rw [hb, hd]
  ring

end

end MazurProof.N18RouteC.CyclotomicValuation
