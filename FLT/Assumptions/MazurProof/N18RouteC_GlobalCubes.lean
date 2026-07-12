import FLT.Assumptions.MazurProof.N18RouteC_ValuationSupport
import FLT.Assumptions.MazurProof.N18ConjCube
import FLT.Assumptions.MazurProof.N18RouteC_UnitCubes
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic
import FLT.Assumptions.MazurProof.N18RouteC_TwoAdic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

open UniqueFactorizationMonoid
open IsDedekindDomain

/-!
# Global cube classes in the N18 cubic field

This file turns divisibility of all height-one orders into an actual cube
factorization.  Class number one is used through the UFD structure of the
integer ring.  Removing the two exceptional orders then gives the four
concrete `S`-unit directions used by the 81-entry dual Selmer table.
-/

namespace MazurProof.N18RouteC.GlobalCubes

open FieldArithmetic ValuationSupport

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

def qOfIrreducible (p : OL) (hp : Irreducible p) :
    IsDedekindDomain.HeightOneSpectrum OL :=
  IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp))

@[simp] theorem qOfIrreducible_asIdeal (p : OL) (hp : Irreducible p) :
    (qOfIrreducible p hp).asIdeal = Ideal.span {p} := rfl

theorem ideal_multiplicity_span_eq (p A : OL) (hp : Irreducible p)
    (hA : A ≠ 0) :
    multiplicity (Ideal.span {p}) (Ideal.span {A}) = multiplicity p A := by
  have hpPrime : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hpIdeal : Prime (Ideal.span ({p} : Set OL)) :=
    Ideal.prime_span_singleton_iff.mpr hpPrime
  have hspanA : Ideal.span ({A} : Set OL) ≠ 0 := by
    intro hspan
    apply hA
    apply Ideal.span_singleton_eq_bot.mp
    simpa using hspan
  have hfinI : FiniteMultiplicity (Ideal.span ({p} : Set OL))
      (Ideal.span ({A} : Set OL)) :=
    FiniteMultiplicity.of_prime_left hpIdeal hspanA
  have hfinE : FiniteMultiplicity p A :=
    FiniteMultiplicity.of_prime_left hpPrime hA
  have hem := Ideal.emultiplicity_eq_emultiplicity_span (a := p) (b := A)
  rw [hfinI.emultiplicity_eq_multiplicity,
    hfinE.emultiplicity_eq_multiplicity] at hem
  exact WithTop.coe_eq_coe.mp hem

theorem ordAt_algebraMap_eq_multiplicity (p A : OL) (hp : Irreducible p)
    (hA : A ≠ 0) :
    ordAt (qOfIrreducible p hp) (algebraMap OL L A) = multiplicity p A := by
  unfold ordAt
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hA]
  rw [qOfIrreducible_asIdeal, ideal_multiplicity_span_eq p A hp hA]
  simp

theorem exists_reduced_fraction {x : L} (hx : x ≠ 0) :
    ∃ A B : OL, A ≠ 0 ∧ B ≠ 0 ∧ IsRelPrime A B ∧
      x = algebraMap OL L A / algebraMap OL L B := by
  classical
  letI : GCDMonoid OL := IsBezout.toGCDDomain OL
  obtain ⟨A, B, hBmem, hAB⟩ := IsFractionRing.div_surjective OL x
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
    x = algebraMap OL L A / algebraMap OL L B := hAB.symm
    _ = algebraMap OL L (gcd A B * A') /
        algebraMap OL L (gcd A B * B') := by rw [← hAeq, ← hBeq]
    _ = algebraMap OL L A' / algebraMap OL L B' := by
      push_cast
      have hdL : (((gcd A B : OL) : L)) ≠ 0 := by
        exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective OL L)).not.mpr hd
      field_simp [hdL]

private theorem not_dvd_right_of_isRelPrime {A B p : OL}
    (hrel : IsRelPrime A B) (hp : Irreducible p) (hpA : p ∣ A) :
    ¬p ∣ B := by
  intro hpB
  exact hp.not_isUnit (hrel hpA hpB)

theorem ordAt_reduced_fraction_eq
    {A B p : OL} (hA : A ≠ 0) (hB : B ≠ 0)
    (hp : Irreducible p) :
    ordAt (qOfIrreducible p hp)
        (algebraMap OL L A / algebraMap OL L B) =
      (multiplicity p A : ℤ) - multiplicity p B := by
  rw [ValuationSupport.ordAt_div]
  · rw [ordAt_algebraMap_eq_multiplicity p A hp hA,
      ordAt_algebraMap_eq_multiplicity p B hp hB]
  · exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective OL L)).not.mpr hA
  · exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective OL L)).not.mpr hB

theorem field_unit_mul_cube_of_all_orders
    {x : L} (hx : x ≠ 0)
    (hall : ∀ q : IsDedekindDomain.HeightOneSpectrum OL,
      (3 : ℤ) ∣ ordAt q x) :
    ∃ eps : OLˣ, ∃ c : L,
      x = (((eps : OL) : L)) * c ^ 3 := by
  classical
  letI : NormalizationMonoid OL :=
    UniqueFactorizationMonoid.normalizationMonoid
  obtain ⟨A, B, hA, hB, hrel, hxAB⟩ := exists_reduced_fraction hx
  have hfacA : ∀ p : OL, 3 ∣ factorization A p := by
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
  have hfacB : ∀ p : OL, 3 ∣ factorization B p := by
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
      exact hpIrr.not_isUnit
        (hrel hpA hpB)
    have hmultA : multiplicity p A = 0 := multiplicity_eq_zero.mpr hpA
    have hord := hall (qOfIrreducible p hpIrr)
    rw [hxAB, ordAt_reduced_fraction_eq hA hB hpIrr, hmultA,
      Nat.cast_zero, zero_sub] at hord
    have hmult : (3 : ℤ) ∣ (multiplicity p B : ℤ) := by
      exact dvd_neg.mp hord
    have hnat : 3 ∣ multiplicity p B := by exact_mod_cast hmult
    have hfacEq : factorization B p = multiplicity p B := by
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hB, hpNorm]
    rwa [hfacEq]
  obtain ⟨epsA, cA, hAcube⟩ :=
    unit_mul_cube_of_factorization_dvd hA hfacA
  obtain ⟨epsB, cB, hBcube⟩ :=
    unit_mul_cube_of_factorization_dvd hB hfacB
  have hcB : (cB : L) ≠ 0 := by
    intro hcB
    have hcB' : cB = 0 := by exact_mod_cast hcB
    rw [hcB', zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero] at hBcube
    exact hB hBcube
  refine ⟨epsA * epsB⁻¹, (cA : L) / (cB : L), ?_⟩
  rw [hxAB, hAcube, hBcube]
  push_cast
  field_simp
  simp

theorem p2_ne_p3 : TwoAdic.p2 ≠ ThreeAdic.p3 := by
  intro heq
  have hideal := congrArg
    (IsDedekindDomain.HeightOneSpectrum.asIdeal (R := OL)) heq
  have hcomap := congrArg (Ideal.comap (algebraMap ℤ OL)) hideal
  change Ideal.comap (algebraMap ℤ OL) FieldArithmetic.primeAboveTwo =
    Ideal.comap (algebraMap ℤ OL) ThreeAdic.primeAboveThree at hcomap
  have hbase : Ideal.span ({(2 : ℤ)} : Set ℤ) =
      Ideal.span ({(3 : ℤ)} : Set ℤ) :=
    FieldArithmetic.primeAboveTwo_mem.2.over.trans
      (hcomap.trans ThreeAdic.primeAboveThree_mem.2.over.symm)
  have hthree : (3 : ℤ) ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) := by
    rw [hbase]
    exact Ideal.subset_span (Set.mem_singleton 3)
  rw [Ideal.mem_span_singleton] at hthree
  norm_num at hthree

theorem two_not_mem_of_ne_p2
    (q : IsDedekindDomain.HeightOneSpectrum OL) (hq : q ≠ TwoAdic.p2) :
    (2 : OL) ∉ q.asIdeal := by
  intro hmem
  have hle : TwoAdic.p2.asIdeal ≤ q.asIdeal := by
    change FieldArithmetic.primeAboveTwo ≤ q.asIdeal
    rw [FieldArithmetic.primeAboveTwo_eq_span_two]
    exact Ideal.span_le.mpr (by simpa using hmem)
  have heq := Ideal.IsMaximal.eq_of_le TwoAdic.p2.isMaximal q.isPrime.ne_top hle
  exact hq (IsDedekindDomain.HeightOneSpectrum.ext heq.symm)

theorem pi_not_mem_of_ne_p3
    (q : IsDedekindDomain.HeightOneSpectrum OL) (hq : q ≠ ThreeAdic.p3) :
    FieldArithmetic.piInteger ∉ q.asIdeal := by
  intro hmem
  have hle : ThreeAdic.p3.asIdeal ≤ q.asIdeal := by
    change ThreeAdic.primeAboveThree ≤ q.asIdeal
    rw [ThreeAdic.primeAboveThree_eq_span_pi]
    exact Ideal.span_le.mpr (by simpa using hmem)
  have heq := Ideal.IsMaximal.eq_of_le ThreeAdic.p3.isMaximal q.isPrime.ne_top hle
  exact hq (IsDedekindDomain.HeightOneSpectrum.ext heq.symm)

theorem ordAt_integral_eq_zero_of_not_mem
    (q : IsDedekindDomain.HeightOneSpectrum OL) (A : OL)
    (hA : A ∉ q.asIdeal) :
    ordAt q (algebraMap OL L A) = 0 := by
  have hv : q.valuation L (algebraMap OL L A) = 1 :=
    (q.valuation_eq_one_iff_notMem (K := L)).mpr hA
  simp [ordAt, hv]

theorem ordAt_two_of_ne_p2
    (q : IsDedekindDomain.HeightOneSpectrum OL) (hq : q ≠ TwoAdic.p2) :
    ordAt q (2 : L) = 0 := by
  change ordAt q (algebraMap OL L (2 : OL)) = 0
  exact ordAt_integral_eq_zero_of_not_mem q (2 : OL)
    (two_not_mem_of_ne_p2 q hq)

theorem ordAt_pi_of_ne_p3
    (q : IsDedekindDomain.HeightOneSpectrum OL) (hq : q ≠ ThreeAdic.p3) :
    ordAt q pi = 0 := by
  simpa [FieldArithmetic.piInteger_coe_L] using
    ordAt_integral_eq_zero_of_not_mem q FieldArithmetic.piInteger
      (pi_not_mem_of_ne_p3 q hq)

theorem ordAt_unit (q : IsDedekindDomain.HeightOneSpectrum OL) (u : OLˣ) :
    ordAt q (((u : OL) : L)) = 0 := by
  apply ordAt_integral_eq_zero_of_not_mem
  intro hmem
  have htop : q.asIdeal = ⊤ :=
    q.asIdeal.eq_top_of_isUnit_mem hmem (Units.isUnit u)
  exact q.isPrime.ne_top htop

theorem ordAt_three_of_ne_p3
    (q : IsDedekindDomain.HeightOneSpectrum OL) (hq : q ≠ ThreeAdic.p3) :
    ordAt q (3 : L) = 0 := by
  have hpi : pi ≠ 0 := by
    intro hzero
    have hrel := pi_relation
    rw [hzero] at hrel
    norm_num at hrel
  let u : OLˣ := ThreeAdic.oneSubPiSqUnit⁻¹
  have hu : (((u : OL) : L)) ≠ 0 := by simp
  have hfield : (((u : OL) : L)) =
      pi ^ 2 + 3 * pi + 1 := rfl
  rw [ThreeAdic.three_eq_pi_cubed_mul_inverse, ← hfield,
    ordAt_mul q (pow_ne_zero 3 hpi) hu,
    ordAt_pow q hpi 3, ordAt_pi_of_ne_p3 q hq, ordAt_unit q u]
  norm_num

theorem exists_fin3_sub_dvd (z : ℤ) :
    ∃ k : Fin 3, (3 : ℤ) ∣ z - k.val := by
  have hnonneg : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
  have hlt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
  have hltNat : (z % 3).toNat < 3 := by
    rw [Int.toNat_lt hnonneg]
    exact hlt
  let k : Fin 3 := ⟨(z % 3).toNat, hltNat⟩
  refine ⟨k, z / 3, ?_⟩
  have hcast : ((z % 3).toNat : ℤ) = z % 3 :=
    Int.toNat_of_nonneg hnonneg
  have hdiv := Int.emod_add_mul_ediv z 3
  dsimp [k]
  omega

theorem s_unit_normal_form
    {x : L} (hx : x ≠ 0)
    (hsupp : ∀ q : IsDedekindDomain.HeightOneSpectrum OL,
      q ≠ TwoAdic.p2 → q ≠ ThreeAdic.p3 →
      (3 : ℤ) ∣ ordAt q x) :
    ∃ i j k l : Fin 3, ∃ c : L,
      x = a ^ i.val * (a + 1) ^ j.val *
        (2 : L) ^ k.val * pi ^ l.val * c ^ 3 := by
  obtain ⟨k, hk⟩ := exists_fin3_sub_dvd (ordAt TwoAdic.p2 x)
  obtain ⟨l, hl⟩ := exists_fin3_sub_dvd (ordAt ThreeAdic.p3 x)
  let d : L := (2 : L) ^ k.val * pi ^ l.val
  have hpi : pi ≠ 0 := by
    intro hzero
    have hrel := pi_relation
    rw [hzero] at hrel
    norm_num at hrel
  have hd : d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hpi)
  let y : L := x / d
  have hy : y ≠ 0 := div_ne_zero hx hd
  have hall : ∀ q : IsDedekindDomain.HeightOneSpectrum OL,
      (3 : ℤ) ∣ ordAt q y := by
    intro q
    by_cases hq2 : q = TwoAdic.p2
    · subst q
      have hpi2 : ordAt TwoAdic.p2 pi = 0 :=
        ordAt_pi_of_ne_p3 TwoAdic.p2 p2_ne_p3
      have h2 : ordAt TwoAdic.p2 (2 : L) = 1 := TwoAdic.ordTwo_two
      have hyord : ordAt TwoAdic.p2 y = ordAt TwoAdic.p2 x - k.val := by
        simp only [y, d]
        rw [ordAt_div TwoAdic.p2 hx hd,
          ordAt_mul TwoAdic.p2 (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hpi),
          ordAt_pow TwoAdic.p2 (by norm_num) k.val,
          ordAt_pow TwoAdic.p2 hpi l.val, h2, hpi2]
        omega
      rw [hyord]
      exact hk
    · by_cases hq3 : q = ThreeAdic.p3
      · subst q
        have h23 : ordAt ThreeAdic.p3 (2 : L) = 0 :=
          ordAt_two_of_ne_p2 ThreeAdic.p3 p2_ne_p3.symm
        have hpi3 : ordAt ThreeAdic.p3 pi = 1 :=
          ThreeAdic.ordPi_pi
        have hyord : ordAt ThreeAdic.p3 y = ordAt ThreeAdic.p3 x - l.val := by
          simp only [y, d]
          rw [ordAt_div ThreeAdic.p3 hx hd,
            ordAt_mul ThreeAdic.p3 (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hpi),
            ordAt_pow ThreeAdic.p3 (by norm_num) k.val,
            ordAt_pow ThreeAdic.p3 hpi l.val, h23, hpi3]
          omega
        rw [hyord]
        exact hl
      · have h2q := ordAt_two_of_ne_p2 q hq2
        have hpiq := ordAt_pi_of_ne_p3 q hq3
        have hyord : ordAt q y = ordAt q x := by
          simp only [y, d]
          rw [ordAt_div q hx hd,
            ordAt_mul q (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hpi),
            ordAt_pow q (by norm_num) k.val,
            ordAt_pow q hpi l.val, h2q, hpiq]
          omega
        rw [hyord]
        exact hsupp q hq2 hq3
  obtain ⟨eps, c, hycube⟩ := field_unit_mul_cube_of_all_orders hy hall
  obtain ⟨i, j, v, heps⟩ := UnitCubes.unit_cubeclass_classification eps
  have hepsL : (((eps : OL) : L)) =
      a ^ i.val * (a + 1) ^ j.val * (((v : OL) : L)) ^ 3 := by
    simpa using congrArg (fun e : OLˣ ↦ (((e : OL) : L))) heps
  refine ⟨i, j, k, l, (((v : OL) : L)) * c, ?_⟩
  have hxy : x = y * d := by simp [y, hd]
  rw [hxy, hycube, hepsL]
  dsimp [d]
  ring

end

end MazurProof.N18RouteC.GlobalCubes
