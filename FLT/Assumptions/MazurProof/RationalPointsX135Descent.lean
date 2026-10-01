import Mathlib

namespace MazurProof.RationalPointsX135

noncomputable section

open scoped NumberField

open UniqueFactorizationMonoid

/-- A conjugate product which is a cube has cube exponents factor by factor. -/
theorem n35_unit_mul_cube_of_mul_conj_cube
    {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (conj : R ≃+* R) (hinv : Function.Involutive conj)
    {A M : R} (hA : A ≠ 0) (hEq : A * conj A = M ^ 3)
    (hsep : ∀ p : R, Irreducible p →
      (Associated p (conj p) ∨ ¬(p ∣ A ∧ conj p ∣ A))) :
    ∃ eps : Rˣ, ∃ B : R, A = (eps : R) * B ^ 3 := by
  classical
  letI : NormalizationMonoid R :=
    UniqueFactorizationMonoid.normalizationMonoid
  have hconjA : conj A ≠ 0 := by
    intro h
    apply hA
    apply conj.injective
    simpa using h
  have hM : M ≠ 0 := by
    intro h
    have hz : A * conj A = 0 := by simpa [h] using hEq
    exact (mul_ne_zero hA hconjA) hz
  let fac : R →₀ ℕ := factorization A
  have hfac_dvd : ∀ p : R, 3 ∣ fac p := by
    intro p
    by_cases hp0 : fac p = 0
    · simp [hp0]
    have hpSupp : p ∈ fac.support := Finsupp.mem_support_iff.mpr hp0
    have hpNF : p ∈ normalizedFactors A := by simpa [fac] using hpSupp
    have hpPrime : Prime p := prime_of_normalized_factor p hpNF
    have hpIrr : Irreducible p := hpPrime.irreducible
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpDivA : p ∣ A := dvd_of_mem_normalizedFactors hpNF
    have hfinProd : FiniteMultiplicity p (A * conj A) :=
      FiniteMultiplicity.of_prime_left hpPrime (mul_ne_zero hA hconjA)
    have hfinM : FiniteMultiplicity p M :=
      FiniteMultiplicity.of_prime_left hpPrime hM
    have hmul : multiplicity p A + multiplicity p (conj A) =
        3 * multiplicity p M := by
      calc
        multiplicity p A + multiplicity p (conj A) =
            multiplicity p (A * conj A) :=
          (multiplicity_mul hpPrime hfinProd).symm
        _ = multiplicity p (M ^ 3) := by rw [hEq]
        _ = 3 * multiplicity p M :=
          FiniteMultiplicity.multiplicity_pow hpPrime hfinM
    have hmap : multiplicity p (conj A) = multiplicity (conj p) A := by
      have h := multiplicity_map_eq conj (a := conj p) (b := A)
      simpa only [hinv p] using h
    have hfacEq : fac p = multiplicity p A := by
      change factorization A p = multiplicity p A
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hA, hpNorm]
    rw [hfacEq]
    rcases hsep p hpIrr with hpSelf | hpSeparated
    · have hconjMult : multiplicity (conj p) A = multiplicity p A :=
        multiplicity_eq_of_associated_left hpSelf
      rw [hmap, hconjMult] at hmul
      have hthree_two : 3 ∣ 2 * multiplicity p A := by
        refine ⟨multiplicity p M, ?_⟩
        simpa [two_mul] using hmul
      exact (Nat.prime_three.dvd_mul.mp hthree_two).resolve_left (by norm_num)
    · have hnotConj : ¬conj p ∣ A := by
        intro hpConj
        exact hpSeparated ⟨hpDivA, hpConj⟩
      have hzero : multiplicity (conj p) A = 0 :=
        multiplicity_eq_zero.mpr hnotConj
      rw [hmap, hzero, add_zero] at hmul
      exact ⟨multiplicity p M, hmul⟩
  let rootFac : R →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 3) (by simp) fac
  have hthree_rootFac : (3 : ℕ) • rootFac = fac := by
    ext p
    simpa only [Finsupp.nsmul_apply, rootFac,
      Finsupp.mapRange_apply, Nat.nsmul_eq_mul] using
      Nat.mul_div_cancel' (hfac_dvd p)
  let s : Multiset R := Finsupp.toMultiset rootFac
  have hroot_support : rootFac.support ⊆ fac.support := by
    dsimp [rootFac]
    exact Finsupp.support_mapRange
  have hsNF : ∀ p ∈ s, p ∈ normalizedFactors A := by
    intro p hp
    have hpRoot : p ∈ rootFac.support := by simpa [s] using hp
    have hpFac : p ∈ fac.support := hroot_support hpRoot
    simpa [fac] using hpFac
  have hsIrr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p (hsNF p hp)
  have hsNorm : ∀ p ∈ s, normalize p = p := by
    intro p hp
    exact normalize_normalized_factor p (hsNF p hp)
  let B : R := s.prod
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Multiset.prod_ne_zero
    intro hzero
    exact (hsIrr 0 hzero).ne_zero rfl
  have hnormB : normalizedFactors B = s := by
    calc
      normalizedFactors B = s.map normalize := by
        dsimp [B]
        exact normalizedFactors_prod_eq s hsIrr
      _ = s.map id := by
        apply Multiset.map_congr rfl
        intro p hp
        simpa using hsNorm p hp
      _ = s := by simp
  have hfacB : factorization B = rootFac := by
    change Multiset.toFinsupp (normalizedFactors B) = rootFac
    rw [hnormB]
    change Multiset.toFinsupp (Finsupp.toMultiset rootFac) = rootFac
    exact Finsupp.toMultiset_toFinsupp rootFac
  have hfacCube : factorization (B ^ 3) = factorization A := by
    calc
      factorization (B ^ 3) = (3 : ℕ) • factorization B := factorization_pow
      _ = (3 : ℕ) • rootFac := by rw [hfacB]
      _ = fac := hthree_rootFac
      _ = factorization A := rfl
  have hAssoc : Associated (B ^ 3) A :=
    associated_of_factorization_eq (B ^ 3) A
      (pow_ne_zero 3 hB) hA hfacCube
  rcases hAssoc with ⟨eps, heps⟩
  refine ⟨eps, B, ?_⟩
  calc
    A = B ^ 3 * (eps : R) := heps.symm
    _ = (eps : R) * B ^ 3 := mul_comm _ _

private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

private theorem den_monic_cubic_const (a b c : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2 + c * D ^ 3
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D + c * D ^ 2)) D :=
      h1.add_mul_left_left _
    convert h2 using 1 <;> ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

private theorem rat_denom_square_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c).den = x.den ^ 3 := by
    exact_mod_cast den_monic_cubic_const a b c x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

theorem integral_model_monic_const (a b c : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x + c) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      y = (C : ℚ) / (B : ℚ) ^ 3 ∧
      C ^ 2 = A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6 := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ := rat_denom_square_monic_const a b c x y h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A ^ 3 + a * A ^ 2 * B ^ 2 + b * A * B ^ 4 + c * B ^ 6
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  have hsquares : (y * (B : ℚ) ^ 3) ^ 2 = (C : ℚ) ^ 2 := by
    rw [hrat]
    exact_mod_cast (show N = C ^ 2 by simpa [pow_two] using hC)
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with heq | heq
  · refine ⟨A, B, C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm
  · refine ⟨A, B, -C, hBpos, hcop, hx, ?_, ?_⟩
    · apply (eq_div_iff (pow_ne_zero 3 hBne)).2
      simpa using heq
    · simpa [N, pow_two] using hC.symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem even_short_model_mod_thirtyTwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 16 * A ^ 2 * B ^ 2 + 224 * A * B ^ 4 + 784 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            28 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            28 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide

private theorem even_short_model_divisibility {A B C : ℤ}
    (hA : (2 : ℤ) ∣ A) (hB : ¬(2 : ℤ) ∣ B)
    (hmodel : C ^ 2 = A ^ 3 + 16 * A ^ 2 * B ^ 2 +
      224 * A * B ^ 4 + 784 * B ^ 6) :
    (4 : ℤ) ∣ A ∧
      (8 : ℤ) ∣ C - 4 * A * B - 28 * B ^ 3 ∧
      (8 : ℤ) ∣ C + 4 * A * B + 28 * B ^ 3 := by
  have h32 : (C : ZMod 32) ^ 2 = (A : ZMod 32) ^ 3 +
      16 * (A : ZMod 32) ^ 2 * B ^ 2 + 224 * (A : ZMod 32) * B ^ 4 +
        784 * (B : ZMod 32) ^ 6 := by
    have h' := congrArg (fun n : ℤ => (n : ZMod 32)) hmodel
    push_cast at h'
    exact h'
  have hA2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (A : ZMod 32) = 0 := by
    have hz : (A : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mpr hA
    simpa [ZMod.castHom_apply] using hz
  have hB2 : ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2)
      (B : ZMod 32) ≠ 0 := by
    intro hz
    apply hB
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp
    simpa [ZMod.castHom_apply] using hz
  have hc := even_short_model_mod_thirtyTwo (A : ZMod 32)
    (B : ZMod 32) (C : ZMod 32) hA2 hB2 h32
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd A 4).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C - 4 * A * B - 28 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (C + 4 * A * B + 28 * B ^ 3) 8).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Integral coordinates on the rational flex model, normalized so that the
two factors of the descent function have only the prime seven in common. -/
theorem short_flex_integral_model {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ M D R S : ℤ,
      0 < D ∧ Int.gcd M D = 1 ∧
      x = 4 * (M : ℚ) / (D : ℚ) ^ 2 ∧
      y - (4 * x + 28) = 8 * (R : ℚ) / (D : ℚ) ^ 3 ∧
      R * S = M ^ 3 ∧
      S = R + 4 * M * D + 7 * D ^ 3 := by
  have hcubic : y ^ 2 = x ^ 3 + ((16 : ℤ) : ℚ) * x ^ 2 +
      ((224 : ℤ) : ℚ) * x + (784 : ℤ) := by
    norm_num at h ⊢
    exact h
  obtain ⟨A, B, C, hBpos, hcop, hx, hy, hmodel⟩ :=
    integral_model_monic_const 16 224 784 x y hcubic
  have hBneZ : B ≠ 0 := ne_of_gt hBpos
  have hBneQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBneZ
  have hcopI : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hprodRaw :
      (C - 4 * A * B - 28 * B ^ 3) *
          (C + 4 * A * B + 28 * B ^ 3) = A ^ 3 := by
    calc
      (C - 4 * A * B - 28 * B ^ 3) *
          (C + 4 * A * B + 28 * B ^ 3) =
          C ^ 2 - (4 * A * B + 28 * B ^ 3) ^ 2 := by ring
      _ = A ^ 3 := by linear_combination hmodel
  rcases A.even_or_odd with hAeven | hAodd
  · have hA2 : (2 : ℤ) ∣ A := hAeven.two_dvd
    have hcop2B : IsCoprime (2 : ℤ) B :=
      hcopI.of_isCoprime_of_dvd_left hA2
    have hBodd : Odd B := Int.isCoprime_two_left.mp hcop2B
    obtain ⟨hA4, hN8, hP8⟩ :=
      even_short_model_divisibility hA2 (by
        rw [← even_iff_two_dvd]
        exact Int.not_even_iff_odd.mpr hBodd) hmodel
    obtain ⟨M, hM⟩ := hA4
    obtain ⟨R, hR⟩ := hN8
    obtain ⟨S, hS⟩ := hP8
    have hcopMD : IsCoprime M B := by
      rw [hM] at hcopI
      exact hcopI.of_mul_left_right
    have hprod : R * S = M ^ 3 := by
      rw [hR, hS, hM] at hprodRaw
      ring_nf at hprodRaw ⊢
      omega
    have hlin : S = R + 4 * M * B + 7 * B ^ 3 := by
      have h8 : 8 * S = 8 * (R + 4 * M * B + 7 * B ^ 3) := by
        calc
          8 * S = C + 4 * A * B + 28 * B ^ 3 := hS.symm
          _ = (C - 4 * A * B - 28 * B ^ 3) +
              8 * (4 * M * B + 7 * B ^ 3) := by rw [hM]; ring
          _ = 8 * R + 8 * (4 * M * B + 7 * B ^ 3) := by rw [hR]
          _ = 8 * (R + 4 * M * B + 7 * B ^ 3) := by ring
      omega
    refine ⟨M, B, R, S, hBpos,
      Int.isCoprime_iff_gcd_eq_one.mp hcopMD, ?_, ?_, hprod, hlin⟩
    · rw [hx, hM]
      push_cast
      ring
    · rw [hx, hy, hM]
      push_cast
      field_simp [hBneQ]
      have hR' := hR
      rw [hM] at hR'
      have hR'' := congrArg (fun n : ℤ => (n : ℚ)) hR'
      push_cast at hR''
      linear_combination hR''
  · have hcopA2 : IsCoprime A (2 : ℤ) :=
      Int.isCoprime_two_right.mpr hAodd
    have hcopAD : IsCoprime A (2 * B) := hcopA2.mul_right hcopI
    refine ⟨A, 2 * B, C - 4 * A * B - 28 * B ^ 3,
      C + 4 * A * B + 28 * B ^ 3, by positivity,
      Int.isCoprime_iff_gcd_eq_one.mp hcopAD, ?_, ?_, hprodRaw, ?_⟩
    · rw [hx]
      push_cast
      field_simp [hBneQ]
      ring
    · rw [hx, hy]
      push_cast
      field_simp [hBneQ]
      ring
    · ring

private theorem flex_common_prime_eq_seven
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 4 * M * D + 7 * D ^ 3)
    {p : ℕ} (hp : p.Prime) (hpR : (p : ℤ) ∣ R) (hpS : (p : ℤ) ∣ S) :
    p = 7 := by
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpPow : (p : ℤ) ∣ M ^ 3 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpR S
  have hpM : (p : ℤ) ∣ M := hpInt.dvd_of_dvd_pow hpPow
  have hpDiff : (p : ℤ) ∣ S - R := dvd_sub hpS hpR
  have hpSum : (p : ℤ) ∣ 4 * M * D + 7 * D ^ 3 := by
    rw [hlin] at hpDiff
    convert hpDiff using 1 <;> ring
  have hpFirst : (p : ℤ) ∣ 4 * M * D := by
    rcases hpM with ⟨k, hk⟩
    refine ⟨4 * k * D, ?_⟩
    rw [hk]
    ring
  have hpTail : (p : ℤ) ∣ 7 * D ^ 3 := by
    have := dvd_sub hpSum hpFirst
    rcases this with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    linear_combination hk
  have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hpD : ¬(p : ℤ) ∣ D := by
    intro hpD
    exact hpInt.not_unit (hcopI.isUnit_of_dvd' hpM hpD)
  rcases hpInt.dvd_mul.mp hpTail with hp7 | hpD3
  · have hp7Nat : p ∣ 7 := by exact_mod_cast hp7
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hp7Nat with hp1 | hp7'
    · exact (hp.ne_one hp1).elim
    · exact hp7'
  · exact (hpD (hpInt.dvd_of_dvd_pow hpD3)).elim

private theorem isCoprime_of_common_prime_eq_seven {R S : ℤ}
    (hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R → (p : ℤ) ∣ S → p = 7)
    (hnotBoth : ¬((7 : ℤ) ∣ R ∧ (7 : ℤ) ∣ S)) : IsCoprime R S := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hcop
  obtain ⟨p, hp, hpR, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpR' : (p : ℤ) ∣ R := Int.natCast_dvd.mpr hpR
  have hpS' : (p : ℤ) ∣ S := Int.natCast_dvd.mpr hpS
  have hp7 := hsupport hp hpR' hpS'
  subst p
  exact hnotBoth ⟨hpR', hpS'⟩

/-- The rational-flex descent function has one of the three cube classes
`1`, `7`, and `49`. -/
theorem flex_factor_cubeclass
    {M D R S : ℤ} (hcop : Int.gcd M D = 1)
    (hprod : R * S = M ^ 3)
    (hlin : S = R + 4 * M * D + 7 * D ^ 3) :
    ∃ q : ℤ, R = q ^ 3 ∨ R = 7 * q ^ 3 ∨ R = 49 * q ^ 3 := by
  have hsupport : ∀ {p : ℕ}, p.Prime → (p : ℤ) ∣ R → (p : ℤ) ∣ S → p = 7 :=
    fun {_p} hp hpR hpS => flex_common_prime_eq_seven hcop hprod hlin hp hpR hpS
  by_cases h7R : (7 : ℤ) ∣ R
  · have h7Mpow : (7 : ℤ) ∣ M ^ 3 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left h7R S
    have h7M : (7 : ℤ) ∣ M :=
      Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7Mpow
    have h7S : (7 : ℤ) ∣ S := by
      rw [hlin]
      have hmid : (7 : ℤ) ∣ 4 * M * D := by
        rcases h7M with ⟨m, hm⟩
        refine ⟨4 * m * D, ?_⟩
        rw [hm]
        ring
      exact dvd_add (dvd_add h7R hmid) (dvd_mul_right 7 (D ^ 3))
    obtain ⟨R1, hR1⟩ := h7R
    obtain ⟨S1, hS1⟩ := h7S
    obtain ⟨M1, hM1⟩ := h7M
    have hprod1 : R1 * S1 = 7 * M1 ^ 3 := by
      rw [hR1, hS1, hM1] at hprod
      ring_nf at hprod ⊢
      omega
    have hlin1 : S1 = R1 + 4 * M1 * D + D ^ 3 := by
      rw [hR1, hS1, hM1] at hlin
      ring_nf at hlin ⊢
      omega
    have hnotBoth1 : ¬((7 : ℤ) ∣ R1 ∧ (7 : ℤ) ∣ S1) := by
      rintro ⟨h7R1, h7S1⟩
      obtain ⟨r, hr⟩ := h7R1
      obtain ⟨s, hs⟩ := h7S1
      have hM1cube : M1 ^ 3 = 7 * (r * s) := by
        rw [hr, hs] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have h7M1pow : (7 : ℤ) ∣ M1 ^ 3 := ⟨r * s, hM1cube⟩
      have h7M1 : (7 : ℤ) ∣ M1 :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7M1pow
      obtain ⟨m, hm⟩ := h7M1
      have hDcube : D ^ 3 = 7 * (s - r - 4 * m * D) := by
        rw [hr, hs, hm] at hlin1
        ring_nf at hlin1 ⊢
        omega
      have h7Dpow : (7 : ℤ) ∣ D ^ 3 := ⟨s - r - 4 * m * D, hDcube⟩
      have h7D : (7 : ℤ) ∣ D :=
        Int.Prime.dvd_pow' (by norm_num : Nat.Prime 7) h7Dpow
      have hcopI : IsCoprime M D := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have hu : IsUnit (7 : ℤ) :=
        hcopI.isUnit_of_dvd' (show (7 : ℤ) ∣ M by exact ⟨M1, hM1⟩) h7D
      rw [Int.isUnit_iff_abs_eq] at hu
      norm_num at hu
    have hcop1 : IsCoprime R1 S1 :=
      isCoprime_of_common_prime_eq_seven
        (fun {_p} hp hpR hpS => hsupport hp
          (hR1 ▸ dvd_mul_of_dvd_right hpR 7)
          (hS1 ▸ dvd_mul_of_dvd_right hpS 7)) hnotBoth1
    by_cases h7R1 : (7 : ℤ) ∣ R1
    · obtain ⟨R2, hR2⟩ := h7R1
      have hprod2 : R2 * S1 = M1 ^ 3 := by
        rw [hR2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R2 S1 := by
        rw [hR2] at hcop1
        exact hcop1.of_mul_left_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2 (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inr ?_)⟩
      rw [hR1, hR2, hq]
      ring
    · have h7S1 : (7 : ℤ) ∣ S1 := by
        have h7prod : (7 : ℤ) ∣ R1 * S1 := by rw [hprod1]; exact dvd_mul_right 7 _
        exact ((by norm_num : Prime (7 : ℤ)).dvd_mul.mp h7prod).resolve_left h7R1
      obtain ⟨S2, hS2⟩ := h7S1
      have hprod2 : R1 * S2 = M1 ^ 3 := by
        rw [hS2] at hprod1
        ring_nf at hprod1 ⊢
        omega
      have hcop2 : IsCoprime R1 S2 := by
        rw [hS2] at hcop1
        exact hcop1.of_mul_right_right
      obtain ⟨q, hq⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left hcop2 (show Odd 3 by decide) hprod2
      refine ⟨q, Or.inr (Or.inl ?_)⟩
      rw [hR1, hq]
  · have hcopRS : IsCoprime R S :=
      isCoprime_of_common_prime_eq_seven hsupport (fun h => h7R h.1)
    obtain ⟨q, hq⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left hcopRS (show Odd 3 by decide) hprod
    exact ⟨q, Or.inl hq⟩

theorem short_alpha_cubeclass {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ r : ℚ,
      y - (4 * x + 28) = r ^ 3 ∨
      y - (4 * x + 28) = 7 * r ^ 3 ∨
      y - (4 * x + 28) = 49 * r ^ 3 := by
  obtain ⟨M, D, R, S, hDpos, hcop, _hx, halpha, hprod, hlin⟩ :=
    short_flex_integral_model h
  obtain ⟨q, hq | hq | hq⟩ := flex_factor_cubeclass hcop hprod hlin
  all_goals
    refine ⟨2 * (q : ℚ) / (D : ℚ), ?_⟩
  · left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; left
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring
  · right; right
    rw [halpha, hq]
    push_cast
    field_simp [Int.cast_ne_zero.mpr (ne_of_gt hDpos)]
    ring

/-! Experimental use of Mathlib's cyclotomic PID and Dirichlet-unit APIs. -/

abbrev N35K3 := CyclotomicField 3 ℚ
abbrev N35O3 := 𝓞 N35K3

local instance n35K3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance n35O3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

noncomputable def n35Zeta : N35K3 :=
  IsCyclotomicExtension.zeta 3 ℚ N35K3

theorem n35Zeta_isPrimitive : IsPrimitiveRoot n35Zeta 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ N35K3

theorem n35Zeta_relation : n35Zeta ^ 2 + n35Zeta + 1 = 0 := by
  simpa [add_assoc, add_comm, add_left_comm] using
    n35Zeta_isPrimitive.isRoot_cyclotomic (by norm_num)

noncomputable def n35ConjK : N35K3 ≃ₐ[ℚ] N35K3 :=
  IsCyclotomicExtension.fromZetaAut
    (n35Zeta_isPrimitive.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3))

@[simp] theorem n35ConjK_zeta :
    n35ConjK n35Zeta = n35Zeta ^ 2 := by
  exact IsCyclotomicExtension.fromZetaAut_spec
    (n35Zeta_isPrimitive.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3))

theorem n35ConjK_involutive : Function.Involutive n35ConjK := by
  have heq : n35ConjK.trans n35ConjK = AlgEquiv.refl := by
    apply AlgEquiv.coe_algHom_injective
    apply (n35Zeta_isPrimitive.powerBasis ℚ).algHom_ext
    rw [AlgEquiv.coe_algHom, AlgEquiv.coe_algHom,
      AlgEquiv.trans_apply,
      IsPrimitiveRoot.powerBasis_gen, n35ConjK_zeta, map_pow,
      n35ConjK_zeta]
    calc
      (n35Zeta ^ 2) ^ 2 = n35Zeta * n35Zeta ^ 3 := by ring
      _ = n35Zeta := by rw [n35Zeta_isPrimitive.pow_eq_one]; ring
  intro x
  have hx := DFunLike.congr_fun heq x
  exact hx

noncomputable def n35ConjO : N35O3 ≃+* N35O3 :=
  NumberField.RingOfIntegers.mapRingEquiv n35ConjK.toRingEquiv

@[simp] theorem n35ConjO_coe (x : N35O3) :
    ((n35ConjO x : N35O3) : N35K3) = n35ConjK (x : N35K3) := by
  exact NumberField.RingOfIntegers.mapRingEquiv_apply _ _

theorem n35ConjO_involutive : Function.Involutive n35ConjO := by
  intro x
  ext
  simp only [n35ConjO_coe]
  exact n35ConjK_involutive x

noncomputable def n35Omega : N35O3 := n35Zeta_isPrimitive.toInteger

@[simp] theorem n35Omega_coe : (n35Omega : N35K3) = n35Zeta := rfl

theorem n35Omega_relation : n35Omega ^ 2 + n35Omega + 1 = 0 := by
  ext
  exact n35Zeta_relation

theorem n35Omega_cube : n35Omega ^ 3 = 1 := by
  unfold n35Omega
  exact n35Zeta_isPrimitive.toInteger_cube_eq_one

@[simp] theorem n35ConjO_omega : n35ConjO n35Omega = n35Omega ^ 2 := by
  ext
  rw [n35ConjO_coe]
  exact n35ConjK_zeta

noncomputable def n35SqrtNegThree : N35O3 := 1 + 2 * n35Omega

theorem n35SqrtNegThree_sq : n35SqrtNegThree ^ 2 = -3 := by
  unfold n35SqrtNegThree
  linear_combination 4 * n35Omega_relation

@[simp] theorem n35ConjO_sqrtNegThree :
    n35ConjO n35SqrtNegThree = -n35SqrtNegThree := by
  unfold n35SqrtNegThree
  rw [map_add, map_mul, map_one, map_ofNat, n35ConjO_omega]
  linear_combination 2 * n35Omega_relation

theorem n35O3_exists_coords (x : N35O3) :
    ∃ a b : ℤ, x = (a : N35O3) + (b : N35O3) * n35Omega := by
  let pb := n35Zeta_isPrimitive.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [IsPrimitiveRoot.integralPowerBasis_dim]
    decide
  let B : Module.Basis (Fin 2) ℤ N35O3 :=
    pb.basis.reindex (finCongr hdim)
  let a : ℤ := B.repr x 0
  let b : ℤ := B.repr x 1
  refine ⟨a, b, ?_⟩
  have hB0 : B 0 = 1 := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hB1 : B 1 = n35Omega := by
    simp [B, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pb,
      IsPrimitiveRoot.integralPowerBasis_gen, n35Omega]
  have hsum := B.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simpa [a, b, hB0, hB1, Algebra.smul_def] using hsum.symm

def n35NormForm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

theorem n35_coord_mul_conj (a b : ℤ) :
    ((a : N35O3) + (b : N35O3) * n35Omega) *
        n35ConjO ((a : N35O3) + (b : N35O3) * n35Omega) =
      (n35NormForm a b : N35O3) := by
  have hs : n35Omega ^ 2 = -n35Omega - 1 := by
    linear_combination n35Omega_relation
  simp only [map_add, map_mul, map_intCast, n35ConjO_omega]
  push_cast
  unfold n35NormForm
  ring_nf
  rw [hs, n35Omega_cube]
  push_cast
  ring

private theorem n35NormForm_nonneg (a b : ℤ) : 0 ≤ n35NormForm a b := by
  have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
  unfold n35NormForm
  nlinarith

private theorem n35NormForm_eq_zero_iff (a b : ℤ) :
    n35NormForm a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsq1 : 0 ≤ (2 * a - b) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ b ^ 2 := sq_nonneg _
    unfold n35NormForm at h
    have hb : b = 0 := by nlinarith
    subst b
    norm_num at h ⊢
    nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num [n35NormForm]

private theorem n35NormForm_ne_two_mod_three :
    ∀ a b : ZMod 3, a ^ 2 - a * b + b ^ 2 ≠ 2 := by
  decide

theorem n35NormForm_ne_two (a b : ℤ) : n35NormForm a b ≠ 2 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  simpa [n35NormForm] using h'

theorem n35NormForm_ne_five (a b : ℤ) : n35NormForm a b ≠ 5 := by
  intro h
  apply n35NormForm_ne_two_mod_three (a : ZMod 3) (b : ZMod 3)
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  norm_num [n35NormForm] at h' ⊢
  exact h'

theorem n35_coord_norm_pos {x : N35O3} {a b : ℤ} (hx : x ≠ 0)
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega) :
    0 < n35NormForm a b := by
  have hn := n35NormForm_nonneg a b
  apply lt_of_le_of_ne hn
  intro hzero
  have hab := (n35NormForm_eq_zero_iff a b).mp hzero.symm
  apply hx
  rw [hcoord, hab.1, hab.2]
  norm_num

theorem n35_isUnit_of_coord_norm_one {x : N35O3} {a b : ℤ}
    (hcoord : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hnorm : n35NormForm a b = 1) : IsUnit x := by
  apply IsUnit.of_mul_eq_one (n35ConjO x)
  rw [hcoord, n35_coord_mul_conj, hnorm]
  norm_num

theorem n35_coord_norm_mul_eq_sq {x y : N35O3} {a b c d r : ℤ}
    (hx : x = (a : N35O3) + (b : N35O3) * n35Omega)
    (hy : y = (c : N35O3) + (d : N35O3) * n35Omega)
    (hxy : x * y = (r : N35O3)) :
    n35NormForm a b * n35NormForm c d = r ^ 2 := by
  have ho :
      ((n35NormForm a b * n35NormForm c d : ℤ) : N35O3) =
        ((r ^ 2 : ℤ) : N35O3) := by
    push_cast
    rw [← n35_coord_mul_conj a b, ← n35_coord_mul_conj c d,
      ← hx, ← hy]
    calc
      (x * n35ConjO x) * (y * n35ConjO y) =
          (x * y) * n35ConjO (x * y) := by rw [map_mul]; ring
      _ = (r : N35O3) * n35ConjO (r : N35O3) := by rw [hxy]
      _ = (r : N35O3) ^ 2 := by simp; ring
  exact_mod_cast ho

private theorem n35_intCast_not_isUnit {p : ℤ} (hp : 2 ≤ p) :
    ¬IsUnit (p : N35O3) := by
  intro hu
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
  obtain ⟨c, d, hvcoord⟩ := n35O3_exists_coords v
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hv
    exact zero_ne_one hv
  have hnormpos := n35_coord_norm_pos hv0 hvcoord
  have hnorm := n35_coord_norm_mul_eq_sq
    (x := (p : N35O3)) (y := v) (a := p) (b := 0)
    (c := c) (d := d) (r := 1) (by ring) hvcoord hv
  have hpform : n35NormForm p 0 = p ^ 2 := by
    simp [n35NormForm]
  rw [hpform] at hnorm
  have hpSq : 4 ≤ p ^ 2 := by nlinarith [sq_nonneg p]
  have hN : 1 ≤ n35NormForm c d := by omega
  have hle : p ^ 2 ≤ p ^ 2 * n35NormForm c d :=
    by simpa using mul_le_mul_of_nonneg_left hN (sq_nonneg p)
  rw [hnorm] at hle
  omega

theorem n35_two_irreducible : Irreducible (2 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNx : n35NormForm a b = 2 := by nlinarith
  exact n35NormForm_ne_two a b hNx

theorem n35_five_irreducible : Irreducible (5 : N35O3) := by
  rw [irreducible_iff]
  refine ⟨n35_intCast_not_isUnit (by norm_num), ?_⟩
  intro x y hxy
  by_cases hxU : IsUnit x
  · exact Or.inl hxU
  by_cases hyU : IsUnit y
  · exact Or.inr hyU
  exfalso
  obtain ⟨a, b, hxcoord⟩ := n35O3_exists_coords x
  obtain ⟨c, d, hycoord⟩ := n35O3_exists_coords y
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    norm_num at hxy
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at hxy
    norm_num at hxy
  have hNxpos := n35_coord_norm_pos hx0 hxcoord
  have hNypos := n35_coord_norm_pos hy0 hycoord
  have hNx1 : n35NormForm a b ≠ 1 := by
    intro h
    exact hxU (n35_isUnit_of_coord_norm_one hxcoord h)
  have hNy1 : n35NormForm c d ≠ 1 := by
    intro h
    exact hyU (n35_isUnit_of_coord_norm_one hycoord h)
  have hprod := n35_coord_norm_mul_eq_sq hxcoord hycoord hxy.symm
  norm_num at hprod
  have hNxlo : 2 ≤ n35NormForm a b := by omega
  have hNylo : 2 ≤ n35NormForm c d := by omega
  have hNxhi : n35NormForm a b ≤ 12 := by nlinarith
  have hNx : n35NormForm a b = 5 := by
    interval_cases hN : n35NormForm a b <;> omega
  exact n35NormForm_ne_five a b hNx

noncomputable def n35Rho : N35K3 := 1 + n35Zeta

theorem n35Rho_sq : n35Rho ^ 2 = n35Zeta := by
  unfold n35Rho
  linear_combination n35Zeta_relation

theorem n35Rho_cube : n35Rho ^ 3 = -1 := by
  calc
    n35Rho ^ 3 = n35Rho * n35Rho ^ 2 := by ring
    _ = (1 + n35Zeta) * n35Zeta := by rw [n35Rho_sq]; rfl
    _ = -1 := by linear_combination n35Zeta_relation

noncomputable def n35ZetaUnit : N35O3ˣ :=
  ((n35Zeta_isPrimitive.toInteger_isPrimitiveRoot).isUnit (by norm_num)).unit

theorem n35Omega_sub_one_prime : Prime (n35Omega - 1) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ N35K3 := by
    simpa using n35K3_isCyclotomic
  simpa [n35Omega] using
    (IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two
      (p := 3) (k := 0) n35Zeta_isPrimitive (by norm_num))

theorem n35SqrtNegThree_prime : Prime n35SqrtNegThree := by
  have hassoc : Associated (n35Omega - 1) n35SqrtNegThree := by
    refine ⟨-n35ZetaUnit, ?_⟩
    change (n35Omega - 1) * (-n35Omega) = 1 + 2 * n35Omega
    have hs : n35Omega ^ 2 = -n35Omega - 1 := by
      linear_combination n35Omega_relation
    rw [mul_neg]
    change -((n35Omega - 1) * n35Omega) = _
    rw [show (n35Omega - 1) * n35Omega =
      n35Omega ^ 2 - n35Omega by ring, hs]
    ring
  exact (hassoc.prime_iff).mp n35Omega_sub_one_prime

theorem n35K3_unit_mod_cube (u : N35O3ˣ) :
    (∃ v : N35O3ˣ, u = v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit * v ^ 3) ∨
      (∃ v : N35O3ˣ, u = n35ZetaUnit ^ 2 * v ^ 3) := by
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem
    n35Zeta_isPrimitive u
  change u ∈ [1, -1, n35ZetaUnit, -n35ZetaUnit,
    n35ZetaUnit ^ 2, -(n35ZetaUnit ^ 2)] at hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · exact Or.inl ⟨1, by simpa using h⟩
  · exact Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩
  · exact Or.inr (Or.inl ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inl ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)
  · exact Or.inr (Or.inr ⟨1, by simpa using h⟩)
  · exact Or.inr (Or.inr ⟨-1, by rw [h]; ext; simp [pow_succ]⟩)

theorem n35_dual_integral_model {s t : ℚ}
    (h : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ m n d : ℤ,
      0 < d ∧ Int.gcd m d = 1 ∧
      s = (m : ℚ) / (d : ℚ) ^ 2 ∧
      t = (n : ℚ) / (d : ℚ) ^ 3 ∧
      n ^ 2 = m ^ 3 - 3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2 := by
  have hcubic : t ^ 2 = s ^ 3 + ((-432 : ℤ) : ℚ) * s ^ 2 +
      ((-108000 : ℤ) : ℚ) * s + ((-6750000 : ℤ) : ℚ) := by
    norm_num at h ⊢
    nlinarith
  obtain ⟨m, d, n, hd, hcop, hs, ht, hmodel⟩ :=
    integral_model_monic_const (-432) (-108000) (-6750000) s t hcubic
  refine ⟨m, n, d, hd, hcop, hs, ht, ?_⟩
  linear_combination hmodel

noncomputable def n35DualA (m n d : ℤ) : N35O3 :=
  (n : N35O3) - n35SqrtNegThree *
    (d * (12 * m + 1500 * d ^ 2) : ℤ)

@[simp] theorem n35ConjO_dualA (m n d : ℤ) :
    n35ConjO (n35DualA m n d) =
      (n : N35O3) + n35SqrtNegThree *
      (d * (12 * m + 1500 * d ^ 2) : ℤ) := by
  unfold n35DualA
  rw [map_sub, map_intCast, map_mul, n35ConjO_sqrtNegThree,
    map_intCast]
  ring

theorem n35DualA_mul_conj {m n d : ℤ}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    n35DualA m n d * n35ConjO (n35DualA m n d) =
      (m : N35O3) ^ 3 := by
  rw [n35ConjO_dualA]
  unfold n35DualA
  have hc := congrArg (fun z : ℤ => (z : N35O3)) hcurve
  push_cast at hc ⊢
  ring_nf
  rw [n35SqrtNegThree_sq]
  linear_combination hc

private theorem n35_nonsymmetric_not_dvd_prime
    {pi r : N35O3} (hpi : Irreducible pi) (hr : Prime r)
    (hrconj : Associated (n35ConjO r) r)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ r := by
  intro hp
  have hpr : Associated pi r :=
    (hpi.dvd_irreducible_iff_associated hr.irreducible).mp hp
  have hcpr : Associated (n35ConjO pi) (n35ConjO r) :=
    hpr.map n35ConjO
  exact hnself (hpr.trans (hcpr.trans hrconj).symm)

private theorem n35_nonsymmetric_not_dvd_two
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) : ¬pi ∣ (2 : N35O3) := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35_two_irreducible.prime _ hnself
  have hmap : n35ConjO (2 : N35O3) = 2 := by
    ext
    rw [n35ConjO_coe]
    exact map_ofNat n35ConjK 2
  rw [hmap]

private theorem n35_nonsymmetric_not_dvd_five
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) : ¬pi ∣ (5 : N35O3) := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35_five_irreducible.prime _ hnself
  have hmap : n35ConjO (5 : N35O3) = 5 := by
    ext
    rw [n35ConjO_coe]
    exact map_ofNat n35ConjK 5
  rw [hmap]

private theorem n35_nonsymmetric_not_dvd_sqrtNegThree
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ n35SqrtNegThree := by
  apply n35_nonsymmetric_not_dvd_prime hpi n35SqrtNegThree_prime _ hnself
  rw [n35ConjO_sqrtNegThree]
  exact Associated.rfl.neg_left

theorem n35DualA_no_common_nonsymmetric_factor
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬(pi ∣ n35DualA m n d ∧ n35ConjO pi ∣ n35DualA m n d) := by
  rintro ⟨hpA, hpcA⟩
  have hpConjA : pi ∣ n35ConjO (n35DualA m n d) := by
    have hmapped := map_dvd n35ConjO hpcA
    simpa only [n35ConjO_involutive pi] using hmapped
  have hp2 : ¬pi ∣ (2 : N35O3) :=
    n35_nonsymmetric_not_dvd_two hpi hnself
  have hpq : ¬pi ∣ n35SqrtNegThree :=
    n35_nonsymmetric_not_dvd_sqrtNegThree hpi hnself
  have hp5 : ¬pi ∣ (5 : N35O3) :=
    n35_nonsymmetric_not_dvd_five hpi hnself
  have hpPrime : Prime pi := hpi.prime
  have hp2n : pi ∣ (2 * n : ℤ) := by
    have hs := dvd_add hpA hpConjA
    rw [n35ConjO_dualA] at hs
    unfold n35DualA at hs
    convert hs using 1 <;> push_cast <;> ring
  have hpn : pi ∣ (n : N35O3) := by
    have hsplit := hpPrime.dvd_mul.mp (by simpa only [Int.cast_mul] using hp2n)
    exact hsplit.resolve_left hp2
  have hpMpow : pi ∣ (m : N35O3) ^ 3 := by
    rw [← n35DualA_mul_conj hcurve]
    exact dvd_mul_of_dvd_left hpA _
  have hpm : pi ∣ (m : N35O3) := hpPrime.dvd_of_dvd_pow hpMpow
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  have hp2qC : pi ∣ (2 : N35O3) * n35SqrtNegThree * (C : N35O3) := by
    have hdif := dvd_sub hpA hpConjA
    rw [n35ConjO_dualA] at hdif
    unfold n35DualA at hdif
    dsimp only [C]
    convert hdif.neg_right using 1 <;> push_cast <;> ring
  have hpqC : pi ∣ n35SqrtNegThree * (C : N35O3) :=
    (hpPrime.dvd_mul.mp (by simpa [mul_assoc] using hp2qC)).resolve_left hp2
  have hpC : pi ∣ (C : N35O3) :=
    (hpPrime.dvd_mul.mp hpqC).resolve_left hpq
  have hpd : ¬pi ∣ (d : N35O3) := by
    intro hpd
    have hcopI : IsCoprime (m : N35O3) (d : N35O3) := by
      have hz : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      exact hz.map (Int.castRingHom N35O3)
    exact hpi.not_isUnit (hcopI.isUnit_of_dvd' hpm hpd)
  have hpL : pi ∣ (12 * m + 1500 * d ^ 2 : ℤ) := by
    have hs : pi ∣ (d : N35O3) *
        (12 * m + 1500 * d ^ 2 : ℤ) := by
      simpa [C] using hpC
    exact (hpPrime.dvd_mul.mp hs).resolve_left hpd
  have hp1500d2 : pi ∣ (1500 : N35O3) * (d : N35O3) ^ 2 := by
    have hs := dvd_sub hpL (dvd_mul_of_dvd_right hpm (12 : N35O3))
    convert hs using 1 <;> push_cast <;> ring
  have hp1500 : pi ∣ (1500 : N35O3) := by
    rcases hpPrime.dvd_mul.mp hp1500d2 with hp1500 | hpd2
    · exact hp1500
    · exact (hpd (hpPrime.dvd_of_dvd_pow hpd2)).elim
  have hfactor : (1500 : N35O3) =
      (2 : N35O3) ^ 2 * ((3 : N35O3) * (5 : N35O3) ^ 3) := by norm_num
  rw [hfactor] at hp1500
  rcases hpPrime.dvd_mul.mp hp1500 with hp2sq | hp35
  · exact hp2 (hpPrime.dvd_of_dvd_pow hp2sq)
  · rcases hpPrime.dvd_mul.mp hp35 with hp3 | hp5cube
    · have hpneg3 : pi ∣ -(3 : N35O3) := hp3.neg_right
      have hpq2 : pi ∣ n35SqrtNegThree ^ 2 := by
        rwa [n35SqrtNegThree_sq]
      exact hpq (hpPrime.dvd_of_dvd_pow hpq2)
    · exact hp5 (hpPrime.dvd_of_dvd_pow hp5cube)

theorem n35DualA_unit_mul_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    ∃ eps : N35O3ˣ, ∃ B : N35O3,
      n35DualA m n d = (eps : N35O3) * B ^ 3 := by
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    have hd0 : d ≠ 0 := ne_of_gt hd
    nlinarith [sq_nonneg n, sq_pos_of_ne_zero hd0]
  have hA0 : n35DualA m n d ≠ 0 := by
    intro hA
    have hp := n35DualA_mul_conj hcurve
    rw [hA, zero_mul] at hp
    exact (pow_ne_zero 3 (Int.cast_ne_zero.mpr hm0)) hp.symm
  apply n35_unit_mul_cube_of_mul_conj_cube n35ConjO
    n35ConjO_involutive hA0 (n35DualA_mul_conj hcurve)
  intro pi hpi
  by_cases hs : Associated pi (n35ConjO pi)
  · exact Or.inl hs
  · exact Or.inr (n35DualA_no_common_nonsymmetric_factor hd hcop hcurve hpi hs)

theorem n35DualA_three_cubeclasses
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    (∃ B : N35O3, n35DualA m n d = B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3, n35DualA m n d = n35ZetaUnit ^ 2 * B ^ 3) := by
  obtain ⟨eps, B, hA⟩ := n35DualA_unit_mul_cube hd hcop hcurve
  rcases n35K3_unit_mod_cube eps with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; right
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring

theorem n35_coords_injective {a b c d : ℤ}
    (h : (a : N35O3) + (b : N35O3) * n35Omega =
      (c : N35O3) + (d : N35O3) * n35Omega) :
    a = c ∧ b = d := by
  have hc := congrArg n35ConjO h
  simp only [map_add, map_mul, map_intCast, n35ConjO_omega] at hc
  have hdiff : ((b - d : ℤ) : N35O3) *
      (n35Omega - n35Omega ^ 2) = 0 := by
    push_cast
    linear_combination h - hc
  have homega : n35Omega - n35Omega ^ 2 = n35SqrtNegThree := by
    unfold n35SqrtNegThree
    push_cast
    linear_combination -n35Omega_relation
  rw [homega] at hdiff
  have hq0 : n35SqrtNegThree ≠ 0 := by
    intro hq
    have hs := n35SqrtNegThree_sq
    rw [hq] at hs
    norm_num at hs
  have hbdO : ((b - d : ℤ) : N35O3) = 0 :=
    (mul_eq_zero.mp hdiff).resolve_right hq0
  have hbd : b = d := by
    have : b - d = 0 := by exact_mod_cast hbdO
    omega
  subst d
  have hacO : ((a - c : ℤ) : N35O3) = 0 := by
    push_cast
    linear_combination h
  have hac : a - c = 0 := by exact_mod_cast hacO
  exact ⟨by omega, rfl⟩

theorem n35_coord_cube (a b : ℤ) :
    ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 =
      (a ^ 3 + b ^ 3 - 3 * a * b ^ 2 : ℤ) +
        (3 * a ^ 2 * b - 3 * a * b ^ 2 : ℤ) * n35Omega := by
  have hs : n35Omega ^ 2 = -n35Omega - 1 := by
    linear_combination n35Omega_relation
  push_cast
  ring_nf
  rw [hs, n35Omega_cube]
  push_cast
  ring

@[simp] theorem n35ZetaUnit_val : (n35ZetaUnit : N35O3) = n35Omega := rfl

theorem n35ZetaUnit_norm_one :
    (n35ZetaUnit : N35O3) * n35ConjO (n35ZetaUnit : N35O3) = 1 := by
  rw [n35ZetaUnit_val, n35ConjO_omega]
  rw [show n35Omega * n35Omega ^ 2 = n35Omega ^ 3 by ring,
    n35Omega_cube]

theorem n35ZetaUnit_sq_norm_one :
    (n35ZetaUnit : N35O3) ^ 2 *
        n35ConjO ((n35ZetaUnit : N35O3) ^ 2) = 1 := by
  calc
    (n35ZetaUnit : N35O3) ^ 2 *
        n35ConjO ((n35ZetaUnit : N35O3) ^ 2) =
        ((n35ZetaUnit : N35O3) *
          n35ConjO (n35ZetaUnit : N35O3)) ^ 2 := by rw [map_pow]; ring
    _ = 1 := by rw [n35ZetaUnit_norm_one]; norm_num

theorem n35_m_eq_coord_norm_of_unit_cube
    {m n d a b : ℤ} {u : N35O3}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    (hu : u * n35ConjO u = 1)
    (hclass : n35DualA m n d =
      u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) :
    m = n35NormForm a b := by
  have heqO : (m : N35O3) ^ 3 = (n35NormForm a b : N35O3) ^ 3 := by
    calc
      (m : N35O3) ^ 3 =
          n35DualA m n d * n35ConjO (n35DualA m n d) :=
        (n35DualA_mul_conj hcurve).symm
      _ = (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
          n35ConjO (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) := by
        rw [hclass]
      _ = (n35NormForm a b : N35O3) ^ 3 := by
        rw [map_mul, map_pow]
        rw [show (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
            (n35ConjO u * n35ConjO
              ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) =
            (u * n35ConjO u) *
              (((a : N35O3) + (b : N35O3) * n35Omega) *
                n35ConjO ((a : N35O3) + (b : N35O3) * n35Omega)) ^ 3 by ring,
          hu, one_mul, n35_coord_mul_conj]
  have heqZ : m ^ 3 = n35NormForm a b ^ 3 := by exact_mod_cast heqO
  exact (show Odd 3 by decide).pow_injective heqZ

def n35CoverRho (X Y Z : ℤ) : ℤ :=
  X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

def n35CoverRhoSq (X Y Z : ℤ) : ℤ :=
  X ^ 3 + 3 * Y ^ 3 + 3000 * Z ^ 3 - 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem n35CoverRho_mod_twentySeven :
    ∀ X Y Z : ZMod 27,
      X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem n35CoverRhoSq_mod_twentySeven :
    ∀ X Y Z : ZMod 27,
      X ^ 3 + 3 * Y ^ 3 + 3000 * Z ^ 3 - 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by
  decide

theorem n35CoverRho_all_three_dvd {X Y Z : ℤ}
    (h : n35CoverRho X Y Z = 0) : 3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have h27 := congrArg (fun z : ℤ => (z : ZMod 27)) h
  unfold n35CoverRho at h27
  push_cast at h27
  have hc := n35CoverRho_mod_twentySeven (X : ZMod 27)
    (Y : ZMod 27) (Z : ZMod 27) h27
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 3).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Z 3).mp
    simpa [ZMod.castHom_apply] using hc.2.2

theorem n35CoverRhoSq_all_three_dvd {X Y Z : ℤ}
    (h : n35CoverRhoSq X Y Z = 0) : 3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have h27 := congrArg (fun z : ℤ => (z : ZMod 27)) h
  unfold n35CoverRhoSq at h27
  push_cast at h27
  have hc := n35CoverRhoSq_mod_twentySeven (X : ZMod 27)
    (Y : ZMod 27) (Z : ZMod 27) h27
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 3).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Z 3).mp
    simpa [ZMod.castHom_apply] using hc.2.2

private theorem n35_common_three_contradiction {m d a b : ℤ}
    (hcop : Int.gcd m d = 1) (hm : m = n35NormForm a b)
    (h3x : (3 : ℤ) ∣ 2 * a - b) (h3b : (3 : ℤ) ∣ b)
    (h3z : (3 : ℤ) ∣ 2 * d) : False := by
  have h32a : (3 : ℤ) ∣ 2 * a := by
    simpa [sub_eq_add_neg, add_assoc] using dvd_add h3x h3b
  have h3a : (3 : ℤ) ∣ a :=
    ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp h32a).resolve_left (by norm_num)
  have h3d : (3 : ℤ) ∣ d :=
    ((by norm_num : Prime (3 : ℤ)).dvd_mul.mp h3z).resolve_left (by norm_num)
  obtain ⟨ka, hka⟩ := h3a
  obtain ⟨kb, hkb⟩ := h3b
  have h3m : (3 : ℤ) ∣ m := by
    refine ⟨3 * (ka ^ 2 - ka * kb + kb ^ 2), ?_⟩
    rw [hm, hka, hkb]
    unfold n35NormForm
    ring
  have hcopI : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hu : IsUnit (3 : ℤ) := hcopI.isUnit_of_dvd' h3m h3d
  rw [Int.isUnit_iff_abs_eq] at hu
  norm_num at hu

theorem n35DualA_not_zeta_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : n35DualA m n d = (n35ZetaUnit : N35O3) * B ^ 3) : False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : n35DualA m n d = (n35ZetaUnit : N35O3) *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := n35_m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_norm_one hclass'
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((-I : ℤ) : N35O3) + ((R - I : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((-I : ℤ) : N35O3) + ((R - I : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs]
        push_cast
        ring
  have hcoeff : -2 * C = R - I := (n35_coords_injective hcoords).2
  have hG : n35CoverRhoSq (2 * a - b) b (2 * d) = 0 := by
    dsimp [C, R, I] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold n35CoverRhoSq
    linear_combination -8 * hcoeff
  obtain ⟨h3x, h3b, h3z⟩ := n35CoverRhoSq_all_three_dvd hG
  exact n35_common_three_contradiction hcop hm h3x h3b h3z

theorem n35DualA_not_zeta_sq_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : n35DualA m n d = (n35ZetaUnit : N35O3) ^ 2 * B ^ 3) : False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : n35DualA m n d = (n35ZetaUnit : N35O3) ^ 2 *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := n35_m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_sq_norm_one hclass'
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((I - R : ℤ) : N35O3) + ((-R : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) ^ 2 *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((I - R : ℤ) : N35O3) + ((-R : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs, n35Omega_cube]
        push_cast
        ring
  have hcoeff : -2 * C = -R := (n35_coords_injective hcoords).2
  have hG : n35CoverRho (-(2 * a - b)) (-b) (2 * d) = 0 := by
    dsimp [C, R] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold n35CoverRho
    linear_combination -8 * hcoeff
  obtain ⟨h3xneg, h3bneg, h3z⟩ := n35CoverRho_all_three_dvd hG
  have h3x : (3 : ℤ) ∣ 2 * a - b := by
    simpa only [dvd_neg] using h3xneg
  have h3b : (3 : ℤ) ∣ b := by
    simpa only [dvd_neg] using h3bneg
  exact n35_common_three_contradiction hcop hm h3x h3b h3z

theorem n35DualA_is_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (12 * m + 1500 * d ^ 2) ^ 2) :
    ∃ B : N35O3, n35DualA m n d = B ^ 3 := by
  rcases n35DualA_three_cubeclasses hd hcop hcurve with h | h | h
  · exact h
  · obtain ⟨B, hB⟩ := h
    exact (n35DualA_not_zeta_cube hcop hcurve hB).elim
  · obtain ⟨B, hB⟩ := h
    exact (n35DualA_not_zeta_sq_cube hcop hcurve hB).elim

private theorem n35_inverse_short_identity {u v : ℚ} (hv : v + 4 ≠ 0)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (u * (-84 / (v + 4)) / 3) ^ 2 =
      (-84 / (v + 4)) ^ 3 + (4 * (-84 / (v + 4)) + 28) ^ 2 := by
  field_simp [hv]
  linear_combination 7056 * hrel

private theorem n35_inverse_x_identity {u v s : ℚ} (hv : v + 4 ≠ 0)
    (hs : s = u ^ 2 + 3 * v ^ 2)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (9 * (-84 / (v + 4)) ^ 3 + 192 * (-84 / (v + 4)) ^ 2 +
        4032 * (-84 / (v + 4)) + 28224) /
      (-84 / (v + 4)) ^ 2 = s := by
  rw [hs]
  field_simp [hv]
  linear_combination (-7056) * hrel

private theorem n35_inverse_y_identity {u v t : ℚ} (hv : v + 4 ≠ 0)
    (ht : t = u ^ 3 - 9 * u * v ^ 2)
    (hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0) :
    (27 * (-84 / (v + 4)) ^ 3 * (u * (-84 / (v + 4)) / 3) -
        12096 * (-84 / (v + 4)) * (u * (-84 / (v + 4)) / 3) -
        169344 * (u * (-84 / (v + 4)) / 3)) /
      (-84 / (v + 4)) ^ 3 = t := by
  rw [ht]
  field_simp [hv]
  linear_combination (-21168 * u) * hrel

theorem n35_dual_affine_has_three_isogeny_preimage {s t : ℚ}
    (hdual : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 ∧
      (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3 = t := by
  obtain ⟨m, n, d, hd, hcop, hs, ht, hcurve⟩ :=
    n35_dual_integral_model hdual
  obtain ⟨B, hBcube⟩ := n35DualA_is_cube hd hcop hcurve
  obtain ⟨a, b, hBcoord⟩ := n35O3_exists_coords B
  have hclass : n35DualA m n d =
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hBcoord] using hBcube
  have hm : m = n35NormForm a b :=
    n35_m_eq_coord_norm_of_unit_cube (u := (1 : N35O3)) hcurve
      (by simp only [map_one, one_mul])
      (by simpa only [one_mul] using hclass)
  let C : ℤ := d * (12 * m + 1500 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        (R : N35O3) + (I : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
          n35DualA m n d := by
        unfold n35DualA n35SqrtNegThree C
        push_cast
        ring
      _ = ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass
      _ = (R : N35O3) + (I : N35O3) * n35Omega := by
        rw [n35_coord_cube]
  have hreal : n - C = R := (n35_coords_injective hcoords).1
  have himag : -2 * C = I := (n35_coords_injective hcoords).2
  have hrealQ : ((n - C : ℤ) : ℚ) = (R : ℚ) := by exact_mod_cast hreal
  have himagQ : ((-2 * C : ℤ) : ℚ) = (I : ℚ) := by exact_mod_cast himag
  let u : ℚ := (2 * a - b : ℤ) / (2 * d : ℤ)
  let v : ℚ := (b : ℚ) / (2 * d : ℤ)
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hd)
  have hsuv : s = u ^ 2 + 3 * v ^ 2 := by
    rw [hs, hm]
    unfold u v n35NormForm
    push_cast
    field_simp [hdQ]
    ring
  have htuv : t = u ^ 3 - 9 * u * v ^ 2 := by
    rw [ht]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, R] at hrealQ
    dsimp [C, I] at himagQ
    push_cast at hrealQ himagQ
    linear_combination 8 * hrealQ - 4 * himagQ
  have himaguv : -(12 * s + 1500) = 3 * u ^ 2 * v - 3 * v ^ 3 := by
    rw [hs]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, I] at himagQ
    push_cast at himagQ
    linear_combination 4 * himagQ
  have hrel : u ^ 2 * v + 4 * u ^ 2 - v ^ 3 + 12 * v ^ 2 + 500 = 0 := by
    rw [hsuv] at himaguv
    linear_combination (-1 / 3 : ℚ) * himaguv
  have hv4 : v + 4 ≠ 0 := by
    intro hv
    have hv' : v = -4 := by linarith
    rw [hv'] at hrel
    norm_num at hrel
    linarith
  let x : ℚ := -84 / (v + 4)
  let y : ℚ := u * x / 3
  have hx0 : x ≠ 0 := by
    unfold x
    exact div_ne_zero (by norm_num) hv4
  refine ⟨x, y, hx0, ?_, ?_, ?_⟩
  · exact n35_inverse_short_identity hv4 hrel
  · exact n35_inverse_x_identity hv4 hsuv hrel
  · exact n35_inverse_y_identity hv4 htuv hrel
end

end MazurProof.RationalPointsX135
