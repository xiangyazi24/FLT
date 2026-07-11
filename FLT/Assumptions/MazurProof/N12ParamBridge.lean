import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-!
# Bridge from primitive Eisenstein triples to the normalized branch statement

This file keeps the hard arithmetic input explicit: a primitive positive
Eisenstein-triple parametrization with the unit exception.  The local work here
is only the Lean plumbing from that residual to the branch interface used by
the quartic descent assembly.
-/

namespace MazurProof.RationalPointsN12

private lemma int_pos_eq_one_of_mul_eq_one {x y : ℤ}
    (hx : 0 < x) (hxy : x * y = 1) :
    x = 1 := by
  have hypos : 0 < y := by
    by_contra hy_not
    have hy_nonpos : y ≤ 0 := le_of_not_gt hy_not
    have hprod_nonpos : x * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) hy_nonpos
    nlinarith [hxy, hprod_nonpos]
  have hxle : x ≤ 1 := by
    by_contra hx_not
    have hx_ge_two : (2 : ℤ) ≤ x := by omega
    have hy_ge_one : (1 : ℤ) ≤ y := by omega
    have hprod_ge_two : (2 : ℤ) ≤ x * y := by
      calc
        (2 : ℤ) = 2 * 1 := by ring
        _ ≤ x * y := by
          exact mul_le_mul hx_ge_two hy_ge_one (by norm_num) (by omega)
    nlinarith [hxy, hprod_ge_two]
  omega

private lemma int_pos_sq_eq_one {x : ℤ} (hx : 0 < x) (hsq : x ^ 2 = 1) :
    x = 1 := by
  apply int_pos_eq_one_of_mul_eq_one hx
  simpa [pow_two] using hsq

private lemma sq_pos_of_pos_int {x : ℤ} (hx : 0 < x) :
    0 < x ^ 2 := by
  exact sq_pos_of_ne_zero (ne_of_gt hx)

private lemma normalizedEisensteinBad_second_pos' {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    0 < N :=
  lt_trans h.1 h.2.1

private lemma normalizedEisensteinBad_not_triple_unit {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S)
    (hunit : A ^ 2 = 1 ∧ N ^ 2 = 1 ∧ S = 1) :
    False := by
  have hA1 : A = 1 := int_pos_sq_eq_one h.1 hunit.1
  have hNpos : 0 < N := normalizedEisensteinBad_second_pos' h
  have hN1 : N = 1 := int_pos_sq_eq_one hNpos hunit.2.1
  have hlt : A < N := h.2.1
  rw [hA1, hN1] at hlt
  exact (lt_irrefl (1 : ℤ)) hlt

/-- Product identity for the `Y`-oriented half factors, bundled with the two
linear identities used later to recover `X`, `Y`, and `Z` from a square split. -/
theorem eisensteinTriple_halfFactor_identities {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) :
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y)) = 3 * Y ^ 2 ∧
      (2 * Z - (2 * X - Y)) + (2 * Z + (2 * X - Y)) = 4 * Z ∧
      (2 * Z + (2 * X - Y)) - (2 * Z - (2 * X - Y)) =
        2 * (2 * X - Y) := by
  refine ⟨eisensteinTriple_factor_identity h, ?_, ?_⟩ <;> ring

/-- The two `Y`-oriented half factors are positive for a positive primitive
triple.  This avoids later ad hoc sign arguments around the square split. -/
theorem eisensteinTriple_halfFactors_pos {X Y Z : ℤ}
    (hY : 0 < Y) (hZ : 0 < Z)
    (h : EisensteinTriple X Y Z) :
    0 < 2 * Z - (2 * X - Y) ∧
      0 < 2 * Z + (2 * X - Y) := by
  let U : ℤ := 2 * Z - (2 * X - Y)
  let V : ℤ := 2 * Z + (2 * X - Y)
  have hprod : U * V = 3 * Y ^ 2 := by
    dsimp [U, V]
    exact eisensteinTriple_factor_identity h
  have hprod_pos : 0 < U * V := by
    rw [hprod]
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hY)]
  have hsum_pos : 0 < U + V := by
    dsimp [U, V]
    nlinarith
  have hUpos : 0 < U := by
    by_contra hUnot
    have hUle : U ≤ 0 := le_of_not_gt hUnot
    have hUne : U ≠ 0 := by
      intro hU0
      rw [hU0] at hprod_pos
      norm_num at hprod_pos
    have hUlt : U < 0 := lt_of_le_of_ne hUle hUne
    have hVlt : V < 0 := by
      by_contra hVnot
      have hVge : 0 ≤ V := le_of_not_gt hVnot
      have hprod_nonpos : U * V ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hUlt) hVge
      nlinarith
    nlinarith
  have hVpos : 0 < V := by
    by_contra hVnot
    have hVle : V ≤ 0 := le_of_not_gt hVnot
    have hprod_nonpos : U * V ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hUpos) hVle
    nlinarith
  exact ⟨hUpos, hVpos⟩

theorem eisenstein_Y_lt_Z_add_X {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (h : EisensteinTriple X Y Z) :
    Y < Z + X := by
  have hsq : Z ^ 2 - (Y - X) ^ 2 = X * Y := by
    unfold EisensteinTriple at h
    nlinarith
  have hpos : 0 < Z ^ 2 - (Y - X) ^ 2 := by
    nlinarith [mul_pos hX hY]
  by_contra hnot
  have hle : Z + X ≤ Y := le_of_not_gt hnot
  have hZle : Z ≤ Y - X := by omega
  have hdiff_nonneg : 0 ≤ (Y - X) - Z := by linarith
  have hsum_nonneg : 0 ≤ (Y - X) + Z := by nlinarith
  have hprod_nonneg : 0 ≤ ((Y - X) - Z) * ((Y - X) + Z) :=
    mul_nonneg hdiff_nonneg hsum_nonneg
  have hsq_le : Z ^ 2 ≤ (Y - X) ^ 2 := by nlinarith
  nlinarith

noncomputable def eisensteinSlope (X Y Z : ℤ) : ℚ :=
  (Y : ℚ) / (Z + X : ℤ)

noncomputable def eisenstein_m (X Y Z : ℤ) : ℤ :=
  ((eisensteinSlope X Y Z).den : ℤ)

noncomputable def eisenstein_n (X Y Z : ℤ) : ℤ :=
  (eisensteinSlope X Y Z).num

theorem eisenstein_slope_pos_lt_one {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (h : EisensteinTriple X Y Z) :
    0 < eisensteinSlope X Y Z ∧ eisensteinSlope X Y Z < 1 := by
  have hden : 0 < Z + X := by nlinarith
  have hlt : Y < Z + X := eisenstein_Y_lt_Z_add_X hX hY hZ h
  constructor
  · unfold eisensteinSlope
    positivity
  · unfold eisensteinSlope
    have hdenQ : (0 : ℚ) < ((Z + X : ℤ) : ℚ) := by exact_mod_cast hden
    rw [div_lt_iff₀ hdenQ]
    norm_num
    exact_mod_cast hlt

theorem eisenstein_mn_pos_coprime {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (h : EisensteinTriple X Y Z) :
    0 < eisenstein_n X Y Z ∧
      eisenstein_n X Y Z < eisenstein_m X Y Z ∧
      IsCoprime (eisenstein_m X Y Z) (eisenstein_n X Y Z) := by
  let q := eisensteinSlope X Y Z
  have hq : 0 < q ∧ q < 1 := eisenstein_slope_pos_lt_one hX hY hZ h
  have hnpos : 0 < q.num := Rat.num_pos.mpr hq.1
  have hnltm : q.num < (q.den : ℤ) := Rat.num_lt_denom_iff.mpr hq.2
  have hcop_gcd : Int.gcd (q.den : ℤ) q.num = 1 := by
    rw [Int.gcd_comm]
    exact q.reduced
  refine ⟨?_, ?_, ?_⟩
  · change 0 < q.num
    exact hnpos
  · change q.num < (q.den : ℤ)
    exact hnltm
  · change IsCoprime (q.den : ℤ) q.num
    exact Int.isCoprime_iff_gcd_eq_one.mpr hcop_gcd

theorem eisenstein_slope_cross {X Y Z : ℤ}
    (hX : 0 < X) (hZ : 0 < Z) :
    eisenstein_m X Y Z * Y = eisenstein_n X Y Z * (Z + X) := by
  let q := eisensteinSlope X Y Z
  let m : ℤ := (q.den : ℤ)
  let n : ℤ := q.num
  have hm0 : (m : ℚ) ≠ 0 := by
    dsimp [m]
    norm_cast
    exact Rat.den_nz q
  have hden_pos : 0 < Z + X := by nlinarith
  have hden0Q : (((Z + X : ℤ) : ℚ) ≠ 0) := by
    exact_mod_cast (ne_of_gt hden_pos)
  have hq_num : q = (n : ℚ) / (m : ℚ) := by
    dsimp [m, n]
    exact (Rat.num_div_den q).symm
  have heq : (n : ℚ) / (m : ℚ) = (Y : ℚ) / ((Z + X : ℤ) : ℚ) := by
    rw [← hq_num]
    rfl
  have hcrossQ : (n : ℚ) * ((Z + X : ℤ) : ℚ) = (Y : ℚ) * (m : ℚ) := by
    field_simp [hm0, hden0Q] at heq
    simpa [mul_comm, mul_left_comm, mul_assoc] using heq
  have hcrossQ' : (m : ℚ) * (Y : ℚ) =
      (n : ℚ) * ((Z + X : ℤ) : ℚ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcrossQ.symm
  have hcast : ((m * Y : ℤ) : ℚ) = ((n * (Z + X) : ℤ) : ℚ) := by
    push_cast
    simpa using hcrossQ'
  have hint : m * Y = n * (Z + X) := by
    exact_mod_cast hcast
  simpa [eisenstein_m, eisenstein_n, q, m, n] using hint

abbrev eisensteinEA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2

abbrev eisensteinEB (m n : ℤ) : ℤ := 2 * m - n

/-- The exceptional divisor `3` occurs exactly when `3 ∣ m+n`. -/
theorem eisenstein_EB_three_dvd_iff {m n : ℤ} :
    (3 : ℤ) ∣ eisensteinEB m n ↔ (3 : ℤ) ∣ m + n := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨2 * t - (m - n), ?_⟩
    unfold eisensteinEB at ht
    nlinarith
  · rintro ⟨t, ht⟩
    refine ⟨2 * t - n, ?_⟩
    unfold eisensteinEB
    nlinarith

/-- If `3 ∣ m+n`, then the first slope factor is divisible by `3`. -/
theorem eisenstein_EA_three_dvd_of_sum {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ eisensteinEA m n := by
  rcases h3 with ⟨t, ht⟩
  refine ⟨(m - n) * t, ?_⟩
  calc
    eisensteinEA m n = (m - n) * (m + n) := by
      unfold eisensteinEA
      ring
    _ = (m - n) * (3 * t) := by rw [ht]
    _ = 3 * ((m - n) * t) := by ring

/-- If `3 ∣ m+n`, then the second slope factor is divisible by `3`. -/
theorem eisenstein_EB_three_dvd_of_sum {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ eisensteinEB m n :=
  (eisenstein_EB_three_dvd_iff).2 h3

/-- Main linear identity for the common-divisor argument. -/
theorem eisenstein_common_divisor_identity (m n : ℤ) :
    (2 * m + n) * eisensteinEB m n - eisensteinEA m n = 3 * m ^ 2 := by
  unfold eisensteinEA eisensteinEB
  ring

/-- Any divisor of `2*m-n` is coprime to `m`, provided `m` and `n` are. -/
theorem eisenstein_common_divisor_coprime_m {d m n : ℤ}
    (hmn : IsCoprime m n) (hdB : d ∣ eisensteinEB m n) :
    IsCoprime d m := by
  apply IsRelPrime.isCoprime
  intro c hcd hcm
  have hcB : c ∣ eisensteinEB m n := hcd.trans hdB
  have hc2m : c ∣ 2 * m := dvd_mul_of_dvd_right hcm 2
  have hcn : c ∣ n := by
    have htmp : c ∣ 2 * m - eisensteinEB m n := dvd_sub hc2m hcB
    convert htmp using 1
    unfold eisensteinEB
    ring
  exact hmn.isUnit_of_dvd' hcm hcn

/-- Every common divisor of `m²-n²` and `2*m-n` divides `3`. -/
theorem eisenstein_common_dvd_three {d m n : ℤ}
    (hmn : IsCoprime m n)
    (hdA : d ∣ eisensteinEA m n) (hdB : d ∣ eisensteinEB m n) :
    d ∣ (3 : ℤ) := by
  have hdm : IsCoprime d m :=
    eisenstein_common_divisor_coprime_m hmn hdB
  have hdCombo :
      d ∣ (2 * m + n) * eisensteinEB m n - eisensteinEA m n :=
    dvd_sub (dvd_mul_of_dvd_right hdB (2 * m + n)) hdA
  have hd3m2 : d ∣ 3 * m ^ 2 := by
    simpa [eisenstein_common_divisor_identity m n] using hdCombo
  have hd3m : d ∣ 3 * m := by
    have hd3m2' : d ∣ m * (3 * m) := by
      convert hd3m2 using 1
      ring
    exact hdm.dvd_of_dvd_mul_left hd3m2'
  have hd3m' : d ∣ m * 3 := by
    convert hd3m using 1
    ring
  exact hdm.dvd_of_dvd_mul_left hd3m'

/-- Algebraic scale equations from the reduced Eisenstein slope.

The nonzero scale hypothesis is necessary; without it the degenerate
`C=0, Y=0, Z=-X` cases satisfy the two linear equations but not the
parametrization equations. -/
theorem eisenstein_scale_equations_of_slope_of_ne_zero {X Y Z m n C : ℤ}
    (hC : C ≠ 0)
    (hE : EisensteinTriple X Y Z)
    (hY : Y = n * C)
    (hW : Z + X = m * C) :
    eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C ∧
      eisensteinEB m n * X = eisensteinEA m n * C ∧
      eisensteinEB m n * Y = (2 * m * n - n ^ 2) * C := by
  have hE0 : Z ^ 2 = X ^ 2 - X * Y + Y ^ 2 := by
    unfold EisensteinTriple at hE
    exact hE
  have hXeq : X = m * C - Z := by
    nlinarith [hW]
  have hE1 :
      Z ^ 2 = (m * C - Z) ^ 2 - (m * C - Z) * (n * C) + (n * C) ^ 2 := by
    simpa [hXeq, hY] using hE0
  have h1zero :
      C * (eisensteinEB m n * Z - (m ^ 2 - m * n + n ^ 2) * C) = 0 := by
    unfold eisensteinEB
    nlinarith [hE1]
  have h1diff :
      eisensteinEB m n * Z - (m ^ 2 - m * n + n ^ 2) * C = 0 := by
    exact (mul_eq_zero.mp h1zero).resolve_left hC
  have h1 : eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C :=
    sub_eq_zero.mp h1diff
  refine ⟨h1, ?_, ?_⟩
  · calc
      eisensteinEB m n * X =
          eisensteinEB m n * (Z + X) - eisensteinEB m n * Z := by ring
      _ = eisensteinEB m n * (m * C) - eisensteinEB m n * Z := by rw [hW]
      _ = eisensteinEB m n * (m * C) -
          (m ^ 2 - m * n + n ^ 2) * C := by rw [h1]
      _ = eisensteinEA m n * C := by
        unfold eisensteinEA eisensteinEB
        ring
  · calc
      eisensteinEB m n * Y = eisensteinEB m n * (n * C) := by rw [hY]
      _ = (2 * m * n - n ^ 2) * C := by
        unfold eisensteinEB
        ring

/-- Positive-scale wrapper for the slope equations. -/
theorem eisenstein_scale_equations_of_slope_of_pos {X Y Z m n C : ℤ}
    (hCpos : 0 < C)
    (hE : EisensteinTriple X Y Z)
    (hY : Y = n * C)
    (hW : Z + X = m * C) :
    eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C ∧
      eisensteinEB m n * X = eisensteinEA m n * C ∧
      eisensteinEB m n * Y = (2 * m * n - n ^ 2) * C :=
  eisenstein_scale_equations_of_slope_of_ne_zero
    (ne_of_gt hCpos) hE hY hW

/-- A coprime equality `a*C=b*X` extracts the common integer scale. -/
theorem coprime_mul_eq_mul_scale {a b C X : ℤ}
    (hab : IsCoprime a b) (ha : 0 < a) (hXpos : 0 < X)
    (h : a * C = b * X) :
    ∃ k : ℤ, 0 < k ∧ X = k * a ∧ C = k * b := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hadvd : a ∣ b * X := by
    exact ⟨C, h.symm⟩
  have ha_dvd_X : a ∣ X := hab.dvd_of_dvd_mul_left hadvd
  rcases ha_dvd_X with ⟨k, hk⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · have hmulpos : 0 < a * k := by
      simpa [hk] using hXpos
    nlinarith
  · calc
      X = a * k := hk
      _ = k * a := by ring
  · have hCeq_mul : a * C = a * (k * b) := by
      calc
        a * C = b * X := h
        _ = b * (a * k) := by rw [hk]
        _ = a * (k * b) := by ring
    exact mul_left_cancel₀ ha_ne hCeq_mul

/-- Integer divisors of `3` are either units or multiples of `3`. -/
theorem int_isUnit_or_three_dvd_of_dvd_three {d : ℤ}
    (hd : d ∣ (3 : ℤ)) : IsUnit d ∨ (3 : ℤ) ∣ d := by
  have hdNat : d.natAbs ∣ (3 : ℕ) := by
    rcases hd with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have h := congrArg Int.natAbs hk
    simpa [Int.natAbs_mul] using h
  have hcase : d.natAbs = 1 ∨ d.natAbs = 3 :=
    Nat.prime_three.eq_one_or_self_of_dvd d.natAbs hdNat
  rcases hcase with hd1 | hd3
  · left
    exact Int.isUnit_iff_natAbs_eq.mpr hd1
  · right
    rw [← Int.dvd_natAbs, hd3]
    norm_num

/-- Raw sector: the two slope factors are coprime. -/
theorem eisenstein_factor_coprime_raw {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    IsCoprime (eisensteinEA m n) (eisensteinEB m n) := by
  apply IsRelPrime.isCoprime
  intro d hdA hdB
  have hd3 : d ∣ (3 : ℤ) :=
    eisenstein_common_dvd_three hmn hdA hdB
  rcases int_isUnit_or_three_dvd_of_dvd_three hd3 with hdUnit | hthree_d
  · exact hdUnit
  · have hthree_B : (3 : ℤ) ∣ eisensteinEB m n := hthree_d.trans hdB
    have hthree_sum : (3 : ℤ) ∣ m + n :=
      (eisenstein_EB_three_dvd_iff (m := m) (n := n)).mp hthree_B
    exact False.elim (h3 hthree_sum)

/-- Divided sector: quotient witnesses after removing the forced common `3`
are coprime.  This statement deliberately avoids integer `/`. -/
theorem eisenstein_factor_coprime_divided_witness {m n EA' EB' : ℤ}
    (hmn : IsCoprime m n)
    (hEA : eisensteinEA m n = 3 * EA')
    (hEB : eisensteinEB m n = 3 * EB') :
    IsCoprime EA' EB' := by
  apply IsRelPrime.isCoprime
  intro d hdA hdB
  have h3dA : 3 * d ∣ eisensteinEA m n := by
    rcases hdA with ⟨a, ha⟩
    rw [hEA, ha]
    exact ⟨a, by ring⟩
  have h3dB : 3 * d ∣ eisensteinEB m n := by
    rcases hdB with ⟨b, hb⟩
    rw [hEB, hb]
    exact ⟨b, by ring⟩
  have h3d_dvd_three : 3 * d ∣ (3 : ℤ) :=
    eisenstein_common_dvd_three hmn h3dA h3dB
  rcases h3d_dvd_three with ⟨q, hq⟩
  apply isUnit_of_dvd_one
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
  calc
    (3 : ℤ) * 1 = 3 := by ring
    _ = (3 * d) * q := hq
    _ = 3 * (d * q) := by ring

/-- Divided sector: canonical quotient witnesses from `3 ∣ m+n`. -/
theorem eisenstein_divided_factor_witnesses {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : (3 : ℤ) ∣ m + n) :
    ∃ EA' EB' : ℤ,
      eisensteinEA m n = 3 * EA' ∧
      eisensteinEB m n = 3 * EB' ∧
      IsCoprime EA' EB' := by
  rcases eisenstein_EA_three_dvd_of_sum h3 with ⟨EA', hEA⟩
  rcases eisenstein_EB_three_dvd_of_sum h3 with ⟨EB', hEB⟩
  exact ⟨EA', EB', hEA, hEB,
    eisenstein_factor_coprime_divided_witness hmn hEA hEB⟩

/-- A positive integer unit is `1`. -/
theorem positive_unit_eq_one {k : ℤ} (hk : 0 < k) (hu : IsUnit k) :
    k = 1 := by
  rcases Int.isUnit_eq_one_or hu with h | h
  · exact h
  · rw [h] at hk
    norm_num at hk

private theorem isUnit_of_common_scale {X Y A B k : ℤ}
    (hXY : IsCoprime X Y)
    (hX : X = A * k)
    (hY : Y = B * k) :
    IsUnit k := by
  have hkX : k ∣ X := by
    refine ⟨A, ?_⟩
    rw [hX]
    ring
  have hkY : k ∣ Y := by
    refine ⟨B, ?_⟩
    rw [hY]
    ring
  exact hXY.isUnit_of_dvd' hkX hkY

/-- Raw sector scale kill: primitive `(X,Y)` forces the scale to be exactly
`2*m-n`. -/
theorem eisenstein_scale_kill_raw {X Y Z m n C : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hYpos : 0 < Y)
    (hEBpos : 0 < eisensteinEB m n)
    (hEAEB : IsCoprime (eisensteinEA m n) (eisensteinEB m n))
    (hZeq : eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C)
    (hXeq : eisensteinEB m n * X = eisensteinEA m n * C)
    (hYC : Y = n * C) :
    C = eisensteinEB m n ∧ X = eisensteinEA m n ∧
      Y = 2 * m * n - n ^ 2 ∧ Z = m ^ 2 - m * n + n ^ 2 := by
  have hEBne : eisensteinEB m n ≠ 0 := ne_of_gt hEBpos
  have hEB_dvd_EA_C : eisensteinEB m n ∣ eisensteinEA m n * C := by
    exact ⟨X, hXeq.symm⟩
  have hEB_dvd_C : eisensteinEB m n ∣ C :=
    hEAEB.symm.dvd_of_dvd_mul_left hEB_dvd_EA_C
  rcases hEB_dvd_C with ⟨k, hkC⟩
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    nlinarith
  have hkpos : 0 < k := by
    have hprod : 0 < eisensteinEB m n * k := by
      simpa [hkC] using hCpos
    nlinarith
  have hXk : X = eisensteinEA m n * k := by
    apply mul_left_cancel₀ hEBne
    calc
      eisensteinEB m n * X = eisensteinEA m n * C := hXeq
      _ = eisensteinEA m n * (eisensteinEB m n * k) := by rw [hkC]
      _ = eisensteinEB m n * (eisensteinEA m n * k) := by ring
  have hYk : Y = (2 * m * n - n ^ 2) * k := by
    calc
      Y = n * C := hYC
      _ = n * (eisensteinEB m n * k) := by rw [hkC]
      _ = (2 * m * n - n ^ 2) * k := by
        unfold eisensteinEB
        ring
  have hkUnit : IsUnit k :=
    isUnit_of_common_scale hXY hXk hYk
  have hk1 : k = 1 := positive_unit_eq_one hkpos hkUnit
  have hCfinal : C = eisensteinEB m n := by
    simpa [hk1] using hkC
  have hXfinal : X = eisensteinEA m n := by
    simpa [hk1] using hXk
  have hYfinal : Y = 2 * m * n - n ^ 2 := by
    simpa [hk1] using hYk
  have hZfinal : Z = m ^ 2 - m * n + n ^ 2 := by
    apply mul_left_cancel₀ hEBne
    calc
      eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C := hZeq
      _ = (m ^ 2 - m * n + n ^ 2) * eisensteinEB m n := by rw [hCfinal]
      _ = eisensteinEB m n * (m ^ 2 - m * n + n ^ 2) := by ring
  exact ⟨hCfinal, hXfinal, hYfinal, hZfinal⟩

/-- Divided sector scale kill, stated with explicit quotient witnesses rather
than integer division. -/
theorem eisenstein_scale_kill_divided {X Y Z m n C EA' EB' : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hYpos : 0 < Y)
    (hEBpos : 0 < eisensteinEB m n)
    (hEA : eisensteinEA m n = 3 * EA')
    (hEB : eisensteinEB m n = 3 * EB')
    (hEAEB : IsCoprime EA' EB')
    (hZeq : eisensteinEB m n * Z = (m ^ 2 - m * n + n ^ 2) * C)
    (hXeq : eisensteinEB m n * X = eisensteinEA m n * C)
    (hYeq : eisensteinEB m n * Y = (2 * m * n - n ^ 2) * C)
    (hYC : Y = n * C) :
    C = EB' ∧ 3 * X = eisensteinEA m n ∧
      3 * Y = 2 * m * n - n ^ 2 ∧
      3 * Z = m ^ 2 - m * n + n ^ 2 := by
  have hEB'pos : 0 < EB' := by
    nlinarith [hEBpos, hEB]
  have hEB'ne : EB' ≠ 0 := ne_of_gt hEB'pos
  have hXeq' : EB' * X = EA' * C := by
    apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by norm_num)
    calc
      (3 : ℤ) * (EB' * X) = (3 * EB') * X := by ring
      _ = eisensteinEB m n * X := by rw [← hEB]
      _ = eisensteinEA m n * C := hXeq
      _ = (3 * EA') * C := by rw [hEA]
      _ = 3 * (EA' * C) := by ring
  have hEB'_dvd_EA_C : EB' ∣ EA' * C := by
    exact ⟨X, hXeq'.symm⟩
  have hEB'_dvd_C : EB' ∣ C :=
    hEAEB.symm.dvd_of_dvd_mul_left hEB'_dvd_EA_C
  rcases hEB'_dvd_C with ⟨k, hkC⟩
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    nlinarith
  have hkpos : 0 < k := by
    have hprod : 0 < EB' * k := by
      simpa [hkC] using hCpos
    nlinarith
  have hXk : X = EA' * k := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * X = EA' * C := hXeq'
      _ = EA' * (EB' * k) := by rw [hkC]
      _ = EB' * (EA' * k) := by ring
  have hYk : Y = (n * EB') * k := by
    calc
      Y = n * C := hYC
      _ = n * (EB' * k) := by rw [hkC]
      _ = (n * EB') * k := by ring
  have hkUnit : IsUnit k :=
    isUnit_of_common_scale hXY hXk hYk
  have hk1 : k = 1 := positive_unit_eq_one hkpos hkUnit
  have hCfinal : C = EB' := by
    simpa [hk1] using hkC
  have hXfinal : X = EA' := by
    simpa [hk1] using hXk
  have h3X : 3 * X = eisensteinEA m n := by
    calc
      3 * X = 3 * EA' := by rw [hXfinal]
      _ = eisensteinEA m n := hEA.symm
  have h3Y : 3 * Y = 2 * m * n - n ^ 2 := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * (3 * Y) = (3 * EB') * Y := by ring
      _ = eisensteinEB m n * Y := by rw [← hEB]
      _ = (2 * m * n - n ^ 2) * C := hYeq
      _ = (2 * m * n - n ^ 2) * EB' := by rw [hCfinal]
      _ = EB' * (2 * m * n - n ^ 2) := by ring
  have h3Z : 3 * Z = m ^ 2 - m * n + n ^ 2 := by
    apply mul_left_cancel₀ hEB'ne
    calc
      EB' * (3 * Z) = (3 * EB') * Z := by ring
      _ = eisensteinEB m n * Z := by rw [← hEB]
      _ = (m ^ 2 - m * n + n ^ 2) * C := hZeq
      _ = (m ^ 2 - m * n + n ^ 2) * EB' := by rw [hCfinal]
      _ = EB' * (m ^ 2 - m * n + n ^ 2) := by ring
  exact ⟨hCfinal, h3X, h3Y, h3Z⟩

/-- Positivity of the first slope factor from `0<n<m`. -/
theorem eisenstein_EA_pos {m n : ℤ} (hn0 : 0 < n) (hnm : n < m) :
    0 < eisensteinEA m n := by
  have hmn : 0 < m - n := by omega
  have hmpn : 0 < m + n := by omega
  calc
    0 < (m - n) * (m + n) := by positivity
    _ = eisensteinEA m n := by
      unfold eisensteinEA
      ring

/-- Positivity of the second slope factor from `0<n<m`. -/
theorem eisenstein_EB_pos {m n : ℤ} (hn0 : 0 < n) (hnm : n < m) :
    0 < eisensteinEB m n := by
  unfold eisensteinEB
  omega

/-- Raw half-factor algebra.  The hard primitive-triple work is to produce
`s`, `m`, and `n` with these identities; once they are available, the branch
equations are only polynomial arithmetic. -/
theorem eisensteinSqBranch_of_rawHalfFactors
    {A N S m n s : ℤ}
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (hs : s = 2 * m - n)
    (hN : N ^ 2 = n * s)
    (hU : 2 * S - (2 * A ^ 2 - N ^ 2) = 3 * n ^ 2)
    (hV : 2 * S + (2 * A ^ 2 - N ^ 2) = s ^ 2) :
    EisensteinSqBranch A N S m n := by
  have hAeq : A ^ 2 = (m - n) * (m + n) := by
    nlinarith
  have hNeq : N ^ 2 = n * (2 * m - n) := by
    nlinarith
  have hSeq : S = m ^ 2 - m * n + n ^ 2 := by
    nlinarith
  exact ⟨hnpos, hnltm, hcop, hAeq, hNeq, hSeq⟩

/-- Divided-by-`3` half-factor algebra.  The divisibility `3 ∣ m+n` follows
formally from `2*m-n = 3*s`. -/
theorem dividedSquareBranch_of_dividedHalfFactors
    {A N S m n s : ℤ}
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (hs : 2 * m - n = 3 * s)
    (hN : N ^ 2 = n * s)
    (hU : 2 * S - (2 * A ^ 2 - N ^ 2) = n ^ 2)
    (hV : 2 * S + (2 * A ^ 2 - N ^ 2) = 3 * s ^ 2) :
    DividedSquareBranch A N S m n := by
  have h3 : (3 : ℤ) ∣ m + n := by
    refine ⟨m - s, ?_⟩
    nlinarith
  have hAeq : 3 * A ^ 2 = (m - n) * (m + n) := by
    nlinarith
  have hNeq : 3 * N ^ 2 = n * (2 * m - n) := by
    nlinarith
  have hSeq : 3 * S = m ^ 2 - m * n + n ^ 2 := by
    nlinarith
  exact ⟨hnpos, hnltm, hcop, h3, hAeq, hNeq, hSeq⟩

/-- Stronger primitive triple frontier: the unit triple is also parametrized,
by the divided-by-`3` sector with `(m,n)=(2,1)`. -/
def EisensteinTriplePrimitiveFullParamStatement : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ, EisensteinFullParam X Y Z m n

/-- Constructor for the raw sector of `EisensteinFullParam`, first
orientation. -/
theorem eisensteinFullParam_of_raw
    {X Y Z m n : ℤ}
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (hnot3 : ¬ (3 : ℤ) ∣ m + n)
    (hZ : Z = m ^ 2 - m * n + n ^ 2)
    (hX : X = m ^ 2 - n ^ 2)
    (hY : Y = 2 * m * n - n ^ 2) :
    EisensteinFullParam X Y Z m n := by
  refine ⟨hnpos, hnltm, hcop, Or.inl ⟨hnot3, ?_⟩⟩
  refine ⟨hZ, Or.inl ⟨?_, hY⟩⟩
  calc
    X = m ^ 2 - n ^ 2 := hX
    _ = m ^ 2 - n ^ 2 := rfl

/-- Constructor for the divided-by-`3` sector of `EisensteinFullParam`, first
orientation. -/
theorem eisensteinFullParam_of_divided
    {X Y Z m n : ℤ}
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (h3 : (3 : ℤ) ∣ m + n)
    (hZ : 3 * Z = m ^ 2 - m * n + n ^ 2)
    (hX : 3 * X = m ^ 2 - n ^ 2)
    (hY : 3 * Y = 2 * m * n - n ^ 2) :
    EisensteinFullParam X Y Z m n := by
  exact ⟨hnpos, hnltm, hcop, Or.inr ⟨h3, hZ, Or.inl ⟨hX, hY⟩⟩⟩

/-- The unit triple is represented in the divided-by-`3` sector. -/
theorem eisensteinFullParam_unit :
    EisensteinFullParam 1 1 1 2 1 := by
  refine eisensteinFullParam_of_divided
    (X := 1) (Y := 1) (Z := 1) (m := 2) (n := 1)
    (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · use 0, 1
    norm_num
  · exact ⟨1, by norm_num⟩
  · norm_num
  · norm_num
  · norm_num

/-- Raw sector constructor from a positive scaled slope. -/
theorem eisensteinFullParam_raw_of_scaled
    {X Y Z m n C : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (hnot3 : ¬ (3 : ℤ) ∣ m + n)
    (hYpos : 0 < Y)
    (hE : EisensteinTriple X Y Z)
    (hYC : Y = n * C)
    (hW : Z + X = m * C) :
    EisensteinFullParam X Y Z m n := by
  have hEBpos : 0 < eisensteinEB m n :=
    eisenstein_EB_pos hnpos hnltm
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    nlinarith
  have hscale :=
    eisenstein_scale_equations_of_slope_of_pos hCpos hE hYC hW
  have hEAEB : IsCoprime (eisensteinEA m n) (eisensteinEB m n) :=
    eisenstein_factor_coprime_raw hcop hnot3
  have hkill :=
    eisenstein_scale_kill_raw hXY hnpos hYpos hEBpos hEAEB
      hscale.1 hscale.2.1 hYC
  exact eisensteinFullParam_of_raw hnpos hnltm hcop hnot3
    (by simpa using hkill.2.2.2)
    (by simpa [eisensteinEA] using hkill.2.1)
    (by simpa using hkill.2.2.1)

/-- Divided sector constructor from a positive scaled slope. -/
theorem eisensteinFullParam_divided_of_scaled
    {X Y Z m n C : ℤ}
    (hXY : IsCoprime X Y)
    (hnpos : 0 < n) (hnltm : n < m) (hcop : IsCoprime m n)
    (h3 : (3 : ℤ) ∣ m + n)
    (hYpos : 0 < Y)
    (hE : EisensteinTriple X Y Z)
    (hYC : Y = n * C)
    (hW : Z + X = m * C) :
    EisensteinFullParam X Y Z m n := by
  have hEBpos : 0 < eisensteinEB m n :=
    eisenstein_EB_pos hnpos hnltm
  have hCpos : 0 < C := by
    have hprod : 0 < n * C := by
      simpa [hYC] using hYpos
    nlinarith
  have hscale :=
    eisenstein_scale_equations_of_slope_of_pos hCpos hE hYC hW
  rcases eisenstein_divided_factor_witnesses hcop h3 with
    ⟨EA', EB', hEA, hEB, hEAEB⟩
  have hkill :=
    eisenstein_scale_kill_divided hXY hnpos hYpos hEBpos hEA hEB hEAEB
      hscale.1 hscale.2.1 hscale.2.2 hYC
  exact eisensteinFullParam_of_divided hnpos hnltm hcop h3
    (by simpa using hkill.2.2.2)
    (by simpa [eisensteinEA] using hkill.2.1)
    (by simpa using hkill.2.2.1)

/-- Checked primitive positive Eisenstein-triple parametrization, using the
reduced rational slope `Y/(Z+X)`. -/
theorem eisensteinTriplePrimitiveFullParamStatement_checked :
    EisensteinTriplePrimitiveFullParamStatement := by
  intro X Y Z hX hY hZ hcopXY htri
  let m := eisenstein_m X Y Z
  let n := eisenstein_n X Y Z
  have hmn : 0 < n ∧ n < m ∧ IsCoprime m n := by
    simpa [m, n] using eisenstein_mn_pos_coprime hX hY hZ htri
  have hcross : m * Y = n * (Z + X) := by
    simpa [m, n] using eisenstein_slope_cross (X := X) (Y := Y) (Z := Z) hX hZ
  have hscale : ∃ C : ℤ, 0 < C ∧ Y = C * n ∧ Z + X = C * m :=
    coprime_mul_eq_mul_scale (a := n) (b := m) (C := Z + X) (X := Y)
      hmn.2.2.symm hmn.1 hY hcross.symm
  rcases hscale with ⟨C, hCpos, hYscaled, hWscaled⟩
  have hYC : Y = n * C := by
    calc
      Y = C * n := hYscaled
      _ = n * C := by ring
  have hW : Z + X = m * C := by
    calc
      Z + X = C * m := hWscaled
      _ = m * C := by ring
  refine ⟨m, n, ?_⟩
  by_cases h3 : (3 : ℤ) ∣ m + n
  · exact eisensteinFullParam_divided_of_scaled
      hcopXY hmn.1 hmn.2.1 hmn.2.2 h3 hY htri hYC hW
  · exact eisensteinFullParam_raw_of_scaled
      hcopXY hmn.1 hmn.2.1 hmn.2.2 h3 hY htri hYC hW

/-- The stronger full-parametrization frontier implies the current
unit-or-param frontier. -/
theorem tripleParamOrUnit_of_fullParam
    (hFull : EisensteinTriplePrimitiveFullParamStatement) :
    EisensteinTriplePrimitiveParamOrUnit := by
  intro X Y Z hX hY hZ hcop htri
  exact Or.inr (hFull hX hY hZ hcop htri)

/-- The hard primitive-triple parametrization residual implies the branch
parametrization statement required by the normalized descent assembly. -/
theorem normalizedBadParamStatement_of_tripleParamOrUnit
    (hTriple : EisensteinTriplePrimitiveParamOrUnit) :
    NormalizedBadParamStatement := by
  intro A N S hnorm
  have hNpos : 0 < N := normalizedEisensteinBad_second_pos' hnorm
  have hA2pos : 0 < A ^ 2 := sq_pos_of_pos_int hnorm.1
  have hN2pos : 0 < N ^ 2 := sq_pos_of_pos_int hNpos
  have hcopSq : IsCoprime (A ^ 2) (N ^ 2) :=
    hnorm.2.2.2.1.pow
  have htri : EisensteinTriple (A ^ 2) (N ^ 2) S :=
    eisensteinTriple_of_quartic hnorm.2.2.2.2
  rcases hTriple hA2pos hN2pos hnorm.2.2.1 hcopSq htri with hunit | hparam
  · exact False.elim (normalizedEisensteinBad_not_triple_unit hnorm hunit)
  · rcases hparam with ⟨m, n, hfull⟩
    refine ⟨m, n, ?_⟩
    rcases hfull with ⟨hnpos, hnltm, hcopmn, hsector⟩
    rcases hsector with hraw | hdiv
    · rcases hraw with ⟨_hnot3, hparamRaw⟩
      rcases hparamRaw with ⟨hS, hcases⟩
      rcases hcases with hAN | hNA
      · rcases hAN with ⟨hA, hN⟩
        refine Or.inl ⟨hnpos, hnltm, hcopmn, ?_, ?_, hS⟩
        · calc
            A ^ 2 = m ^ 2 - n ^ 2 := hA
            _ = (m - n) * (m + n) := by ring
        · calc
            N ^ 2 = 2 * m * n - n ^ 2 := hN
            _ = n * (2 * m - n) := by ring
      · rcases hNA with ⟨hN, hA⟩
        refine Or.inr (Or.inl ⟨hnpos, hnltm, hcopmn, ?_, ?_, hS⟩)
        · calc
            N ^ 2 = m ^ 2 - n ^ 2 := hN
            _ = (m - n) * (m + n) := by ring
        · calc
            A ^ 2 = 2 * m * n - n ^ 2 := hA
            _ = n * (2 * m - n) := by ring
    · rcases hdiv with ⟨h3, hS, hcases⟩
      rcases hcases with hAN | hNA
      · rcases hAN with ⟨hA, hN⟩
        refine Or.inr (Or.inr (Or.inl
          ⟨hnpos, hnltm, hcopmn, h3, ?_, ?_, hS⟩))
        · calc
            3 * A ^ 2 = m ^ 2 - n ^ 2 := hA
            _ = (m - n) * (m + n) := by ring
        · calc
            3 * N ^ 2 = 2 * m * n - n ^ 2 := hN
            _ = n * (2 * m - n) := by ring
      · rcases hNA with ⟨hN, hA⟩
        refine Or.inr (Or.inr (Or.inr
          ⟨hnpos, hnltm, hcopmn, h3, ?_, ?_, hS⟩))
        · calc
            3 * N ^ 2 = m ^ 2 - n ^ 2 := hN
            _ = (m - n) * (m + n) := by ring
        · calc
            3 * A ^ 2 = 2 * m * n - n ^ 2 := hA
            _ = n * (2 * m - n) := by ring

/-- Stronger full parametrization also implies the normalized branch
parametrization statement. -/
theorem normalizedBadParamStatement_of_tripleFullParam
    (hFull : EisensteinTriplePrimitiveFullParamStatement) :
    NormalizedBadParamStatement :=
  normalizedBadParamStatement_of_tripleParamOrUnit
    (tripleParamOrUnit_of_fullParam hFull)

end MazurProof.RationalPointsN12
