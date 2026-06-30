```lean
lemma int_even_sq_modEq_zero_mod_four {x : ℤ} (hx : Even x) :
    x ^ 2 ≡ 0 [ZMOD 4] := by
  rcases hx with ⟨k, rfl⟩
  rw [Int.modEq_zero_iff_dvd]
  use k ^ 2
  ring

lemma int_odd_sq_modEq_one_mod_four {x : ℤ} (hx : Odd x) :
    x ^ 2 ≡ 1 [ZMOD 4] := by
  rcases hx with ⟨k, rfl⟩
  rw [Int.modEq_iff_dvd]
  use -(k * (k + 1))
  ring

lemma int_odd_sq_modEq_one_mod_eight {x : ℤ} (hx : Odd x) :
    x ^ 2 ≡ 1 [ZMOD 8] := by
  rcases hx with ⟨k, rfl⟩
  rw [Int.modEq_iff_dvd]
  have h2 : (2 : ℤ) ∣ k * (k + 1) := Int.two_dvd_mul_add_one k
  rcases h2 with ⟨t, ht⟩
  use -t
  calc
    1 - (2 * k + 1) ^ 2 = -4 * (k * (k + 1)) := by ring
    _ = 8 * (-t) := by
      rw [ht]
      ring

lemma int_delta_modEq_zero_mod_four_of_same_parity
    {x y Δ : ℤ}
    (hxy : y ^ 2 - x ^ 2 = Δ)
    (hpar : (Even x ∧ Even y) ∨ (Odd x ∧ Odd y)) :
    Δ ≡ 0 [ZMOD 4] := by
  rw [← hxy]
  rcases hpar with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simpa using
      (int_even_sq_modEq_zero_mod_four hy).sub
        (int_even_sq_modEq_zero_mod_four hx)
  · simpa using
      (int_odd_sq_modEq_one_mod_four hy).sub
        (int_odd_sq_modEq_one_mod_four hx)

lemma int_delta_modEq_one_mod_four_of_even_odd
    {x y Δ : ℤ}
    (hxy : y ^ 2 - x ^ 2 = Δ)
    (hx : Even x) (hy : Odd y) :
    Δ ≡ 1 [ZMOD 4] := by
  rw [← hxy]
  simpa using
    (int_odd_sq_modEq_one_mod_four hy).sub
      (int_even_sq_modEq_zero_mod_four hx)

lemma int_delta_modEq_neg_one_mod_four_of_odd_even
    {x y Δ : ℤ}
    (hxy : y ^ 2 - x ^ 2 = Δ)
    (hx : Odd x) (hy : Even y) :
    Δ ≡ -1 [ZMOD 4] := by
  rw [← hxy]
  simpa using
    (int_even_sq_modEq_zero_mod_four hy).sub
      (int_odd_sq_modEq_one_mod_four hx)

lemma int_square_ap_triple_all_even_or_all_odd
    {x y z Δ : ℤ}
    (hxy : y ^ 2 - x ^ 2 = Δ)
    (hyz : z ^ 2 - y ^ 2 = Δ) :
    (Even x ∧ Even y ∧ Even z) ∨ (Odd x ∧ Odd y ∧ Odd z) := by
  rcases Int.even_or_odd x with hxE | hxO
  · rcases Int.even_or_odd y with hyE | hyO
    · rcases Int.even_or_odd z with hzE | hzO
      · exact Or.inl ⟨hxE, hyE, hzE⟩
      · exfalso
        have h0 : Δ ≡ 0 [ZMOD 4] :=
          int_delta_modEq_zero_mod_four_of_same_parity hxy (Or.inl ⟨hxE, hyE⟩)
        have h1 : Δ ≡ 1 [ZMOD 4] :=
          int_delta_modEq_one_mod_four_of_even_odd hyz hyE hzO
        have hc : (0 : ℤ) ≡ 1 [ZMOD 4] := h0.symm.trans h1
        norm_num [Int.ModEq] at hc
    · rcases Int.even_or_odd z with hzE | hzO
      · exfalso
        have h1 : Δ ≡ 1 [ZMOD 4] :=
          int_delta_modEq_one_mod_four_of_even_odd hxy hxE hyO
        have hn1 : Δ ≡ -1 [ZMOD 4] :=
          int_delta_modEq_neg_one_mod_four_of_odd_even hyz hyO hzE
        have hc : (1 : ℤ) ≡ -1 [ZMOD 4] := h1.symm.trans hn1
        norm_num [Int.ModEq] at hc
      · exfalso
        have h1 : Δ ≡ 1 [ZMOD 4] :=
          int_delta_modEq_one_mod_four_of_even_odd hxy hxE hyO
        have h0 : Δ ≡ 0 [ZMOD 4] :=
          int_delta_modEq_zero_mod_four_of_same_parity hyz (Or.inr ⟨hyO, hzO⟩)
        have hc : (1 : ℤ) ≡ 0 [ZMOD 4] := h1.symm.trans h0
        norm_num [Int.ModEq] at hc
  · rcases Int.even_or_odd y with hyE | hyO
    · rcases Int.even_or_odd z with hzE | hzO
      · exfalso
        have hn1 : Δ ≡ -1 [ZMOD 4] :=
          int_delta_modEq_neg_one_mod_four_of_odd_even hxy hxO hyE
        have h0 : Δ ≡ 0 [ZMOD 4] :=
          int_delta_modEq_zero_mod_four_of_same_parity hyz (Or.inl ⟨hyE, hzE⟩)
        have hc : (-1 : ℤ) ≡ 0 [ZMOD 4] := hn1.symm.trans h0
        norm_num [Int.ModEq] at hc
      · exfalso
        have hn1 : Δ ≡ -1 [ZMOD 4] :=
          int_delta_modEq_neg_one_mod_four_of_odd_even hxy hxO hyE
        have h1 : Δ ≡ 1 [ZMOD 4] :=
          int_delta_modEq_one_mod_four_of_even_odd hyz hyE hzO
        have hc : (-1 : ℤ) ≡ 1 [ZMOD 4] := hn1.symm.trans h1
        norm_num [Int.ModEq] at hc
    · rcases Int.even_or_odd z with hzE | hzO
      · exfalso
        have h0 : Δ ≡ 0 [ZMOD 4] :=
          int_delta_modEq_zero_mod_four_of_same_parity hxy (Or.inr ⟨hxO, hyO⟩)
        have hn1 : Δ ≡ -1 [ZMOD 4] :=
          int_delta_modEq_neg_one_mod_four_of_odd_even hyz hyO hzE
        have hc : (0 : ℤ) ≡ -1 [ZMOD 4] := h0.symm.trans hn1
        norm_num [Int.ModEq] at hc
      · exact Or.inr ⟨hxO, hyO, hzO⟩

lemma two_dvd_natAbs_of_even_int {x : ℤ} (hx : Even x) :
    2 ∣ x.natAbs := by
  have hxNat : Even x.natAbs := (Int.natAbs_even (n := x)).2 hx
  exact even_iff_two_dvd.mp hxNat

lemma false_of_all_even_roots_of_rootGCD4_eq_one
    {p q r s : ℤ}
    (hroot : rootGCD4 p q r s = 1)
    (hp : Even p) (hq : Even q) (hr : Even r) (hs : Even s) :
    False := by
  have hp2 : 2 ∣ p.natAbs := two_dvd_natAbs_of_even_int hp
  have hq2 : 2 ∣ q.natAbs := two_dvd_natAbs_of_even_int hq
  have hr2 : 2 ∣ r.natAbs := two_dvd_natAbs_of_even_int hr
  have hs2 : 2 ∣ s.natAbs := two_dvd_natAbs_of_even_int hs
  have h2root : 2 ∣ rootGCD4 p q r s := by
    unfold rootGCD4
    exact Nat.dvd_gcd hp2 (Nat.dvd_gcd hq2 (Nat.dvd_gcd hr2 hs2))
  have h21 : 2 ∣ (1 : ℕ) := by
    simpa [hroot] using h2root
  norm_num at h21

theorem weakPrimitiveAPParity_short : WeakPrimitiveAPParity := by
  intro p q r s Δ hpq hqr hrs hroot
  have hpqr := int_square_ap_triple_all_even_or_all_odd hpq hqr
  have hqrs := int_square_ap_triple_all_even_or_all_odd hqr hrs
  rcases hpqr with hpqrE | hpqrO
  · rcases hqrs with hqrsE | hqrsO
    · exact False.elim <|
        false_of_all_even_roots_of_rootGCD4_eq_one
          hroot hpqrE.1 hpqrE.2.1 hpqrE.2.2 hqrsE.2.2
    · exact False.elim <| (Int.not_even_iff_odd.mpr hqrsO.1) hpqrE.2.1
  · rcases hqrs with hqrsE | hqrsO
    · exact False.elim <| (Int.not_even_iff_odd.mpr hpqrO.2.1) hqrsE.1
    · have hp1 : p % 2 = 1 := Int.odd_iff.mp hpqrO.1
      have hq1 : q % 2 = 1 := Int.odd_iff.mp hpqrO.2.1
      have hr1 : r % 2 = 1 := Int.odd_iff.mp hpqrO.2.2
      have hs1 : s % 2 = 1 := Int.odd_iff.mp hqrsO.2.2
      have h8Δ : (8 : ℤ) ∣ Δ := by
        have hq8 : q ^ 2 ≡ 1 [ZMOD 8] :=
          int_odd_sq_modEq_one_mod_eight hpqrO.2.1
        have hp8 : p ^ 2 ≡ 1 [ZMOD 8] :=
          int_odd_sq_modEq_one_mod_eight hpqrO.1
        have hdiff : q ^ 2 - p ^ 2 ≡ 0 [ZMOD 8] := by
          simpa using hq8.sub hp8
        have hΔ : Δ ≡ 0 [ZMOD 8] := by
          rw [← hpq]
          exact hdiff
        exact Int.modEq_zero_iff_dvd.mp hΔ
      exact ⟨hp1, hq1, hr1, hs1, h8Δ⟩
```
