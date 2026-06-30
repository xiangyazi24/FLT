theorem q2528_int_odd_mod_two_not_dvd {a : ℤ} (ha : a % 2 = 1) :
    ¬ (2 : ℤ) ∣ a := by
  intro h2a
  have hmod0 : a % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2a
  rw [hmod0] at ha
  norm_num at ha

/-- If a natural number divides all four roots, it divides `rootGCD4`. -/
theorem q2528_nat_dvd_rootGCD4_of_dvd_all
    {ℓ : ℕ} {p q r s : ℤ}
    (hℓp : ℓ ∣ p.natAbs)
    (hℓq : ℓ ∣ q.natAbs)
    (hℓr : ℓ ∣ r.natAbs)
    (hℓs : ℓ ∣ s.natAbs) :
    ℓ ∣ rootGCD4 p q r s := by
  unfold rootGCD4
  exact Nat.dvd_gcd hℓp (Nat.dvd_gcd hℓq (Nat.dvd_gcd hℓr hℓs))

/-- Prime-divisor contradiction against `rootGCD4 = 1`. -/
theorem q2528_false_of_prime_dvd_all_roots
    {ℓ : ℕ} {p q r s : ℤ}
    (hroot : rootGCD4 p q r s = 1)
    (hℓprime : Nat.Prime ℓ)
    (hℓp : (ℓ : ℤ) ∣ p)
    (hℓq : (ℓ : ℤ) ∣ q)
    (hℓr : (ℓ : ℤ) ∣ r)
    (hℓs : (ℓ : ℤ) ∣ s) :
    False := by
  have hℓroot : ℓ ∣ rootGCD4 p q r s :=
    q2528_nat_dvd_rootGCD4_of_dvd_all
      (Int.natCast_dvd.mp hℓp)
      (Int.natCast_dvd.mp hℓq)
      (Int.natCast_dvd.mp hℓr)
      (Int.natCast_dvd.mp hℓs)
  have hℓone : ℓ ∣ (1 : ℕ) := by
    simpa [hroot] using hℓroot
  exact hℓprime.ne_one (Nat.dvd_one.mp hℓone)

/-- If an odd natural prime divides `2 * Δ` over `ℤ`, then it divides `Δ`. -/
theorem q2528_natPrime_dvd_of_dvd_two_mul_int_of_ne_two
    {ℓ : ℕ} {Δ : ℤ}
    (hℓprime : Nat.Prime ℓ)
    (hℓne2 : ℓ ≠ 2)
    (hℓtwoΔ : (ℓ : ℤ) ∣ 2 * Δ) :
    (ℓ : ℤ) ∣ Δ := by
  have hcases : (ℓ : ℤ) ∣ (2 : ℤ) ∨ (ℓ : ℤ) ∣ Δ :=
    Int.Prime.dvd_mul' hℓprime hℓtwoΔ
  rcases hcases with hℓtwo | hℓΔ
  · exfalso
    have hℓdvd2Nat : ℓ ∣ (2 : ℕ) := by
      simpa using (Int.natCast_dvd.mp hℓtwo)
    have hℓle2 : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓdvd2Nat
    exact hℓne2 (le_antisymm hℓle2 hℓprime.two_le)
  · exact hℓΔ

/-- Generic gcd closure by excluding every common natural prime divisor. -/
theorem q2528_int_gcd_eq_one_of_no_common_nat_prime
    {a b : ℤ}
    (hno : ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ a.natAbs → ℓ ∣ b.natAbs → False) :
    Int.gcd a b = 1 := by
  by_contra hbad
  have hbadNat : ¬ Nat.Coprime a.natAbs b.natAbs := by
    intro hcop
    apply hbad
    simpa [Int.gcd_def, Nat.Coprime] using hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hbadNat with
    ⟨ℓ, hℓprime, hℓa, hℓb⟩
  exact hno ℓ hℓprime hℓa hℓb

/-- Middle adjacent pair: `gcd q r = 1`. -/
theorem int_gcd_qr_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd q r = 1 := by
  apply q2528_int_gcd_eq_one_of_no_common_nat_prime
  intro ℓ hℓprime hℓqNat hℓrNat
  have hℓq : (ℓ : ℤ) ∣ q := Int.natCast_dvd.mpr hℓqNat
  have hℓr : (ℓ : ℤ) ∣ r := Int.natCast_dvd.mpr hℓrNat
  have hℓΔ : (ℓ : ℤ) ∣ Δ := by
    have hdiv : (ℓ : ℤ) ∣ r ^ 2 - q ^ 2 :=
      dvd_sub (pow_dvd_pow_of_dvd hℓr 2) (pow_dvd_pow_of_dvd hℓq 2)
    rwa [hqr] at hdiv
  have hℓp : (ℓ : ℤ) ∣ p := by
    apply Int.Prime.dvd_pow' (n := p) (k := 2) hℓprime
    have hp2 : p ^ 2 = q ^ 2 - Δ := by nlinarith
    rw [hp2]
    exact dvd_sub (pow_dvd_pow_of_dvd hℓq 2) hℓΔ
  have hℓs : (ℓ : ℤ) ∣ s := by
    apply Int.Prime.dvd_pow' (n := s) (k := 2) hℓprime
    have hs2 : s ^ 2 = r ^ 2 + Δ := by nlinarith
    rw [hs2]
    exact dvd_add (pow_dvd_pow_of_dvd hℓr 2) hℓΔ
  exact q2528_false_of_prime_dvd_all_roots hroot hℓprime hℓp hℓq hℓr hℓs

/-- Middle distance-two pair: `gcd q s = 1`. -/
theorem int_gcd_qs_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (hq_odd : q % 2 = 1) :
    Int.gcd q s = 1 := by
  apply q2528_int_gcd_eq_one_of_no_common_nat_prime
  intro ℓ hℓprime hℓqNat hℓsNat
  have hℓq : (ℓ : ℤ) ∣ q := Int.natCast_dvd.mpr hℓqNat
  have hℓs : (ℓ : ℤ) ∣ s := Int.natCast_dvd.mpr hℓsNat
  by_cases hℓeq2 : ℓ = 2
  · subst ℓ
    exact q2528_int_odd_mod_two_not_dvd hq_odd (by simpa using hℓq)
  have hℓ_s2_sub_q2 : (ℓ : ℤ) ∣ s ^ 2 - q ^ 2 :=
    dvd_sub (pow_dvd_pow_of_dvd hℓs 2) (pow_dvd_pow_of_dvd hℓq 2)
  have hsq_twoΔ : s ^ 2 - q ^ 2 = 2 * Δ := by nlinarith
  have hℓ_twoΔ : (ℓ : ℤ) ∣ 2 * Δ := by
    rwa [hsq_twoΔ] at hℓ_s2_sub_q2
  have hℓΔ : (ℓ : ℤ) ∣ Δ :=
    q2528_natPrime_dvd_of_dvd_two_mul_int_of_ne_two hℓprime hℓeq2 hℓ_twoΔ
  have hℓp : (ℓ : ℤ) ∣ p := by
    apply Int.Prime.dvd_pow' (n := p) (k := 2) hℓprime
    have hp2 : p ^ 2 = q ^ 2 - Δ := by nlinarith
    rw [hp2]
    exact dvd_sub (pow_dvd_pow_of_dvd hℓq 2) hℓΔ
  have hℓr : (ℓ : ℤ) ∣ r := by
    apply Int.Prime.dvd_pow' (n := r) (k := 2) hℓprime
    have hr2 : r ^ 2 = q ^ 2 + Δ := by nlinarith
    rw [hr2]
    exact dvd_add (pow_dvd_pow_of_dvd hℓq 2) hℓΔ
  exact q2528_false_of_prime_dvd_all_roots hroot hℓprime hℓp hℓq hℓr hℓs

/-- Last adjacent pair: `gcd r s = 1`. -/
theorem int_gcd_rs_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd r s = 1 := by
  apply q2528_int_gcd_eq_one_of_no_common_nat_prime
  intro ℓ hℓprime hℓrNat hℓsNat
  have hℓr : (ℓ : ℤ) ∣ r := Int.natCast_dvd.mpr hℓrNat
  have hℓs : (ℓ : ℤ) ∣ s := Int.natCast_dvd.mpr hℓsNat
  have hℓΔ : (ℓ : ℤ) ∣ Δ := by
    have hdiv : (ℓ : ℤ) ∣ s ^ 2 - r ^ 2 :=
      dvd_sub (pow_dvd_pow_of_dvd hℓs 2) (pow_dvd_pow_of_dvd hℓr 2)
    rwa [hrs] at hdiv
  have hℓq : (ℓ : ℤ) ∣ q := by
    apply Int.Prime.dvd_pow' (n := q) (k := 2) hℓprime
    have hq2 : q ^ 2 = r ^ 2 - Δ := by nlinarith
    rw [hq2]
    exact dvd_sub (pow_dvd_pow_of_dvd hℓr 2) hℓΔ
  have hℓp : (ℓ : ℤ) ∣ p := by
    apply Int.Prime.dvd_pow' (n := p) (k := 2) hℓprime
    have hp2 : p ^ 2 = q ^ 2 - Δ := by nlinarith
    rw [hp2]
    exact dvd_sub (pow_dvd_pow_of_dvd hℓq 2) hℓΔ
  exact q2528_false_of_prime_dvd_all_roots hroot hℓprime hℓp hℓq hℓr hℓs

theorem weakPrimitiveAPPairwise : WeakPrimitiveAPPairwise := by
  intro p q r s Δ hpq hqr hrs hroot hp_odd hq_odd hr_odd hs_odd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact int_gcd_pq_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot hp_odd
  · exact int_gcd_pr_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot hp_odd
  · exact int_gcd_ps_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot
  · exact int_gcd_qr_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot
  · exact int_gcd_qs_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot hq_odd
  · exact int_gcd_rs_eq_one_of_weak_ap
      (p := p) (q := q) (r := r) (s := s) (Δ := Δ)
      hpq hqr hrs hroot
