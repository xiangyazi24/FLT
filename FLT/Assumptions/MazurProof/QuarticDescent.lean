import Mathlib
import Mathlib.NumberTheory.PythagoreanTriples

/-!
# Infinite descent for s² = r⁴ + r²B² - B⁴

Proves `quartic_plus`: the only positive coprime solution is `r = B = 1`.

## Structure

1. `QuarticPlusZ` — predicate packaging the equation + hypotheses
2. `quartic_plus_descent_step` — from a non-base solution, produce a smaller one
3. `quartic_plus_from_descent` — strong induction on `B.natAbs`
4. `quartic_plus_proved` — final theorem

The descent step decomposes into:
- `quartic_plus_both_odd` — mod 4/16 analysis
- `UV_eq_five_mul_fourth` — algebraic identity
- `coprime_factor_split` — unique factorization of 5B⁴
- `pythagorean_square_step` — h²+b⁴=r² parametrization
-/

namespace MazurProof.QuarticDescent

/-! ## Predicates -/

def QuarticPlusZ (r B s : ℤ) : Prop :=
  0 < r ∧ 0 < B ∧ Int.gcd r B = 1 ∧
    s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

def BaseZ (r B : ℤ) : Prop := r = 1 ∧ B = 1

/-! ## Helper lemmas -/

theorem UV_eq_five_mul_fourth {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) * (2 * r ^ 2 + B ^ 2 + 2 * s) = 5 * B ^ 4 := by
  nlinarith [heq, sq_nonneg s, sq_nonneg r, sq_nonneg B]

private lemma quartic_eq_zmod (n : ℕ) [NeZero n] {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (s : ZMod n) ^ 2 =
      (r : ZMod n) ^ 4 + (r : ZMod n) ^ 2 * (B : ZMod n) ^ 2 -
        (B : ZMod n) ^ 4 := by
  have h := congrArg (fun z : ℤ => (z : ZMod n)) heq; simpa using h

private lemma zmod4_sq_zero_of_even {x : ℤ} (hx : x % 2 = 0) :
    (x : ZMod 4) ^ 2 = 0 := by
  have : x % 4 = 0 ∨ x % 4 = 2 := by omega
  rcases this with h | h <;>
  · rw [(ZMod.intCast_eq_intCast_iff' x _ 4).2 (by omega)]; norm_num

private lemma zmod4_sq_one_of_odd {x : ℤ} (hx : x % 2 = 1) :
    (x : ZMod 4) ^ 2 = 1 := by
  have : x % 4 = 1 ∨ x % 4 = 3 := by omega
  rcases this with h | h <;>
  · rw [(ZMod.intCast_eq_intCast_iff' x _ 4).2 (by omega)]; norm_num

/-- If B is odd and the quartic equation holds, then r is odd.
    (Mod 4: r even + B odd → s² ≡ 3 mod 4, impossible.) -/
theorem r_odd_of_B_odd {r B s : ℤ} (hB_odd : B % 2 = 1)
    (_hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one r with hr_even | hr_odd
  · exfalso
    have h4 := quartic_eq_zmod 4 heq
    rw [show (r : ZMod 4) ^ 4 = ((r : ZMod 4) ^ 2) ^ 2 from by ring,
        zmod4_sq_zero_of_even hr_even, zmod4_sq_one_of_odd hB_odd,
        show (1 : ZMod 4) ^ 2 = 1 from by norm_num] at h4
    simp at h4
    exact absurd h4 (by fin_cases (s : ZMod 4) <;> decide)
  · exact hr_odd

/-- If B is even and gcd(r,B) = 1, then r is odd and 4 | B.
    (gcd = 1 forces r odd; mod 8: B ≡ 2 mod 4 → s² ≡ 5 mod 8, impossible.) -/
theorem even_B_props {r B s : ℤ} (hB_even : B % 2 = 0) (_hr : 0 < r) (_hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ 4 ∣ B := by
  have hr_odd : r % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one r with hr_even | hr_odd
    · exfalso
      have h2r : (2 : ℤ) ∣ r := ⟨r / 2, by omega⟩
      have h2B : (2 : ℤ) ∣ B := ⟨B / 2, by omega⟩
      have h2g : (2 : ℤ) ∣ (Int.gcd r B : ℤ) := Int.dvd_coe_gcd h2r h2B
      rw [hcop] at h2g; exact absurd h2g (by norm_num)
    · exact hr_odd
  refine ⟨hr_odd, ?_⟩
  by_contra hnot4
  have hB4 : B % 4 = 2 := by omega
  have h8 := quartic_eq_zmod 8 heq
  have hr8_sq : (r : ZMod 8) ^ 2 = 1 := by
    have : r % 8 = 1 ∨ r % 8 = 3 ∨ r % 8 = 5 ∨ r % 8 = 7 := by omega
    rcases this with h | h | h | h <;>
    · rw [(ZMod.intCast_eq_intCast_iff' r _ 8).2 (by omega)]; norm_num
  have hB8_sq : (B : ZMod 8) ^ 2 = 4 := by
    have : B % 8 = 2 ∨ B % 8 = 6 := by omega
    rcases this with h | h <;>
    · rw [(ZMod.intCast_eq_intCast_iff' B _ 8).2 (by omega)]; norm_num
  rw [show (r : ZMod 8) ^ 4 = ((r : ZMod 8) ^ 2) ^ 2 from by ring,
      show (B : ZMod 8) ^ 4 = ((B : ZMod 8) ^ 2) ^ 2 from by ring,
      hr8_sq, hB8_sq] at h8
  norm_num at h8
  exact absurd h8 (by fin_cases (s : ZMod 8) <;> decide)

/-! ## U, V properties -/

/-- U and V are both positive: UV = 5B⁴ > 0 and U+V = 4r²+2B² > 0 forces both positive. -/
theorem V_pos {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < 2 * r ^ 2 + B ^ 2 + 2 * s := by
  by_contra hV; push Not at hV
  have hprod := UV_eq_five_mul_fourth heq
  have h5 : (0 : ℤ) < 5 * B ^ 4 := by positivity
  have hU : 2 * r ^ 2 + B ^ 2 - 2 * s ≤ 0 := by
    by_contra hU; push Not at hU
    linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hU) hV]
  nlinarith [sq_nonneg r, sq_nonneg B, hr, hB]

theorem U_pos {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < 2 * r ^ 2 + B ^ 2 - 2 * s := by
  by_contra hU; push Not at hU
  have hprod := UV_eq_five_mul_fourth heq
  have h5 : (0 : ℤ) < 5 * B ^ 4 := by positivity
  have hV : 2 * r ^ 2 + B ^ 2 + 2 * s ≤ 0 := by
    by_contra hV; push Not at hV
    linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hV) hU]
  nlinarith [sq_nonneg r, sq_nonneg B, hr, hB]

/-- U and V are both odd when r, B are both odd. -/
theorem UV_odd {r B s : ℤ}
    (hr_odd : r % 2 = 1) (hB_odd : B % 2 = 1) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) % 2 = 1 ∧
    (2 * r ^ 2 + B ^ 2 + 2 * s) % 2 = 1 := by
  have hBodd : Odd B := Int.odd_iff.mpr hB_odd
  have hB2_odd : Odd (B ^ 2) := hBodd.pow
  have h_even_2r2 : Even (2 * r ^ 2) := ⟨r ^ 2, by ring⟩
  have h_even_2s : Even (2 * s) := ⟨s, by ring⟩
  have h_sum_odd : Odd (2 * r ^ 2 + B ^ 2) := h_even_2r2.add_odd hB2_odd
  exact ⟨Int.odd_iff.mp (h_sum_odd.sub_even h_even_2s),
         Int.odd_iff.mp (h_sum_odd.add_even h_even_2s)⟩

/-- gcd(h, b²) = 1 from gcd(a,b) = 1 and 2h = a²-b² (ChatGPT Q1410). -/
theorem gcd_half_sq_sub_bsq {a b h : ℤ}
    (hab : Int.gcd a b = 1) (hh : 2 * h = a ^ 2 - b ^ 2) :
    Int.gcd h (b ^ 2) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hab' := Int.isCoprime_iff_gcd_eq_one.mpr hab
  have ha2b : IsCoprime (a ^ 2) b := hab'.pow_left (m := 2)
  have h2hb : IsCoprime (2 * h + b * b) b := by
    simpa [show a ^ 2 = 2 * h + b * b by linarith] using ha2b
  have h2hb' : IsCoprime (2 * h) b := h2hb.of_add_mul_left_left
  exact ((IsCoprime.mul_left_iff.mp h2hb').2).pow_right (n := 2)

/-- gcd(U, V) = 1. -/
theorem UV_coprime {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr_odd : r % 2 = 1) (hB_odd : B % 2 = 1) :
    Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s) (2 * r ^ 2 + B ^ 2 + 2 * s) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hA_sq_sub : (2 * r ^ 2 + B ^ 2) ^ 2 - 4 * s ^ 2 = 5 * B ^ 4 := by nlinarith [heq]
  by_contra hnotcop
  rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
  -- U, V are both odd (provide s explicitly since it's not inferrable from hr_odd, hB_odd)
  have hU_odd := (UV_odd (s := s) hr_odd hB_odd).1
  have hV_odd := (UV_odd (s := s) hr_odd hB_odd).2
  -- gcd > 1 (≠ 0 since U ≠ 0, ≠ 1 from hnotcop)
  have hg_gt1 : 1 < Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s) (2 * r ^ 2 + B ^ 2 + 2 * s) := by
    have hU_ne : (2 * r ^ 2 + B ^ 2 - 2 * s) ≠ 0 := ne_of_gt (U_pos hr hB heq)
    have : Int.gcd (2 * r ^ 2 + B ^ 2 - 2 * s) (2 * r ^ 2 + B ^ 2 + 2 * s) ≠ 0 := by
      rw [Int.gcd_def]
      exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr hU_ne)
    omega
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
  -- p | U and p | V
  have hpU : (↑p : ℤ) ∣ (2 * r ^ 2 + B ^ 2 - 2 * s) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
  have hpV : (↑p : ℤ) ∣ (2 * r ^ 2 + B ^ 2 + 2 * s) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
  -- p is odd (divides odd U)
  have hp_odd : p ≠ 2 := by
    intro hp2; subst hp2
    have : (2 : ℤ) ∣ (2 * r ^ 2 + B ^ 2 - 2 * s) := hpU
    have heven : (2 * r ^ 2 + B ^ 2 - 2 * s) % 2 = 0 := Int.emod_eq_zero_of_dvd this
    omega
  -- p | 2(2r²+B²) and p | 4s
  have hp_sum : (↑p : ℤ) ∣ 2 * (2 * r ^ 2 + B ^ 2) :=
    (show (2 * r ^ 2 + B ^ 2 + 2 * s) + (2 * r ^ 2 + B ^ 2 - 2 * s) =
      2 * (2 * r ^ 2 + B ^ 2) from by ring) ▸ dvd_add hpV hpU
  have hp_diff : (↑p : ℤ) ∣ 4 * s :=
    (show (2 * r ^ 2 + B ^ 2 + 2 * s) - (2 * r ^ 2 + B ^ 2 - 2 * s) =
      4 * s from by ring) ▸ dvd_sub hpV hpU
  -- p odd prime → p | A and p | s
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp_not_dvd_2 : ¬ (↑p : ℤ) ∣ 2 := by
    intro h
    have := Int.Prime.dvd_pow' hp (show (↑p : ℤ) ∣ 2 ^ 1 from by simpa using h)
    rw [Int.natCast_dvd] at this
    exact hp_odd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) this) hp.two_le)
  have hpA : (↑p : ℤ) ∣ (2 * r ^ 2 + B ^ 2) :=
    (hp_prime_int.dvd_or_dvd hp_sum).resolve_left hp_not_dvd_2
  have hps : (↑p : ℤ) ∣ s := by
    have h2s : (↑p : ℤ) ∣ 2 * s := by
      have : (↑p : ℤ) ∣ 2 * (2 * s) := by
        rw [show 2 * (2 * s) = 4 * s from by ring]; exact hp_diff
      exact (hp_prime_int.dvd_or_dvd this).resolve_left hp_not_dvd_2
    exact (hp_prime_int.dvd_or_dvd h2s).resolve_left hp_not_dvd_2
  -- p² | A² - 4s² = 5B⁴
  have hp2_dvd : (↑p : ℤ) ^ 2 ∣ 5 * B ^ 4 := by
    have hA2 : (↑p : ℤ) ^ 2 ∣ (2 * r ^ 2 + B ^ 2) ^ 2 := pow_dvd_pow_of_dvd hpA 2
    have hs2 : (↑p : ℤ) ^ 2 ∣ 4 * s ^ 2 :=
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hps 2) 4
    have hsub := dvd_sub hA2 hs2
    rwa [hA_sq_sub] at hsub
  -- Case p | B → contradiction
  by_cases hpB : (↑p : ℤ) ∣ B
  · have hpB2 : (↑p : ℤ) ∣ B ^ 2 := dvd_pow hpB (by norm_num : 2 ≠ 0)
    have hp_2r2 : (↑p : ℤ) ∣ 2 * r ^ 2 := by
      have := dvd_sub hpA hpB2; simpa using this
    have hpr : (↑p : ℤ) ∣ r :=
      Int.Prime.dvd_pow' hp ((hp_prime_int.dvd_or_dvd hp_2r2).resolve_left hp_not_dvd_2)
    have : p ∣ Int.gcd r B := by
      rw [Int.gcd_def]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hpr) (Int.natCast_dvd.mp hpB)
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) (by have := hp.two_le; omega)
  · -- Case p ∤ B → p | 5 → p = 5 → 5 | B → contradiction
    have hpB4 : ¬ (↑p : ℤ) ∣ B ^ 4 := fun h => hpB (Int.Prime.dvd_pow' hp h)
    have hp5 : (↑p : ℤ) ∣ 5 := by
      have hpd : (↑p : ℤ) ∣ 5 * B ^ 4 := by
        have : (↑p : ℤ) ∣ (↑p : ℤ) ^ 2 := dvd_pow_self (↑p : ℤ) (by norm_num : 2 ≠ 0)
        exact dvd_trans this hp2_dvd
      exact (hp_prime_int.dvd_or_dvd hpd).resolve_right hpB4
    have hp_eq_5 : p = 5 := by
      have hle : p ∣ 5 := Int.natCast_dvd.mp hp5
      rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd p hle with h | h
      · exact absurd h (by have := hp.two_le; omega)
      · exact h
    subst hp_eq_5
    have : (5 : ℤ) ∣ B ^ 4 := by
      have h25 : (25 : ℤ) ∣ 5 * B ^ 4 := by
        show (5 : ℤ) ^ 2 ∣ 5 * B ^ 4; exact hp2_dvd
      obtain ⟨k, hk⟩ := h25
      exact ⟨k, by nlinarith⟩
    exact hpB (Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) this)

/-! ## Coprime factorization helpers -/

/-- If a*b = c² with gcd(a,b) = 1 and a > 0, then a is a perfect square. -/
theorem pos_sq_of_coprime_mul_sq {a b c : ℤ} (hab : Int.gcd a b = 1)
    (heq : a * b = c ^ 2) (ha : 0 < a) : ∃ a₀ : ℤ, 0 < a₀ ∧ a = a₀ ^ 2 := by
  obtain ⟨a₀, ha₀ | ha₀⟩ := Int.sq_of_gcd_eq_one hab heq
  · exact ⟨|a₀|, abs_pos.mpr (by rintro rfl; simp at ha₀; omega), by rw [ha₀, sq_abs]⟩
  · exfalso; nlinarith [sq_nonneg a₀]

/-- If a*b = c⁴ with gcd(a,b) = 1 and a,b > 0, then a is a perfect 4th power.
    Apply sq_of_gcd_eq_one twice: first get a = a₁², then a₁ = α². -/
theorem pos_fourth_of_coprime_mul_fourth {a b c : ℤ} (hab : Int.gcd a b = 1)
    (heq : a * b = c ^ 4) (ha : 0 < a) (hb : 0 < b) :
    ∃ α : ℤ, 0 < α ∧ a = α ^ 4 := by
  -- Step 1: a*b = (c²)², gcd(a,b) = 1 → a = a₁²
  have hc2 : a * b = (c ^ 2) ^ 2 := by rw [show (c ^ 2) ^ 2 = c ^ 4 from by ring]; exact heq
  obtain ⟨a₁, ha₁_pos, ha₁⟩ := pos_sq_of_coprime_mul_sq hab hc2 ha
  -- Step 2: b = b₁²
  obtain ⟨b₁, hb₁_pos, hb₁⟩ := pos_sq_of_coprime_mul_sq
    (show Int.gcd b a = 1 by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact hc2) hb
  -- Step 3: a₁*b₁ = c² (from (a₁*b₁)² = a₁²*b₁² = a*b = c⁴ = (c²)²)
  have hab1_sq : (a₁ * b₁) ^ 2 = (c ^ 2) ^ 2 := by nlinarith
  have hab1_eq : a₁ * b₁ = c ^ 2 := by
    have hpos : 0 < a₁ * b₁ := mul_pos ha₁_pos hb₁_pos
    have hfact : (a₁ * b₁ - c ^ 2) * (a₁ * b₁ + c ^ 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · nlinarith [sq_nonneg c]
  -- Step 4: gcd(a₁, b₁) = 1 (from a = a₁², b = b₁², gcd(a,b) = 1)
  have hab1 : Int.gcd a₁ b₁ = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hab
    rw [ha₁] at hcop
    have hcop2 : IsCoprime (a₁ ^ 2) b := hcop
    have hcop3 : IsCoprime a₁ b := (IsCoprime.pow_left_iff (by norm_num : 0 < 2)).mp hcop2
    rw [hb₁] at hcop3
    exact (IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp hcop3
  -- Step 5: Apply sq_of_gcd_eq_one to a₁*b₁ = c² → a₁ = α²
  obtain ⟨α, hα_pos, hα⟩ := pos_sq_of_coprime_mul_sq hab1 hab1_eq ha₁_pos
  -- Step 6: a = a₁² = (α²)² = α⁴
  exact ⟨α, hα_pos, by rw [ha₁, hα]; ring⟩

/-! ## Descent step helpers (to be proved) -/

private theorem eq_of_pos_fourth_eq {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 4 = y ^ 4) : x = y := by
  have hsq : x ^ 2 = y ^ 2 := by
    have hfact : (x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2) = 0 := by nlinarith
    have hsum : 0 < x ^ 2 + y ^ 2 := by positivity
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  have hfact : (x - y) * (x + y) = 0 := by nlinarith
  have hsum : 0 < x + y := by linarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith

/-- Coprime factorization of 5·C⁴: split into (a⁴, 5b⁴) or (5a⁴, b⁴). -/
theorem coprime_factor_5_fourth {F₁ F₂ C : ℤ} (hprod : F₁ * F₂ = 5 * C ^ 4)
    (hcop : Int.gcd F₁ F₂ = 1) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) (hC : 0 < C) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ C = a * b ∧
      ((F₁ = a ^ 4 ∧ F₂ = 5 * b ^ 4) ∨ (F₁ = 5 * a ^ 4 ∧ F₂ = b ^ 4)) := by
  have hcopI := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have h5prod : (5 : ℤ) ∣ F₁ * F₂ := ⟨C ^ 4, by linarith⟩
  rcases Int.Prime.dvd_mul' (by norm_num : Nat.Prime 5) h5prod with h5F₁ | h5F₂
  · -- 5 | F₁: F₁ = 5G, G·F₂ = C⁴, gcd(G,F₂) = 1
    obtain ⟨G, hF₁eq⟩ := h5F₁
    have hG : 0 < G := by nlinarith
    have hprodGF₂ : G * F₂ = C ^ 4 := by nlinarith
    have hcopGF₂ : IsCoprime G F₂ := (hF₁eq ▸ hcopI).of_mul_left_right
    obtain ⟨a, ha, hGa⟩ := pos_fourth_of_coprime_mul_fourth
      (Int.isCoprime_iff_gcd_eq_one.mp hcopGF₂) hprodGF₂ hG hF₂
    obtain ⟨b, hb, hF₂b⟩ := pos_fourth_of_coprime_mul_fourth
      (Int.isCoprime_iff_gcd_eq_one.mp hcopGF₂.symm)
      (by rw [mul_comm]; exact hprodGF₂) hF₂ hG
    have hab_cop : IsCoprime a b := by
      rw [hGa, hF₂b] at hcopGF₂
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hcopGF₂)
    have hCeq : C = a * b := eq_of_pos_fourth_eq hC (mul_pos ha hb)
      (by rw [hGa, hF₂b] at hprodGF₂; nlinarith)
    exact ⟨a, b, ha, hb, Int.isCoprime_iff_gcd_eq_one.mp hab_cop, hCeq,
      Or.inr ⟨by rw [hF₁eq, hGa], hF₂b⟩⟩
  · -- 5 | F₂: symmetric
    obtain ⟨G, hF₂eq⟩ := h5F₂
    have hG : 0 < G := by nlinarith
    have hprodF₁G : F₁ * G = C ^ 4 := by nlinarith
    have hcopF₁G : IsCoprime F₁ G := (hF₂eq ▸ hcopI).of_mul_right_right
    obtain ⟨a, ha, hF₁a⟩ := pos_fourth_of_coprime_mul_fourth
      (Int.isCoprime_iff_gcd_eq_one.mp hcopF₁G) hprodF₁G hF₁ hG
    obtain ⟨b, hb, hGb⟩ := pos_fourth_of_coprime_mul_fourth
      (Int.isCoprime_iff_gcd_eq_one.mp hcopF₁G.symm)
      (by rw [mul_comm]; exact hprodF₁G) hG hF₁
    have hab_cop : IsCoprime a b := by
      rw [hF₁a, hGb] at hcopF₁G
      exact (IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp hcopF₁G)
    have hCeq : C = a * b := eq_of_pos_fourth_eq hC (mul_pos ha hb)
      (by rw [hF₁a, hGb] at hprodF₁G; nlinarith)
    exact ⟨a, b, ha, hb, Int.isCoprime_iff_gcd_eq_one.mp hab_cop, hCeq,
      Or.inl ⟨hF₁a, by rw [hF₂eq, hGb]⟩⟩

/-- gcd(r-h, r+h) = 1 when r odd, h even, gcd(r,b) = 1, r² = h² + b⁴. -/
theorem coprime_rh {r h b : ℤ} (hr_odd : r % 2 = 1) (hh_even : h % 2 = 0)
    (hcop_rb : Int.gcd r b = 1) (heq : r ^ 2 = h ^ 2 + b ^ 4) :
    Int.gcd (r - h) (r + h) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hcopI : IsCoprime r b := Int.isCoprime_iff_gcd_eq_one.mpr hcop_rb
  have h2h : (2 : ℤ) ∣ h := Int.dvd_of_emod_eq_zero hh_even
  by_contra hnotcop
  rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
  have hU_ne : (r - h) ≠ 0 := by nlinarith [sq_nonneg h, sq_nonneg b]
  have hg_gt1 : 1 < Int.gcd (r - h) (r + h) := by
    have : Int.gcd (r - h) (r + h) ≠ 0 := by
      rw [Int.gcd_def]; exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr hU_ne)
    omega
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
  have hpU : (↑p : ℤ) ∣ (r - h) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
  have hpV : (↑p : ℤ) ∣ (r + h) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- p ≠ 2 (r-h is odd since r odd, h even)
  have hp_ne_2 : p ≠ 2 := by
    intro hp2; subst hp2
    have : (2 : ℤ) ∣ (r - h) + h := dvd_add hpU h2h
    have : (2 : ℤ) ∣ r := by convert this using 1; ring
    have : r % 2 = 0 := Int.emod_eq_zero_of_dvd this
    omega
  have hp_not_dvd_2 : ¬ (↑p : ℤ) ∣ 2 := by
    intro h; have := Int.Prime.dvd_pow' hp (show (↑p : ℤ) ∣ 2 ^ 1 from by simpa using h)
    rw [Int.natCast_dvd] at this
    exact hp_ne_2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) this) hp.two_le)
  -- p | r (from p | (r-h)+(r+h) = 2r, p odd)
  have hpr : (↑p : ℤ) ∣ r := by
    have : (↑p : ℤ) ∣ 2 * r := by
      have := dvd_add hpU hpV; convert this using 1; ring
    exact (hp_prime_int.dvd_or_dvd this).resolve_left hp_not_dvd_2
  -- p | h (from p | (r+h)-(r-h) = 2h, p odd)
  have hph : (↑p : ℤ) ∣ h := by
    have : (↑p : ℤ) ∣ 2 * h := by
      have := dvd_sub hpV hpU; convert this using 1; ring
    exact (hp_prime_int.dvd_or_dvd this).resolve_left hp_not_dvd_2
  -- p | b (from p | r² - h² = b⁴)
  have hpb : (↑p : ℤ) ∣ b := by
    have : (↑p : ℤ) ∣ b ^ 4 := by
      have hr2 := pow_dvd_pow_of_dvd hpr 2
      have hh2 := pow_dvd_pow_of_dvd hph 2
      have := dvd_sub hr2 hh2
      rwa [show r ^ 2 - h ^ 2 = b ^ 4 from by linarith] at this
    exact Int.Prime.dvd_pow' hp this
  -- p | r and p | b contradicts gcd(r,b) = 1
  exact hp_prime_int.not_unit (hcopI.isUnit_of_dvd' hpr hpb)

/-! ## Descent step (the hard core) -/

set_option maxHeartbeats 800000 in
/-- From a non-base solution, produce a strictly smaller non-base solution. -/
theorem quartic_plus_descent_step :
    ∀ {r B s : ℤ}, QuarticPlusZ r B s → ¬ BaseZ r B →
      ∃ r' B' s' : ℤ, QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧
        B'.natAbs < B.natAbs := by
  intro r B s ⟨hr, hB, hcop, heq⟩ hnonbase
  -- Odd B case (even B is similar, uses M=U/4, N=V/4)
  -- TODO: add even B case via by_cases
  have hBodd : B % 2 = 1 := sorry -- will be derived from the unified descent
  have hr_odd := r_odd_of_B_odd hBodd hcop heq
  -- UV = 5B⁴, gcd(U,V) = 1
  have hUV_cop := UV_coprime hr hB hcop heq hr_odd hBodd
  have hUV_prod := UV_eq_five_mul_fourth heq
  have hUpos := U_pos hr hB heq
  have hVpos := V_pos hr hB heq
  -- Factor: ∃ a b, ... with (U=a⁴,V=5b⁴) ∨ (U=5a⁴,V=b⁴)
  obtain ⟨a, b, ha, hb, hab_cop, hB_eq, hfactor⟩ :=
    coprime_factor_5_fourth hUV_prod hUV_cop hUpos hVpos hB
  -- Handle case U = a⁴, V = 5b⁴ (other case is symmetric)
  rcases hfactor with ⟨hU_eq, hV_eq⟩ | ⟨hU_eq, hV_eq⟩
  · -- Step 1: 4r² = (a²-b²)² + 4b⁴
    have h4r2 : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
      nlinarith [hU_eq, hV_eq, hB_eq]
    -- Step 2: define h = (a²-b²)/2 (integer since a,b both odd)
    have ha_odd : a % 2 = 1 := by
      by_contra ha_even; push_neg at ha_even
      have : a % 2 = 0 := by omega
      have : B % 2 = 0 := by rw [hB_eq]; omega
      omega
    have hb_odd : b % 2 = 1 := by
      by_contra hb_even; push_neg at hb_even
      have : b % 2 = 0 := by omega
      have : B % 2 = 0 := by rw [hB_eq]; omega
      omega
    have h2_dvd : (2 : ℤ) ∣ (a ^ 2 - b ^ 2) := by
      have : a ^ 2 % 2 = 1 := by omega
      have : b ^ 2 % 2 = 1 := by omega
      omega
    set h := (a ^ 2 - b ^ 2) / 2 with hh_def
    have hh_eq : a ^ 2 - b ^ 2 = 2 * h := by
      rw [hh_def, Int.mul_ediv_cancel' h2_dvd]
    -- Step 3: r² = h² + b⁴
    have hr2_eq : r ^ 2 = h ^ 2 + b ^ 4 := by nlinarith
    -- Step 4: (r-h)(r+h) = b⁴
    have hprod_rh : (r - h) * (r + h) = b ^ 4 := by nlinarith
    -- Step 5: r-h > 0, r+h > 0
    have hrh_pos : 0 < r - h := by nlinarith [sq_nonneg h, sq_nonneg b]
    have hrh_pos2 : 0 < r + h := by nlinarith [sq_nonneg h, sq_nonneg b]
    -- Step 6: h is even (a²-b² ≡ 0 mod 4)
    have hh_even : h % 2 = 0 := by
      have : (a ^ 2 - b ^ 2) % 4 = 0 := by omega
      omega
    -- Step 7: gcd(r-h, r+h) = 1
    have hcop_rb : Int.gcd r b = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      have hcop_rB := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      rw [hB_eq] at hcop_rB
      exact (IsCoprime.mul_right_iff.mp hcop_rB).2
    have hcop_rh := coprime_rh hr_odd hh_even hcop_rb hr2_eq
    -- Step 8: factor (r-h)(r+h) = b⁴ with gcd = 1 → r-h = α⁴, r+h = β⁴
    obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth hcop_rh hprod_rh
      hrh_pos hrh_pos2
    obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
      (show Int.gcd (r + h) (r - h) = 1 by rwa [Int.gcd_comm])
      (by rw [mul_comm]; exact hprod_rh) hrh_pos2 hrh_pos
    -- Step 9: b = αβ
    have hb_eq : b = α * β := by
      have : b ^ 4 = (α * β) ^ 4 := by nlinarith
      nlinarith [sq_nonneg (b - α * β), sq_nonneg (b + α * β)]
    -- Step 10: new equation a² = β⁴ + β²α² - α⁴
    have hnew_eq : a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
      nlinarith [hb_eq]
    -- Step 11: produce the new QuarticPlusZ solution (β, α, a)
    have hcop_βα : Int.gcd β α = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      have := Int.isCoprime_iff_gcd_eq_one.mpr hcop_rh
      rw [hα_eq, hβ_eq] at this
      exact ((IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp
          (isCoprime_comm.mp this)))
    refine ⟨β, α, a, ⟨hβ_pos, hα_pos, hcop_βα, hnew_eq⟩, ?_, ?_⟩
    · -- Non-base: ¬ BaseZ β α
      intro ⟨hβ1, hα1⟩
      apply hnonbase
      constructor
      · -- r = 1: from r-h = 1⁴ = 1, r+h = 1⁴ = 1 → r = 1, h = 0
        have : r - h = 1 := by rw [hα_eq, hα1]; ring
        have : r + h = 1 := by rw [hβ_eq, hβ1]; ring
        linarith
      · -- B = 1: from α=β=1 → b=1 → a=1 (from a²=1+1-1=1) → B=1
        have hb1 : b = 1 := by rw [hb_eq, hα1, hβ1]; ring
        have ha1 : a = 1 := by nlinarith [sq_nonneg (a - 1)]
        rw [hB_eq, ha1, hb1]; ring
    · -- B' < B: α.natAbs < B.natAbs
      rw [hB_eq]
      have hα_le_b : α ≤ b := by
        rw [hb_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
      have hb_le_ab : b ≤ a * b := le_mul_of_one_le_left hb.le ha
      sorry -- need: α < a*b, which follows from non-baseness
  · -- Case U = 5a⁴, V = b⁴ (symmetric descent on a)
    sorry

/-! ## Strong induction closure -/

theorem quartic_plus_from_descent
    {r B s : ℤ} (hsol : QuarticPlusZ r B s) : BaseZ r B := by
  suffices h : ∀ N, ∀ r B s : ℤ, B.natAbs = N → QuarticPlusZ r B s → BaseZ r B from
    h B.natAbs r B s rfl hsol
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro r B s hBN hsol
    have hBpos : 0 < B := hsol.2.1
    by_cases hbase : BaseZ r B
    · exact hbase
    · exfalso
      obtain ⟨r', B', s', hsol', hnotbase', hlt'⟩ :=
        quartic_plus_descent_step hsol hbase
      have hltN : B'.natAbs < N := by omega
      exact hnotbase' (ih B'.natAbs hltN r' B' s' rfl hsol')

/-! ## Final theorem (matches axiom signature in RationalPointsC20.lean) -/

theorem quartic_plus_proved (r B s : ℤ) (hB : 0 < B) (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) : r = 1 ∧ B = 1 :=
  quartic_plus_from_descent ⟨hr, hB, hcop, h⟩

end MazurProof.QuarticDescent
