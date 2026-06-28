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

/-- If B is odd and the quartic equation holds, then r is odd.
    (Mod 4: r even + B odd → s² ≡ 3 mod 4, impossible.) -/
theorem r_odd_of_B_odd {r B s : ℤ} (hB_odd : B % 2 = 1)
    (_hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one r with hr_even | hr_odd
  · exfalso
    obtain ⟨k, rfl⟩ : 2 ∣ r := ⟨r / 2, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, B = 2 * m + 1 := ⟨B / 2, by omega⟩
    -- 4 | s² + B⁴ (since r⁴ + r²B² = 16k⁴ + 4k²B²)
    have h4 : 4 ∣ (s ^ 2 + (2 * m + 1) ^ 4) :=
      ⟨4 * k ^ 4 + k ^ 2 * (2 * m + 1) ^ 2, by linarith⟩
    -- B⁴ ≡ 1 mod 4
    have hB4 : (2 * m + 1) ^ 4 % 4 = 1 := by
      have : (2 * m + 1) ^ 4 = 4 * (4 * m ^ 4 + 8 * m ^ 3 + 6 * m ^ 2 + 2 * m) + 1 := by ring
      omega
    -- s² ≡ 3 mod 4, but squares mod 4 are 0 or 1
    have hs_mod : s ^ 2 % 4 = 3 := by omega
    rcases Int.emod_two_eq_zero_or_one s with hs | hs
    · obtain ⟨j, rfl⟩ : 2 ∣ s := ⟨s / 2, by omega⟩
      have : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, s = 2 * j + 1 := ⟨s / 2, by omega⟩
      have : (2 * j + 1) ^ 2 = 4 * (j ^ 2 + j) + 1 := by ring
      omega
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
  obtain ⟨c, rfl⟩ : ∃ c, B = 4 * c + 2 := ⟨B / 4, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
  -- 8 | s² + B⁴ - r⁴ - r²B² ... actually just compute mod 8
  -- s² = r⁴ + r²B² - B⁴. Expand and compute mod 8.
  -- r = 2j+1: r² = 4j²+4j+1, r⁴ ≡ 1 mod 8
  -- B = 4c+2: B² = 16c²+16c+4 ≡ 4 mod 8, B⁴ ≡ 0 mod 16 ≡ 0 mod 8
  -- r²B² ≡ 1·4 = 4 mod 8
  -- s² ≡ 1 + 4 - 0 = 5 mod 8. But s² mod 8 ∈ {0,1,4}.
  have h8 : s ^ 2 % 8 = 5 := by
    have : s ^ 2 = (2 * j + 1) ^ 4 + (2 * j + 1) ^ 2 * (4 * c + 2) ^ 2 -
      (4 * c + 2) ^ 4 := heq
    have : s ^ 2 = 8 * (2 * j ^ 4 + 4 * j ^ 3 + 3 * j ^ 2 + j +
      8 * c ^ 2 * j ^ 2 + 8 * c ^ 2 * j + 2 * c ^ 2 + 8 * c * j ^ 2 + 8 * c * j +
      2 * c + 2 * j ^ 2 + 2 * j -
      32 * c ^ 4 - 64 * c ^ 3 - 48 * c ^ 2 - 16 * c - 2) + 5 := by linarith [
      show (2 * j + 1) ^ 4 = 8 * (2 * j ^ 4 + 4 * j ^ 3 + 3 * j ^ 2 + j) + 1 from by ring,
      show (2 * j + 1) ^ 2 * (4 * c + 2) ^ 2 = 8 * (8 * c ^ 2 * j ^ 2 + 8 * c ^ 2 * j + 2 * c ^ 2 + 8 * c * j ^ 2 + 8 * c * j + 2 * c + 2 * j ^ 2 + 2 * j) + 4 from by ring,
      show (4 * c + 2) ^ 4 = 8 * (32 * c ^ 4 + 64 * c ^ 3 + 48 * c ^ 2 + 16 * c + 2) from by ring]
    omega
  -- s² % 8 ∈ {0,1,4}
  rcases Int.emod_two_eq_zero_or_one s with hs | hs
  · obtain ⟨t, rfl⟩ : 2 ∣ s := ⟨s / 2, by omega⟩
    rcases Int.emod_two_eq_zero_or_one t with ht | ht
    · obtain ⟨u, rfl⟩ : 2 ∣ t := ⟨t / 2, by omega⟩
      have : (2 * (2 * u)) ^ 2 = 8 * (2 * u ^ 2) := by ring
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, t = 2 * u + 1 := ⟨t / 2, by omega⟩
      have : (2 * (2 * u + 1)) ^ 2 = 8 * (2 * u ^ 2 + 2 * u) + 4 := by ring
      omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rcases Int.emod_two_eq_zero_or_one t with ht | ht
    · obtain ⟨u, rfl⟩ : 2 ∣ t := ⟨t / 2, by omega⟩
      have : (2 * (2 * u) + 1) ^ 2 = 8 * (2 * u ^ 2 + u) + 1 := by ring
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, t = 2 * u + 1 := ⟨t / 2, by omega⟩
      have := show (2 * (2 * u + 1) + 1) ^ 2 = 8 * (2 * u ^ 2 + 3 * u + 1) + 1 from by ring
      omega

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
    have hprodGF₂ : G * F₂ = C ^ 4 := by
      have h := hprod; rw [hF₁eq, mul_assoc] at h
      exact mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0) h
    have hcopGF₂ : IsCoprime G F₂ := by
      have h := hcopI; rw [hF₁eq] at h; exact h.of_mul_left_right
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
      Or.inr ⟨by nlinarith [hF₁eq, hGa], hF₂b⟩⟩
  · -- 5 | F₂: symmetric
    obtain ⟨G, hF₂eq⟩ := h5F₂
    have hG : 0 < G := by nlinarith
    have hprodF₁G : F₁ * G = C ^ 4 := by
      have h := hprod; rw [hF₂eq] at h
      have h2 : 5 * (F₁ * G) = 5 * C ^ 4 := by convert h using 1; ring
      omega
    have hcopF₁G : IsCoprime F₁ G := by
      have h := hcopI; rw [hF₂eq] at h; exact h.of_mul_right_right
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
      Or.inl ⟨hF₁a, by nlinarith [hF₂eq, hGb]⟩⟩

/-- gcd(r-h, r+h) = 1 when r odd, h even, gcd(r,b) = 1, r² = h² + b⁴. -/
theorem coprime_rh {r h b : ℤ} (hr_odd : r % 2 = 1) (hh_even : h % 2 = 0)
    (hcop_rb : Int.gcd r b = 1) (hb : 0 < b) (heq : r ^ 2 = h ^ 2 + b ^ 4) :
    Int.gcd (r - h) (r + h) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hcopI : IsCoprime r b := Int.isCoprime_iff_gcd_eq_one.mpr hcop_rb
  have h2h : (2 : ℤ) ∣ h := Int.dvd_of_emod_eq_zero hh_even
  by_contra hnotcop
  rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
  have hU_ne : (r - h) ≠ 0 := by
    intro heq_rh
    have hr_eq : r = h := by linarith
    rw [hr_eq] at heq
    have hb0 : b ^ 4 = 0 := by linarith
    linarith [show 0 < b ^ 4 from by positivity]
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
    have : (2 : ℤ) ∣ r := by rwa [show (r - h) + h = r from by ring] at this
    have : r % 2 = 0 := Int.emod_eq_zero_of_dvd this
    omega
  have hp_not_dvd_2 : ¬ (↑p : ℤ) ∣ 2 := by
    intro h; have := Int.Prime.dvd_pow' hp (show (↑p : ℤ) ∣ 2 ^ 1 from by simpa using h)
    rw [Int.natCast_dvd] at this
    exact hp_ne_2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) this) hp.two_le)
  -- p | r (from p | (r-h)+(r+h) = 2r, p odd)
  have hpr : (↑p : ℤ) ∣ r := by
    have : (↑p : ℤ) ∣ 2 * r := by
      have h1 := dvd_add hpU hpV
      rwa [show (r - h) + (r + h) = 2 * r from by ring] at h1
    exact (hp_prime_int.dvd_or_dvd this).resolve_left hp_not_dvd_2
  -- p | h (from p | (r+h)-(r-h) = 2h, p odd)
  have hph : (↑p : ℤ) ∣ h := by
    have : (↑p : ℤ) ∣ 2 * h := by
      have h1 := dvd_sub hpV hpU
      rwa [show (r + h) - (r - h) = 2 * h from by ring] at h1
    exact (hp_prime_int.dvd_or_dvd this).resolve_left hp_not_dvd_2
  -- p | b (from p | r² - h² = b⁴)
  have hpb : (↑p : ℤ) ∣ b := by
    have hpr2 : (↑p : ℤ) ∣ r ^ 2 := dvd_pow hpr (by norm_num : 2 ≠ 0)
    have hph2 : (↑p : ℤ) ∣ h ^ 2 := dvd_pow hph (by norm_num : 2 ≠ 0)
    have : (↑p : ℤ) ∣ b ^ 4 := by
      have h3 := dvd_sub hpr2 hph2
      rwa [show r ^ 2 - h ^ 2 = b ^ 4 from by linarith] at h3
    exact Int.Prime.dvd_pow' hp this
  -- p | r and p | b contradicts gcd(r,b) = 1
  exact hp_prime_int.not_unit (hcopI.isUnit_of_dvd' hpr hpb)

/-! ## Descent step (the hard core) -/

set_option maxHeartbeats 3200000 in
/-- From a non-base solution, produce a strictly smaller non-base solution. -/
theorem quartic_plus_descent_step :
    ∀ {r B s : ℤ}, QuarticPlusZ r B s → ¬ BaseZ r B →
      ∃ r' B' s' : ℤ, QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧
        B'.natAbs < B.natAbs := by
  intro r B s ⟨hr, hB, hcop, heq⟩ hnonbase
  rcases Int.emod_two_eq_zero_or_one B with hBeven | hBodd
  · -- Even B case: uses M=U/4, N=V/4, same descent structure
    -- TODO: define M, N, prove MN = 5B₁⁴, gcd(M,N) = 1, then same descent
    have ⟨hr_odd, h4B⟩ := even_B_props hBeven hr hB hcop heq
    -- B = 4k for some k, define B₁ = B/2
    obtain ⟨k, hBk⟩ := h4B
    have hk_pos : 0 < k := by omega
    set B₁ := B / 2 with hB₁_def
    have hB₁_eq : B = 2 * B₁ := by omega
    have hB₁_pos : 0 < B₁ := by omega
    -- s is odd, 4|U, 4|V (substitute r=2j+1, B=4k, ring+omega)
    obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
    have hs_odd : s % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one s with hs | hs
      · exfalso
        obtain ⟨t, rfl⟩ : 2 ∣ s := ⟨s / 2, by omega⟩
        rw [hBk] at heq; ring_nf at heq; omega
      · exact hs
    have h4U : (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) := by
      obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      exact ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 - t, by ring⟩
    have h4V : (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) := by
      obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      exact ⟨2 * j ^ 2 + 2 * j + 4 * k ^ 2 + t + 1, by ring⟩
    -- Define M = U/4, N = V/4
    set M := (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s) / 4
    set N := (2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s) / 4
    have hM_val : 4 * M = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 - 2 * s :=
      Int.mul_ediv_cancel' h4U
    have hN_val : 4 * N = 2 * (2 * j + 1) ^ 2 + (4 * k) ^ 2 + 2 * s :=
      Int.mul_ediv_cancel' h4V
    -- Make M, N opaque so rw can find 4*M patterns
    clear_value M N
    -- MN = 5 * B₁⁴ (via: 16MN = (4M)(4N) = UV = 5(4k)⁴ = 16·5B₁⁴)
    have hB₁_val : B₁ = 2 * k := by omega
    have hUV := UV_eq_five_mul_fourth heq
    rw [hBk] at hUV  -- substitute B = 4*k in hUV so expressions match h4U/h4V
    have hMN_prod : M * N = 5 * B₁ ^ 4 := by
      suffices h : 16 * (M * N) = 16 * (5 * B₁ ^ 4) by omega
      have h1 : 4*M - (2*(2*j+1)^2+(4*k)^2-2*s) = 0 := by linarith
      have h2 : 4*N - (2*(2*j+1)^2+(4*k)^2+2*s) = 0 := by linarith
      have hp1 : (4*M - (2*(2*j+1)^2+(4*k)^2-2*s)) * (4*N) = 0 := by rw [h1]; ring
      have hp2 : (2*(2*j+1)^2+(4*k)^2-2*s) * (4*N - (2*(2*j+1)^2+(4*k)^2+2*s)) = 0 := by
        rw [h2]; ring
      -- ring expands 16*M*N using M,N as opaque vars (after clear_value)
      have h_ring : 16 * (M * N) =
          (4*M - (2*(2*j+1)^2+(4*k)^2-2*s)) * (4*N) +
          (2*(2*j+1)^2+(4*k)^2-2*s) * (4*N - (2*(2*j+1)^2+(4*k)^2+2*s)) +
          (2*(2*j+1)^2+(4*k)^2-2*s) * (2*(2*j+1)^2+(4*k)^2+2*s) := by ring
      have h_rhs : 5 * (4*k)^4 = 16 * (5 * B₁^4) := by rw [hB₁_val]; ring
      -- Two-step: linarith for 16*MN = exprU*exprV, then trans chain
      have h_mid : 16 * (M * N) =
          (2*(2*j+1)^2+(4*k)^2-2*s) * (2*(2*j+1)^2+(4*k)^2+2*s) := by linarith
      exact h_mid.trans (hUV.trans h_rhs)
    -- M, N > 0
    have hMpos : 0 < M := by
      by_contra hle; push_neg at hle
      have hNpos : 0 < N := by nlinarith [hN_val, sq_nonneg (2*j+1), sq_nonneg k]
      have : M * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hNpos.le
      linarith [show 0 < 5 * B₁ ^ 4 from by positivity, hMN_prod]
    have hNpos : 0 < N := by nlinarith [hMN_prod, show 0 < 5 * B₁ ^ 4 from by positivity]
    -- gcd(M,N) = 1 (prime-divisor argument, same pattern as UV_coprime)
    have hMN_sum : M + N = (2 * j + 1) ^ 2 + 2 * B₁ ^ 2 := by
      have : 4 * (M + N) = 4 * ((2*j+1)^2 + 2*B₁^2) := by nlinarith [hM_val, hN_val, hB₁_val]
      omega
    have hNM_diff : N - M = s := by
      have : 4 * (N - M) = 4 * s := by nlinarith [hM_val, hN_val]
      omega
    have hMN_cop : Int.gcd M N = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      by_contra hnotcop
      rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
      have hg_gt1 : 1 < Int.gcd M N := by
        have : Int.gcd M N ≠ 0 := by
          rw [Int.gcd_def]; exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr (ne_of_gt hMpos))
        omega
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
      have hpM : (↑p : ℤ) ∣ M := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
      have hpN : (↑p : ℤ) ∣ N := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
      have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp_sum : (↑p : ℤ) ∣ (2*j+1)^2 + 2*B₁^2 := by
        have := dvd_add hpM hpN; rwa [hMN_sum] at this
      have hp_s : (↑p : ℤ) ∣ s := by have := dvd_sub hpN hpM; rwa [hNM_diff] at this
      have hp2_dvd : (↑p : ℤ) ^ 2 ∣ 5 * B₁ ^ 4 := by
        have : (↑p : ℤ) ^ 2 ∣ M * N := by
          rw [show (↑p : ℤ) ^ 2 = ↑p * ↑p from by ring]; exact mul_dvd_mul hpM hpN
        rwa [hMN_prod] at this
      by_cases hpB₁ : (↑p : ℤ) ∣ B₁
      · have hp_B₁_sq : (↑p : ℤ) ∣ B₁^2 := dvd_pow hpB₁ (by norm_num : 2 ≠ 0)
        have hp_2B₁_sq : (↑p : ℤ) ∣ 2*B₁^2 := dvd_mul_of_dvd_right hp_B₁_sq 2
        have hp_r_sq : (↑p : ℤ) ∣ (2*j+1)^2 := by
          have h := dvd_sub hp_sum hp_2B₁_sq; simpa using h
        have hp_r : (↑p : ℤ) ∣ 2*j+1 := hp_prime_int.dvd_of_dvd_pow hp_r_sq
        have hp_B : (↑p : ℤ) ∣ B := by
          rw [hB₁_val] at hpB₁; rw [hBk]
          have : (↑p : ℤ) ∣ 2*(2*k) := dvd_mul_of_dvd_right hpB₁ 2
          rwa [show 2*(2*k) = 4*k from by ring] at this
        have : p ∣ Int.gcd (2*j+1) B := by
          rw [Int.gcd_def]
          exact Nat.dvd_gcd (Int.natCast_dvd.mp hp_r) (Int.natCast_dvd.mp hp_B)
        rw [hcop] at this
        exact absurd (Nat.le_of_dvd Nat.one_pos this) (by have := hp.two_le; omega)
      · have hpB4 : ¬ (↑p : ℤ) ∣ B₁^4 := fun h => hpB₁ (Int.Prime.dvd_pow' hp h)
        have hp5 : (↑p : ℤ) ∣ 5 := by
          have hpd : (↑p : ℤ) ∣ 5*B₁^4 := by
            have : (↑p : ℤ) ∣ (↑p : ℤ) ^ 2 := dvd_pow_self (↑p : ℤ) (by norm_num : 2 ≠ 0)
            exact dvd_trans this hp2_dvd
          exact (hp_prime_int.dvd_or_dvd hpd).resolve_right hpB4
        have hp_eq_5 : p = 5 := by
          have hle : p ∣ 5 := Int.natCast_dvd.mp hp5
          rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd p hle with h | h
          · exact absurd h (by have := hp.two_le; omega)
          · exact h
        subst hp_eq_5
        have : (5 : ℤ) ∣ B₁^4 := by
          have : (5 : ℤ)*5 ∣ 5*B₁^4 := by
            show (5 : ℤ) ^ 2 ∣ 5 * B₁ ^ 4; exact hp2_dvd
          exact (mul_dvd_mul_iff_left (by norm_num : (5:ℤ) ≠ 0)).mp this
        exact hpB₁ (Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) this)
    -- Even-B descent: coprime_factor_5_fourth → descent
    obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq, hfactor⟩ :=
      coprime_factor_5_fourth hMN_prod hMN_cop hMpos hNpos hB₁_pos
    -- Helper: gcd(r, d) = 1 for any d | B₁
    have hcop_rB := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hB₁_dvd_B : B₁ ∣ B := ⟨2, by rw [hB₁_eq]; omega⟩
    -- Even-B descent: for each coprime_factor branch, the descent variable is b (or a)
    -- The algebra gives r² = (A²-d²)²+4d⁴, then u=(r-(A²-d²))/2, v=(r+(A²-d²))/2, uv=d⁴
    rcases hfactor with ⟨hM_eq, hN_eq⟩ | ⟨hM_eq, hN_eq⟩
    · -- Case M = a⁴, N = 5b⁴: descent on b
      -- r² = (a²-b²)²+4b⁴
      have hr2 : (2*j+1)^2 = (a^2-b^2)^2 + 4*b^4 := by
        have hU := hM_eq; have hV := hN_eq
        nlinarith [hMN_sum, hB₁_eq,
          show (a*b)^2 = a^2*b^2 from by ring,
          show (a^2-b^2)^2 = a^4 - 2*a^2*b^2 + b^4 from by ring]
      -- gcd(r, b) = 1
      have hcop_rb : IsCoprime (2*j+1) b :=
        hcop_rB.of_isCoprime_of_dvd_right (dvd_trans ⟨a, by rw [hB₁_eq]; ring⟩ hB₁_dvd_B)
      -- a²-b² is odd (prove BEFORE set h to avoid opaque interaction)
      have h_raw_odd : (a^2 - b^2) % 2 = 1 := by
        have hab_even : (a*b) % 2 = 0 := by rw [← hB₁_eq, hB₁_val]; omega
        rcases Int.emod_two_eq_zero_or_one a with ha | ha
        · rcases Int.emod_two_eq_zero_or_one b with hb | hb
          · have := Int.dvd_coe_gcd ⟨a/2, by omega⟩ ⟨b/2, by omega⟩
            rw [hab_cop] at this; exact absurd this (by norm_num)
          · sorry -- a even, b odd → a²-b² odd (rfl + rw pattern mismatch)
        · sorry -- a odd, b even → a²-b² odd (same issue)
      set h := a^2 - b^2
      have h_odd : h % 2 = 1 := h_raw_odd
      -- (r-h)(r+h) = 4b⁴
      have hprod : ((2*j+1) - h) * ((2*j+1) + h) = 4*b^4 := by nlinarith [hr2]
      -- r-h and r+h both even
      have h2_sub : (2 : ℤ) ∣ ((2*j+1) - h) := by omega
      have h2_add : (2 : ℤ) ∣ ((2*j+1) + h) := by omega
      -- Define u = (r-h)/2, v = (r+h)/2
      set u := ((2*j+1) - h) / 2
      set v := ((2*j+1) + h) / 2
      have hu_val : 2 * u = (2*j+1) - h := Int.mul_ediv_cancel' h2_sub
      have hv_val : 2 * v = (2*j+1) + h := Int.mul_ediv_cancel' h2_add
      clear_value u v
      -- u + v = r, v - u = h
      have huv_sum : u + v = 2*j+1 := by omega
      have huv_diff : v - u = h := by omega
      -- u*v = b⁴ (from (2u)(2v) = 4b⁴)
      have huv_prod : u * v = b^4 := by
        apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 from by norm_num)
        have h4 : 4 * (u * v) = (2*u) * (2*v) := by ring
        rw [h4, hu_val, hv_val]
        rw [show (4 : ℤ) * b^4 = 4*b^4 from by ring]
        exact hprod
      -- u, v > 0 (from uv = b⁴ > 0 and u+v = r > 0)
      have hb4_pos : 0 < b^4 := by positivity
      have huv_pos_prod : 0 < u * v := by rw [huv_prod]; exact hb4_pos
      have hu_pos : 0 < u := by nlinarith [sq_nonneg u, sq_nonneg v, huv_sum]
      have hv_pos : 0 < v := by nlinarith [sq_nonneg u, sq_nonneg v, huv_sum]
      -- gcd(u,v) = 1
      have huv_cop : Int.gcd u v = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        by_contra hnotcop; rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
        have hg_gt1 : 1 < Int.gcd u v := by
          have : Int.gcd u v ≠ 0 := by
            rw [Int.gcd_def]; exact Nat.gcd_ne_zero_left (Int.natAbs_ne_zero.mpr (ne_of_gt hu_pos))
          omega
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
        have hpu : (↑p : ℤ) ∣ u := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
        have hpv : (↑p : ℤ) ∣ v := dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
        have hpr : (↑p : ℤ) ∣ (2*j+1) := by rw [← huv_sum]; exact dvd_add hpu hpv
        have hpb4 : (↑p : ℤ) ∣ b^4 := by rw [← huv_prod]; exact dvd_mul_of_dvd_left hpu v
        have hpb : (↑p : ℤ) ∣ b := Int.Prime.dvd_pow' hp hpb4
        exact (Nat.prime_iff_prime_int.mp hp).not_unit (hcop_rb.isUnit_of_dvd' hpr hpb)
      -- pos_fourth: u = α⁴, v = β⁴
      obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth huv_cop huv_prod hu_pos hv_pos
      obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
        (show Int.gcd v u = 1 by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact huv_prod) hv_pos hu_pos
      -- b = αβ
      have hb_eq : b = α * β := by
        apply eq_of_pos_fourth_eq hb (mul_pos hα_pos hβ_pos)
        calc b^4 = u * v := huv_prod.symm
          _ = α^4 * β^4 := by rw [hα_eq, hβ_eq]
          _ = (α * β)^4 := by ring
      -- New equation: a² = β⁴ + β²α² - α⁴
      have hnew_eq : a^2 = β^4 + β^2 * α^2 - α^4 := by
        have hh_val : h = β^4 - α^4 := by linarith [hα_eq, hβ_eq, huv_diff]
        have ha2 : a^2 = b^2 + h := by simp only [h]; ring
        rw [hb_eq] at ha2
        linarith [show (α * β)^2 = α^2 * β^2 from by ring]
      -- gcd(β, α) = 1
      have hcop_βα : Int.gcd β α = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have := Int.isCoprime_iff_gcd_eq_one.mpr huv_cop
        rw [hα_eq, hβ_eq] at this
        exact ((IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
          ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp
            (isCoprime_comm.mp this)))
      -- QuarticPlusZ β α a
      refine ⟨β, α, a, ⟨hβ_pos, hα_pos, hcop_βα, hnew_eq⟩, ?_, ?_⟩
      · -- Non-base
        intro ⟨hβ1, hα1⟩; apply hnonbase
        have hb1 : b = 1 := by rw [hb_eq, hα1, hβ1]; ring
        have ha_sq : a^2 = 1 := by rw [hnew_eq, hα1, hβ1]; norm_num
        have ha1 : a = 1 := by linarith [sq_nonneg (a - 1)]
        constructor
        · -- r = u+v = 1+1 = 2. But r = 2j+1 is odd. Contradiction.
          exfalso
          have : u = 1 := by rw [hα_eq, hα1]; ring
          have : v = 1 := by rw [hβ_eq, hβ1]; ring
          omega
        · -- B = 1: B₁ = ab = 1, B = 2B₁ = 2. But BaseZ r B needs B=1.
          -- Actually BaseZ (2j+1) B = BaseZ (2j+1) (4k). Needs 4k=1.
          -- B₁=1 → 2k=1 → k=0... but k>0. Contradiction!
          exfalso; nlinarith [hB₁_eq, hB₁_val]
      · -- B' < B: α.natAbs < B.natAbs (B = 4k after hBk)
        rw [hBk]
        have hα_le_b : α ≤ b := by rw [hb_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
        have hb_le_B₁ : b ≤ B₁ := by rw [hB₁_eq]; exact le_mul_of_one_le_left hb.le ha
        have hB₁_lt_4k : B₁ < 4*k := by rw [hB₁_val]; nlinarith
        have hα_lt : α < 4*k := by linarith
        exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hα_pos.le hα_lt
    · -- Case M = 5a⁴, N = b⁴: descent on a (symmetric)
      sorry
  · -- Odd B case (main case, fully proved)
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
        have hU := hU_eq; have hV := hV_eq
        rw [hB_eq] at hU hV
        nlinarith [show (a ^ 2 - b ^ 2) ^ 2 = a ^ 4 - 2 * a ^ 2 * b ^ 2 + b ^ 4 from by ring,
                   show (a * b) ^ 2 = a ^ 2 * b ^ 2 from by ring]
      -- Step 2: define h = (a²-b²)/2 (integer since a,b both odd)
      have ha_odd : a % 2 = 1 := by
        by_contra ha_even; push_neg at ha_even
        have ha2 : (2 : ℤ) ∣ a := ⟨a / 2, by omega⟩
        have : (2 : ℤ) ∣ a * b := dvd_mul_of_dvd_left ha2 b
        have : B % 2 = 0 := by rw [hB_eq]; omega
        omega
      have hb_odd : b % 2 = 1 := by
        by_contra hb_even; push_neg at hb_even
        have hb2 : (2 : ℤ) ∣ b := ⟨b / 2, by omega⟩
        have : (2 : ℤ) ∣ a * b := dvd_mul_of_dvd_right hb2 a
        have : B % 2 = 0 := by rw [hB_eq]; omega
        omega
      have h2_dvd : (2 : ℤ) ∣ (a ^ 2 - b ^ 2) := by
        have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
        rw [this]; exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ (a - b)) _
      set h := (a ^ 2 - b ^ 2) / 2 with hh_def
      have hh_eq : a ^ 2 - b ^ 2 = 2 * h := by
        rw [hh_def, Int.mul_ediv_cancel' h2_dvd]
      -- Step 3: r² = h² + b⁴ (from 4r² = (2h)² + 4b⁴)
      have hr2_eq : r ^ 2 = h ^ 2 + b ^ 4 := by
        have : 4 * r ^ 2 = 4 * h ^ 2 + 4 * b ^ 4 := by
          calc 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := h4r2
            _ = (2 * h) ^ 2 + 4 * b ^ 4 := by rw [← hh_eq]
            _ = 4 * h ^ 2 + 4 * b ^ 4 := by ring
        linarith
      -- Step 4: (r-h)(r+h) = b⁴
      have hprod_rh : (r - h) * (r + h) = b ^ 4 := by linarith [show (r - h) * (r + h) = r ^ 2 - h ^ 2 from by ring]
      -- Step 5: r-h > 0, r+h > 0
      have hb4_pos : 0 < b ^ 4 := by positivity
      have hrh_pos : 0 < r - h := by
        by_contra hle; push_neg at hle
        have : 0 < r + h := by linarith
        linarith [mul_nonpos_of_nonpos_of_nonneg hle this.le]
      have hrh_pos2 : 0 < r + h := by nlinarith [hprod_rh, hb4_pos, sq_nonneg (r + h)]
      -- Step 6: h is even (a²-b² ≡ 0 mod 4)
      have hh_even : h % 2 = 0 := by
        have : (a ^ 2 - b ^ 2) % 4 = 0 := by
          have h1 : (2 : ℤ) ∣ (a - b) := by omega
          have h2 : (2 : ℤ) ∣ (a + b) := by omega
          obtain ⟨m, hm⟩ := h1; obtain ⟨n, hn⟩ := h2
          have : (a - b) * (a + b) = 4 * (m * n) := by nlinarith
          have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
          omega
        omega
      -- Step 7: gcd(r-h, r+h) = 1
      have hcop_rb : Int.gcd r b = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have hcop_rB := Int.isCoprime_iff_gcd_eq_one.mpr hcop
        rw [hB_eq] at hcop_rB
        exact (IsCoprime.mul_right_iff.mp hcop_rB).2
      have hcop_rh := coprime_rh hr_odd hh_even hcop_rb hb hr2_eq
      -- Step 8: factor (r-h)(r+h) = b⁴ with gcd = 1 → r-h = α⁴, r+h = β⁴
      obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth hcop_rh hprod_rh
        hrh_pos hrh_pos2
      obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
        (show Int.gcd (r + h) (r - h) = 1 by rwa [Int.gcd_comm])
        (by rw [mul_comm]; exact hprod_rh) hrh_pos2 hrh_pos
      -- Step 9: b = αβ (from b⁴ = α⁴β⁴ = (αβ)⁴)
      have hb_eq : b = α * β := by
        apply eq_of_pos_fourth_eq hb (mul_pos hα_pos hβ_pos)
        calc b ^ 4 = (r - h) * (r + h) := hprod_rh.symm
          _ = α ^ 4 * β ^ 4 := by rw [hα_eq, hβ_eq]
          _ = (α * β) ^ 4 := by ring
      -- Step 10: new equation a² = β⁴ + β²α² - α⁴
      have hnew_eq : a ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
        have hh_val : 2 * h = β ^ 4 - α ^ 4 := by linarith [hα_eq, hβ_eq]
        have ha2 : a ^ 2 = b ^ 2 + 2 * h := by linarith [hh_eq]
        rw [hb_eq] at ha2
        linarith [show (α * β) ^ 2 = α ^ 2 * β ^ 2 from by ring]
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
          have ha_sq : a ^ 2 = 1 := by rw [hnew_eq, hα1, hβ1]; norm_num
          have ha1 : a = 1 := by linarith [sq_nonneg (a - 1)]
          rw [hB_eq, ha1, hb1]; ring
      · -- B' < B: α.natAbs < B.natAbs
        rw [hB_eq]
        have hα_le_b : α ≤ b := by
          rw [hb_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
        have hb_le_ab : b ≤ a * b := le_mul_of_one_le_left hb.le ha
        have hα_lt : α < a * b := by
          rcases eq_or_lt_of_le (le_trans hα_le_b hb_le_ab) with heq_ab | hlt
          · exfalso; apply hnonbase
            have hα_eq_b : α = b := le_antisymm hα_le_b (by linarith)
            have hβ1 : β = 1 := by
              have h1 := hb_eq; rw [hα_eq_b] at h1 -- h1 : b = b * β
              nlinarith [mul_pos hb hβ_pos]
            have ha1 : a = 1 := by nlinarith [mul_pos ha hb]
            -- b⁴ = b² (from r+h=1 and h=(1-b²)/2 → b⁴=b²)
            have hb1 : b = 1 := by
              have hrh1 : r + h = 1 := by rw [hβ_eq, hβ1]; ring
              have hrh2 : r - h = b ^ 4 := by rw [hα_eq_b] at hα_eq; linarith [hα_eq]
              have hh_val : h = (1 - b ^ 2) / 2 := by rw [hh_def, ha1]; ring_nf
              nlinarith [sq_nonneg (b - 1), sq_nonneg b]
            constructor
            · -- r = 1
              have : r + h = 1 := by rw [hβ_eq, hβ1]; ring
              have : r - h = 1 := by rw [hα_eq, hα_eq_b, hb1]; ring
              linarith
            · -- B = 1
              rw [hB_eq, ha1, hb1]; ring
          · exact hlt
        exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hα_pos.le hα_lt
    · -- Case U = 5a⁴, V = b⁴ (symmetric: descent on a instead of b)
      -- 4r² = (b²-a²)² + 4a⁴
      have h4r2 : 4 * r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
        have hU := hU_eq; have hV := hV_eq; rw [hB_eq] at hU hV
        nlinarith [show (b ^ 2 - a ^ 2) ^ 2 = b ^ 4 - 2 * b ^ 2 * a ^ 2 + a ^ 4 from by ring,
                   show (a * b) ^ 2 = a ^ 2 * b ^ 2 from by ring]
      have ha_odd : a % 2 = 1 := by
        by_contra ha_even; push_neg at ha_even
        have ha2 : (2 : ℤ) ∣ a := ⟨a / 2, by omega⟩
        have : (2 : ℤ) ∣ a * b := dvd_mul_of_dvd_left ha2 b
        have : B % 2 = 0 := by rw [hB_eq]; omega
        omega
      have hb_odd : b % 2 = 1 := by
        by_contra hb_even; push_neg at hb_even
        have hb2 : (2 : ℤ) ∣ b := ⟨b / 2, by omega⟩
        have : (2 : ℤ) ∣ a * b := dvd_mul_of_dvd_right hb2 a
        have : B % 2 = 0 := by rw [hB_eq]; omega
        omega
      have h2_dvd : (2 : ℤ) ∣ (b ^ 2 - a ^ 2) := by
        have : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
        rw [this]; exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ (b - a)) _
      set h := (b ^ 2 - a ^ 2) / 2 with hh_def
      have hh_eq : b ^ 2 - a ^ 2 = 2 * h := by rw [hh_def, Int.mul_ediv_cancel' h2_dvd]
      have hr2_eq : r ^ 2 = h ^ 2 + a ^ 4 := by
        have : 4 * r ^ 2 = 4 * h ^ 2 + 4 * a ^ 4 := by
          calc 4 * r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := h4r2
            _ = (2 * h) ^ 2 + 4 * a ^ 4 := by rw [← hh_eq]
            _ = 4 * h ^ 2 + 4 * a ^ 4 := by ring
        linarith
      have hprod_rh : (r - h) * (r + h) = a ^ 4 := by
        linarith [show (r - h) * (r + h) = r ^ 2 - h ^ 2 from by ring]
      have ha4_pos : 0 < a ^ 4 := by positivity
      have hrh_pos2 : 0 < r + h := by
        by_contra hle; push_neg at hle
        have : 0 < r - h := by linarith
        linarith [mul_nonpos_of_nonpos_of_nonneg hle this.le]
      have hrh_pos : 0 < r - h := by
        by_contra hle; push_neg at hle
        linarith [mul_nonpos_of_nonpos_of_nonneg hle hrh_pos2.le]
      have hh_even : h % 2 = 0 := by
        have : (b ^ 2 - a ^ 2) % 4 = 0 := by
          have : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
          have h1 : (2 : ℤ) ∣ (b - a) := by omega
          have h2 : (2 : ℤ) ∣ (b + a) := by omega
          obtain ⟨m, hm⟩ := h1; obtain ⟨n, hn⟩ := h2
          have : (b - a) * (b + a) = 4 * (m * n) := by nlinarith
          omega
        omega
      have hcop_ra : Int.gcd r a = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have hcop_rB := Int.isCoprime_iff_gcd_eq_one.mpr hcop; rw [hB_eq] at hcop_rB
        exact (IsCoprime.mul_right_iff.mp hcop_rB).1
      have hcop_rh := coprime_rh hr_odd hh_even hcop_ra ha hr2_eq
      obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth hcop_rh hprod_rh hrh_pos hrh_pos2
      obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
        (show Int.gcd (r + h) (r - h) = 1 by rwa [Int.gcd_comm])
        (by rw [mul_comm]; exact hprod_rh) hrh_pos2 hrh_pos
      have ha_eq : a = α * β := by
        apply eq_of_pos_fourth_eq ha (mul_pos hα_pos hβ_pos)
        calc a ^ 4 = (r - h) * (r + h) := hprod_rh.symm
          _ = α ^ 4 * β ^ 4 := by rw [hα_eq, hβ_eq]
          _ = (α * β) ^ 4 := by ring
      have hnew_eq : b ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
        have hh_val : 2 * h = β ^ 4 - α ^ 4 := by linarith [hα_eq, hβ_eq]
        have hb2 : b ^ 2 = a ^ 2 + 2 * h := by linarith [hh_eq]
        rw [ha_eq] at hb2
        linarith [show (α * β) ^ 2 = α ^ 2 * β ^ 2 from by ring]
      have hcop_βα : Int.gcd β α = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have := Int.isCoprime_iff_gcd_eq_one.mpr hcop_rh
        rw [hα_eq, hβ_eq] at this
        exact ((IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
          ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp
            (isCoprime_comm.mp this)))
      refine ⟨β, α, b, ⟨hβ_pos, hα_pos, hcop_βα, hnew_eq⟩, ?_, ?_⟩
      · intro ⟨hβ1, hα1⟩; apply hnonbase
        have ha1_val : a = 1 := by rw [ha_eq, hα1, hβ1]; ring
        have hb_sq : b ^ 2 = 1 := by rw [hnew_eq, hα1, hβ1]; norm_num
        have hb1_val : b = 1 := by linarith [sq_nonneg (b - 1)]
        constructor
        · have : r - h = 1 := by rw [hα_eq, hα1]; ring
          have : r + h = 1 := by rw [hβ_eq, hβ1]; ring
          linarith
        · rw [hB_eq, ha1_val, hb1_val]; ring
      · rw [hB_eq]
        have hα_le_a : α ≤ a := by rw [ha_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
        have ha_le_ab : a ≤ a * b := le_mul_of_one_le_right ha.le hb
        have hα_lt : α < a * b := by
          rcases eq_or_lt_of_le (le_trans hα_le_a ha_le_ab) with heq_ab | hlt
          · exfalso; apply hnonbase
            have hα_eq_a : α = a := le_antisymm hα_le_a (by linarith)
            have hβ1 : β = 1 := by
              have h1 := ha_eq; rw [hα_eq_a] at h1
              nlinarith [mul_pos ha hβ_pos]
            have hb1 : b = 1 := by nlinarith [mul_pos ha hb]
            have ha1 : a = 1 := by
              have hrh1 : r + h = 1 := by rw [hβ_eq, hβ1]; ring
              have hrh2 : r - h = a ^ 4 := by rw [hα_eq_a] at hα_eq; linarith [hα_eq]
              have hh_val : h = (1 - a ^ 2) / 2 := by rw [hh_def, hb1]; ring_nf
              nlinarith [sq_nonneg (a - 1), sq_nonneg a]
            constructor
            · have : r + h = 1 := by rw [hβ_eq, hβ1]; ring
              have : r - h = 1 := by rw [hα_eq, hα_eq_a, ha1]; ring
              linarith
            · rw [hB_eq, ha1, hb1]; ring
          · exact hlt
        exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hα_pos.le hα_lt

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
