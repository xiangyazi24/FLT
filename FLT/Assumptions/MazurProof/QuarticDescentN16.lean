import Mathlib
import FLT.Assumptions.MazurProof.QuarticDescent

/-!
# Infinite descent for s² = r⁴ - r²B² - B⁴ (N=16 analogue)

Proves `quartic_minus_proved`: there are no positive coprime integer solutions
to s² = r⁴ - r²B² - B⁴, so the conclusion r = 1 ∧ B = 1 holds vacuously.

The key identity is (2r²-B²)² - (2s)² = 5B⁴, i.e.,
  (2r²-B²-2s)(2r²-B²+2s) = 5B⁴

compared to the N=10 case which uses (2r²+B²)² - (2s)² = 5B⁴.

## Structure

1. Odd B is directly impossible (mod 8: s² ≡ 7 mod 8)
2. Even B descends: 4|B, M = U/4, N = V/4, coprime factorization of 5B₁⁴
3. Strong induction shows no solutions exist
4. The final theorem r = 1 ∧ B = 1 is vacuously true (from False)

The self-similar descent produces QuarticMinusZ again (not QuarticPlusZ),
because h = a²+b² (sum) replaces h = a²-b² (difference) from the N=10 case.
-/

namespace MazurProof.QuarticDescentN16

open MazurProof.QuarticDescent (pos_sq_of_coprime_mul_sq pos_fourth_of_coprime_mul_fourth
  coprime_factor_5_fourth)

/-! ## Predicates -/

def QuarticMinusZ (r B s : ℤ) : Prop :=
  0 < r ∧ 0 < B ∧ Int.gcd r B = 1 ∧
    s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4

/-! ## Private helpers -/

/-- Copied from QuarticDescent (private there). -/
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

/-! ## Helper lemmas -/

theorem UV_eq_five_mul_fourth_minus {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4) :
    (2 * r ^ 2 - B ^ 2 - 2 * s) * (2 * r ^ 2 - B ^ 2 + 2 * s) = 5 * B ^ 4 := by
  nlinarith [heq, sq_nonneg s, sq_nonneg r, sq_nonneg B,
    sq_nonneg (2 * r ^ 2 - B ^ 2)]

/-- If B is odd and the quartic minus equation holds, then r is odd.
    (Mod 4: r even + B odd → s² ≡ 3 mod 4, impossible.) -/
theorem r_odd_of_B_odd_minus {r B s : ℤ} (hB_odd : B % 2 = 1)
    (_hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one r with hr_even | hr_odd
  · exfalso
    obtain ⟨k, rfl⟩ : 2 ∣ r := ⟨r / 2, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, B = 2 * m + 1 := ⟨B / 2, by omega⟩
    -- s² + B⁴ = r⁴ - r²B² = 4(4k⁴ - k²B²)
    have h4 : 4 ∣ (s ^ 2 + (2 * m + 1) ^ 4) :=
      ⟨4 * k ^ 4 - k ^ 2 * (2 * m + 1) ^ 2, by nlinarith⟩
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
theorem even_B_props_minus {r B s : ℤ} (hB_even : B % 2 = 0) (_hr : 0 < r) (_hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4) :
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
  -- s² ≡ 5 mod 8 (r⁴ ≡ 1, r²B² ≡ 4, B⁴ ≡ 0 mod 8 → 1 - 4 - 0 = -3 ≡ 5)
  have h8 : s ^ 2 % 8 = 5 := by
    have : s ^ 2 = 8 * (2 * j ^ 4 + 4 * j ^ 3 + 3 * j ^ 2 + j -
      8 * c ^ 2 * j ^ 2 - 8 * c ^ 2 * j - 2 * c ^ 2 - 8 * c * j ^ 2 - 8 * c * j -
      2 * c - 2 * j ^ 2 - 2 * j -
      32 * c ^ 4 - 64 * c ^ 3 - 48 * c ^ 2 - 16 * c - 3) + 5 := by linarith [
      show (2 * j + 1) ^ 4 = 8 * (2 * j ^ 4 + 4 * j ^ 3 + 3 * j ^ 2 + j) + 1 from by ring,
      show (2 * j + 1) ^ 2 * (4 * c + 2) ^ 2 = 8 * (8 * c ^ 2 * j ^ 2 + 8 * c ^ 2 * j +
        2 * c ^ 2 + 8 * c * j ^ 2 + 8 * c * j + 2 * c + 2 * j ^ 2 + 2 * j) + 4 from by ring,
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

/-! ## Odd B impossibility -/

set_option maxHeartbeats 800000 in
/-- When r, B are both odd, the minus equation has no solutions (mod 8 obstruction).
    r⁴ ≡ 1, r²B² ≡ 1, B⁴ ≡ 1 mod 8, so s² ≡ 1-1-1 = -1 ≡ 7 mod 8, impossible. -/
theorem quartic_minus_odd_B_impossible {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1) (hB_odd : B % 2 = 1)
    (heq : s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4) : False := by
  have hr_odd : r % 2 = 1 := r_odd_of_B_odd_minus hB_odd hcop heq
  obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, B = 2 * m + 1 := ⟨B / 2, by omega⟩
  -- s² ≡ 7 mod 8 because odd² ≡ 1 mod 8
  -- Key lemma: (2a+1)² ≡ 1 mod 8 (from 4a(a+1) ≡ 0 mod 8)
  have odd_sq_mod8 : ∀ a : ℤ, 8 ∣ ((2 * a + 1) ^ 2 - 1) := by
    intro a
    rcases Int.emod_two_eq_zero_or_one a with ha | ha
    · obtain ⟨p, rfl⟩ : 2 ∣ a := ⟨a / 2, by omega⟩
      exact ⟨p * (2 * p + 1), by ring⟩
    · obtain ⟨p, rfl⟩ : ∃ p, a = 2 * p + 1 := ⟨a / 2, by omega⟩
      exact ⟨(2 * p + 1) * (p + 1), by ring⟩
  -- 8 | (r⁴-1): factor as ((2j+1)²-1)·((2j+1)²+1)
  have h1 : 8 ∣ ((2 * j + 1) ^ 4 - 1) := by
    have : (2 * j + 1) ^ 4 - 1 = ((2 * j + 1) ^ 2 - 1) * ((2 * j + 1) ^ 2 + 1) := by ring
    rw [this]; exact dvd_mul_of_dvd_left (odd_sq_mod8 j) _
  -- 8 | (r²B²-1): decompose as ((2j+1)²-1)·(2m+1)² + ((2m+1)²-1)
  have h2 : 8 ∣ ((2 * j + 1) ^ 2 * (2 * m + 1) ^ 2 - 1) := by
    have : (2 * j + 1) ^ 2 * (2 * m + 1) ^ 2 - 1 =
        ((2 * j + 1) ^ 2 - 1) * (2 * m + 1) ^ 2 + ((2 * m + 1) ^ 2 - 1) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left (odd_sq_mod8 j) _) (odd_sq_mod8 m)
  -- 8 | (B⁴-1)
  have h3 : 8 ∣ ((2 * m + 1) ^ 4 - 1) := by
    have : (2 * m + 1) ^ 4 - 1 = ((2 * m + 1) ^ 2 - 1) * ((2 * m + 1) ^ 2 + 1) := by ring
    rw [this]; exact dvd_mul_of_dvd_left (odd_sq_mod8 m) _
  -- s²+1 = (r⁴-1) - (r²B²-1) - (B⁴-1), hence 8 | (s²+1)
  have hident : s ^ 2 + 1 =
      ((2 * j + 1) ^ 4 - 1) - ((2 * j + 1) ^ 2 * (2 * m + 1) ^ 2 - 1) -
      ((2 * m + 1) ^ 4 - 1) := by linarith
  have h8 : 8 ∣ (s ^ 2 + 1) := by rw [hident]; exact dvd_sub (dvd_sub h1 h2) h3
  have hs_mod8 : s ^ 2 % 8 = 7 := by omega
  -- But s² mod 8 ∈ {0,1,4}
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

/-! ## Descent step -/

set_option maxHeartbeats 6400000 in
/-- From any QuarticMinusZ solution, produce a strictly smaller one.
    Odd B → direct contradiction (mod 8). Even B → descent via coprime factorization. -/
theorem quartic_minus_descent_step :
    ∀ {r B s : ℤ}, QuarticMinusZ r B s →
      ∃ r' B' s' : ℤ, QuarticMinusZ r' B' s' ∧ B'.natAbs < B.natAbs := by
  intro r B s ⟨hr, hB, hcop, heq⟩
  rcases Int.emod_two_eq_zero_or_one B with hBeven | hBodd
  · -- Even B case: 4|B, define M=U/4, N=V/4, descent
    have ⟨hr_odd, h4B⟩ := even_B_props_minus hBeven hr hB hcop heq
    obtain ⟨k, hBk⟩ := h4B
    have hk_pos : 0 < k := by omega
    set B₁ := B / 2 with hB₁_def
    have hB₁_eq : B = 2 * B₁ := by omega
    have hB₁_pos : 0 < B₁ := by omega
    obtain ⟨j, rfl⟩ : ∃ j, r = 2 * j + 1 := ⟨r / 2, by omega⟩
    -- s is odd
    have hs_odd : s % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one s with hs | hs
      · exfalso
        obtain ⟨t, rfl⟩ : 2 ∣ s := ⟨s / 2, by omega⟩
        rw [hBk] at heq; ring_nf at heq; omega
      · exact hs
    -- 4 | U and 4 | V (where U = 2r²-B²-2s, V = 2r²-B²+2s)
    have h4U : (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 - 2 * s) := by
      obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      exact ⟨2 * j ^ 2 + 2 * j - 4 * k ^ 2 - t, by ring⟩
    have h4V : (4 : ℤ) ∣ (2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 + 2 * s) := by
      obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      exact ⟨2 * j ^ 2 + 2 * j - 4 * k ^ 2 + t + 1, by ring⟩
    -- Define M = U/4, N = V/4
    set M := (2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 - 2 * s) / 4
    set N := (2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 + 2 * s) / 4
    have hM_val : 4 * M = 2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 - 2 * s :=
      Int.mul_ediv_cancel' h4U
    have hN_val : 4 * N = 2 * (2 * j + 1) ^ 2 - (4 * k) ^ 2 + 2 * s :=
      Int.mul_ediv_cancel' h4V
    clear_value M N
    -- MN = 5 * B₁⁴
    have hB₁_val : B₁ = 2 * k := by omega
    have hUV := UV_eq_five_mul_fourth_minus heq
    rw [hBk] at hUV
    have hMN_prod : M * N = 5 * B₁ ^ 4 := by
      suffices h : 16 * (M * N) = 16 * (5 * B₁ ^ 4) by omega
      have h1 : 4*M - (2*(2*j+1)^2-(4*k)^2-2*s) = 0 := by linarith
      have h2 : 4*N - (2*(2*j+1)^2-(4*k)^2+2*s) = 0 := by linarith
      have hp1 : (4*M - (2*(2*j+1)^2-(4*k)^2-2*s)) * (4*N) = 0 := by rw [h1]; ring
      have hp2 : (2*(2*j+1)^2-(4*k)^2-2*s) * (4*N - (2*(2*j+1)^2-(4*k)^2+2*s)) = 0 := by
        rw [h2]; ring
      have h_ring : 16 * (M * N) =
          (4*M - (2*(2*j+1)^2-(4*k)^2-2*s)) * (4*N) +
          (2*(2*j+1)^2-(4*k)^2-2*s) * (4*N - (2*(2*j+1)^2-(4*k)^2+2*s)) +
          (2*(2*j+1)^2-(4*k)^2-2*s) * (2*(2*j+1)^2-(4*k)^2+2*s) := by ring
      have h_rhs : 5 * (4*k)^4 = 16 * (5 * B₁^4) := by rw [hB₁_val]; ring
      have h_mid : 16 * (M * N) =
          (2*(2*j+1)^2-(4*k)^2-2*s) * (2*(2*j+1)^2-(4*k)^2+2*s) := by linarith
      exact h_mid.trans (hUV.trans h_rhs)
    -- M + N = (2j+1)² - 2B₁²
    have hMN_sum : M + N = (2 * j + 1) ^ 2 - 2 * B₁ ^ 2 := by
      have : 4 * (M + N) = 4 * ((2*j+1)^2 - 2*B₁^2) := by nlinarith [hM_val, hN_val, hB₁_val]
      omega
    -- N - M = s
    have hNM_diff : N - M = s := by
      have : 4 * (N - M) = 4 * s := by nlinarith [hM_val, hN_val]
      omega
    -- M, N > 0
    have hMN_sum_pos : 0 < M + N := by
      rw [hMN_sum]
      -- From s²≥0: (2j+1)⁴ ≥ (2j+1)²(4k)²+(4k)⁴
      -- → (2j+1)² ≥ (4k)² ≥ 2B₁²
      have h_sq_nn : 0 ≤ s ^ 2 := sq_nonneg s
      have h_ge : (2*j+1)^4 ≥ (2*j+1)^2*(4*k)^2 + (4*k)^4 := by nlinarith
      have h_r2_ge : (2*j+1)^2 ≥ (4*k)^2 := by
        by_contra hlt; push_neg at hlt
        have : ((2*j+1)^2)^2 < (2*j+1)^2 * (4*k)^2 + ((4*k)^2)^2 := by
          nlinarith [sq_nonneg (2*j+1), sq_nonneg (4*k)]
        nlinarith [show ((2*j+1)^2)^2 = (2*j+1)^4 from by ring,
                   show ((4*k)^2)^2 = (4*k)^4 from by ring]
      nlinarith [hB₁_val]
    have hMN_prod_pos : 0 < 5 * B₁ ^ 4 := by positivity
    have hMpos : 0 < M := by
      by_contra hle; push_neg at hle
      have hNpos : 0 < N := by nlinarith
      have : M * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hNpos.le
      linarith [hMN_prod]
    have hNpos : 0 < N := by
      by_contra hle; push_neg at hle
      linarith [mul_nonpos_of_nonneg_of_nonpos hMpos.le hle, hMN_prod]
    -- gcd(M,N) = 1
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
      have hp_sum : (↑p : ℤ) ∣ (2*j+1)^2 - 2*B₁^2 := by
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
          have h := dvd_add hp_sum hp_2B₁_sq
          rwa [show (2*j+1)^2 - 2*B₁^2 + 2*B₁^2 = (2*j+1)^2 from by ring] at h
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
    -- Factor 5B₁⁴ into coprime fourth powers
    obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq_ab, hfactor⟩ :=
      coprime_factor_5_fourth hMN_prod hMN_cop hMpos hNpos hB₁_pos
    -- Helper: gcd(r, d) = 1 for any d | B₁ | B
    have hcop_rB := Int.isCoprime_iff_gcd_eq_one.mpr hcop
    have hB₁_dvd_B : B₁ ∣ B := ⟨2, by rw [hB₁_eq]; omega⟩
    rcases hfactor with ⟨hM_eq, hN_eq⟩ | ⟨hM_eq, hN_eq⟩
    · -- Case M = a⁴, N = 5b⁴: descent on b
      -- (2j+1)² = (a²+b²)² + 4b⁴
      have hr2 : (2*j+1)^2 = (a^2+b^2)^2 + 4*b^4 := by
        nlinarith [hMN_sum, hB₁_eq_ab,
          show (a*b)^2 = a^2*b^2 from by ring,
          show (a^2+b^2)^2 = a^4 + 2*a^2*b^2 + b^4 from by ring]
      -- gcd(r, b) = 1
      have hcop_rb : IsCoprime (2*j+1) b :=
        hcop_rB.of_isCoprime_of_dvd_right (dvd_trans ⟨a, by rw [hB₁_eq_ab]; ring⟩ hB₁_dvd_B)
      -- a²+b² is odd (since B₁=ab is even and gcd(a,b)=1, exactly one of a,b is even)
      have h_raw_odd : (a^2 + b^2) % 2 = 1 := by
        have hab_even : (a*b) % 2 = 0 := by rw [← hB₁_eq_ab, hB₁_val]; omega
        rcases Int.emod_two_eq_zero_or_one a with ha_ev | ha_od
        · rcases Int.emod_two_eq_zero_or_one b with hb_ev | hb_od
          · exfalso
            have h2a : (2 : ℤ) ∣ a := ⟨a/2, by omega⟩
            have h2b : (2 : ℤ) ∣ b := ⟨b/2, by omega⟩
            have := Int.dvd_coe_gcd h2a h2b
            rw [hab_cop] at this; exact absurd this (by norm_num)
          · -- a even, b odd → a²+b² odd
            have ha2 : a^2 % 2 = 0 := by
              have h2a : (2 : ℤ) ∣ a := by omega
              have : (2 : ℤ) ∣ a^2 := dvd_pow h2a (by norm_num : 2 ≠ 0)
              omega
            have hb2 : b^2 % 2 = 1 := by
              have h2b1 : (2 : ℤ) ∣ (b - 1) := by omega
              have : b^2 - 1 = (b-1)*(b+1) := by ring
              have : (2 : ℤ) ∣ (b^2 - 1) := this ▸ dvd_mul_of_dvd_left h2b1 _
              omega
            omega
        · -- a odd → b must be even (from a*b even, a odd)
          have hb_even : b % 2 = 0 := by
            rcases Int.emod_two_eq_zero_or_one b with hb | hb
            · exact hb
            · exfalso
              have h2_dvd_ab : (2 : ℤ) ∣ (a * b) := by omega
              have h2_ndvd_a : ¬ (2 : ℤ) ∣ a := by omega
              have h2_ndvd_b : ¬ (2 : ℤ) ∣ b := by omega
              have hp2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
              rcases hp2.dvd_or_dvd h2_dvd_ab with h | h
              · exact h2_ndvd_a h
              · exact h2_ndvd_b h
          have hb2 : b^2 % 2 = 0 := by
            have h2b : (2 : ℤ) ∣ b := by omega
            have : (2 : ℤ) ∣ b^2 := dvd_pow h2b (by norm_num : 2 ≠ 0)
            omega
          have ha2 : a^2 % 2 = 1 := by
            have h2a1 : (2 : ℤ) ∣ (a - 1) := by omega
            have : a^2 - 1 = (a-1)*(a+1) := by ring
            have : (2 : ℤ) ∣ (a^2 - 1) := this ▸ dvd_mul_of_dvd_left h2a1 _
            omega
          omega
      set h := a^2 + b^2
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
      have huv_sum : u + v = 2*j+1 := by omega
      have huv_diff : v - u = h := by omega
      -- u*v = b⁴
      have huv_prod : u * v = b^4 := by
        apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 from by norm_num)
        have h4 : 4 * (u * v) = (2*u) * (2*v) := by ring
        rw [h4, hu_val, hv_val, show (4 : ℤ) * b^4 = 4*b^4 from by ring]
        exact hprod
      -- u, v > 0
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
      -- u = α⁴, v = β⁴
      obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth huv_cop huv_prod hu_pos hv_pos
      obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
        (show Int.gcd v u = 1 by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact huv_prod) hv_pos hu_pos
      -- b = αβ
      have hb_eq : b = α * β := by
        apply eq_of_pos_fourth_eq hb (mul_pos hα_pos hβ_pos)
        calc b^4 = u * v := huv_prod.symm
          _ = α^4 * β^4 := by rw [hα_eq, hβ_eq]
          _ = (α * β)^4 := by ring
      -- New equation: a² = β⁴ - β²α² - α⁴ (QuarticMinusZ!)
      have hnew_eq : a^2 = β^4 - β^2 * α^2 - α^4 := by
        have hh_val : h = β^4 - α^4 := by linarith [hα_eq, hβ_eq, huv_diff]
        have ha2 : a^2 = h - b^2 := by simp only [h]; ring
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
      -- QuarticMinusZ β α a
      refine ⟨β, α, a, ⟨hβ_pos, hα_pos, hcop_βα, hnew_eq⟩, ?_⟩
      · -- B' < B: α.natAbs < B.natAbs
        rw [hBk]
        have hα_le_b : α ≤ b := by rw [hb_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
        have hb_le_B₁ : b ≤ B₁ := by rw [hB₁_eq_ab]; exact le_mul_of_one_le_left hb.le ha
        have hB₁_lt_4k : B₁ < 4*k := by rw [hB₁_val]; nlinarith
        have hα_lt : α < 4*k := by linarith
        exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hα_pos.le hα_lt
    · -- Case M = 5a⁴, N = b⁴: descent on a (symmetric)
      -- (2j+1)² = (b²+a²)² + 4a⁴ = (a²+b²)² + 4a⁴
      have hr2 : (2*j+1)^2 = (a^2+b^2)^2 + 4*a^4 := by
        nlinarith [hMN_sum, hB₁_eq_ab,
          show (a*b)^2 = a^2*b^2 from by ring,
          show (a^2+b^2)^2 = a^4 + 2*a^2*b^2 + b^4 from by ring]
      -- gcd(r, a) = 1
      have hcop_ra : IsCoprime (2*j+1) a :=
        hcop_rB.of_isCoprime_of_dvd_right (dvd_trans ⟨b, hB₁_eq_ab⟩ hB₁_dvd_B)
      -- a²+b² is odd
      have h_raw_odd : (a^2 + b^2) % 2 = 1 := by
        have hab_even : (a*b) % 2 = 0 := by rw [← hB₁_eq_ab, hB₁_val]; omega
        rcases Int.emod_two_eq_zero_or_one a with ha_ev | ha_od
        · rcases Int.emod_two_eq_zero_or_one b with hb_ev | hb_od
          · exfalso
            have h2a : (2 : ℤ) ∣ a := ⟨a/2, by omega⟩
            have h2b : (2 : ℤ) ∣ b := ⟨b/2, by omega⟩
            have := Int.dvd_coe_gcd h2a h2b
            rw [hab_cop] at this; exact absurd this (by norm_num)
          · -- a even, b odd → a²+b² odd
            have ha2 : a^2 % 2 = 0 := by
              have h2a : (2 : ℤ) ∣ a := by omega
              have : (2 : ℤ) ∣ a^2 := dvd_pow h2a (by norm_num : 2 ≠ 0)
              omega
            have hb2 : b^2 % 2 = 1 := by
              have h2b1 : (2 : ℤ) ∣ (b - 1) := by omega
              have : b^2 - 1 = (b-1)*(b+1) := by ring
              have : (2 : ℤ) ∣ (b^2 - 1) := this ▸ dvd_mul_of_dvd_left h2b1 _
              omega
            omega
        · -- a odd → b must be even
          have hb_even : b % 2 = 0 := by
            rcases Int.emod_two_eq_zero_or_one b with hb | hb
            · exact hb
            · exfalso
              have h2_dvd_ab : (2 : ℤ) ∣ (a * b) := by omega
              have h2_ndvd_a : ¬ (2 : ℤ) ∣ a := by omega
              have h2_ndvd_b : ¬ (2 : ℤ) ∣ b := by omega
              have hp2 : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
              rcases hp2.dvd_or_dvd h2_dvd_ab with h | h
              · exact h2_ndvd_a h
              · exact h2_ndvd_b h
          have hb2 : b^2 % 2 = 0 := by
            have h2b : (2 : ℤ) ∣ b := by omega
            have : (2 : ℤ) ∣ b^2 := dvd_pow h2b (by norm_num : 2 ≠ 0)
            omega
          have ha2 : a^2 % 2 = 1 := by
            have h2a1 : (2 : ℤ) ∣ (a - 1) := by omega
            have : a^2 - 1 = (a-1)*(a+1) := by ring
            have : (2 : ℤ) ∣ (a^2 - 1) := this ▸ dvd_mul_of_dvd_left h2a1 _
            omega
          omega
      set h := a^2 + b^2
      have h_odd : h % 2 = 1 := h_raw_odd
      -- (r-h)(r+h) = 4a⁴
      have hprod : ((2*j+1) - h) * ((2*j+1) + h) = 4*a^4 := by nlinarith [hr2]
      -- r-h and r+h both even
      have h2_sub : (2 : ℤ) ∣ ((2*j+1) - h) := by omega
      have h2_add : (2 : ℤ) ∣ ((2*j+1) + h) := by omega
      -- Define u = (r-h)/2, v = (r+h)/2
      set u := ((2*j+1) - h) / 2
      set v := ((2*j+1) + h) / 2
      have hu_val : 2 * u = (2*j+1) - h := Int.mul_ediv_cancel' h2_sub
      have hv_val : 2 * v = (2*j+1) + h := Int.mul_ediv_cancel' h2_add
      clear_value u v
      have huv_sum : u + v = 2*j+1 := by omega
      have huv_diff : v - u = h := by omega
      -- u*v = a⁴
      have huv_prod : u * v = a^4 := by
        apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 from by norm_num)
        have h4 : 4 * (u * v) = (2*u) * (2*v) := by ring
        rw [h4, hu_val, hv_val, show (4 : ℤ) * a^4 = 4*a^4 from by ring]
        exact hprod
      -- u, v > 0
      have ha4_pos : 0 < a^4 := by positivity
      have huv_pos_prod : 0 < u * v := by rw [huv_prod]; exact ha4_pos
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
        have hpa4 : (↑p : ℤ) ∣ a^4 := by rw [← huv_prod]; exact dvd_mul_of_dvd_left hpu v
        have hpa : (↑p : ℤ) ∣ a := Int.Prime.dvd_pow' hp hpa4
        exact (Nat.prime_iff_prime_int.mp hp).not_unit (hcop_ra.isUnit_of_dvd' hpr hpa)
      -- u = α⁴, v = β⁴
      obtain ⟨α, hα_pos, hα_eq⟩ := pos_fourth_of_coprime_mul_fourth huv_cop huv_prod hu_pos hv_pos
      obtain ⟨β, hβ_pos, hβ_eq⟩ := pos_fourth_of_coprime_mul_fourth
        (show Int.gcd v u = 1 by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact huv_prod) hv_pos hu_pos
      -- a = αβ
      have ha_eq : a = α * β := by
        apply eq_of_pos_fourth_eq ha (mul_pos hα_pos hβ_pos)
        calc a^4 = u * v := huv_prod.symm
          _ = α^4 * β^4 := by rw [hα_eq, hβ_eq]
          _ = (α * β)^4 := by ring
      -- b² = β⁴ - β²α² - α⁴ (QuarticMinusZ!)
      have hnew_eq : b^2 = β^4 - β^2 * α^2 - α^4 := by
        have hh_val : h = β^4 - α^4 := by linarith [hα_eq, hβ_eq, huv_diff]
        have hb2 : b^2 = h - a^2 := by simp only [h]; ring
        rw [ha_eq] at hb2
        linarith [show (α * β)^2 = α^2 * β^2 from by ring]
      -- gcd(β, α) = 1
      have hcop_βα : Int.gcd β α = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one]
        have := Int.isCoprime_iff_gcd_eq_one.mpr huv_cop
        rw [hα_eq, hβ_eq] at this
        exact ((IsCoprime.pow_left_iff (by norm_num : 0 < 4)).mp
          ((IsCoprime.pow_right_iff (by norm_num : 0 < 4)).mp
            (isCoprime_comm.mp this)))
      -- QuarticMinusZ β α b
      refine ⟨β, α, b, ⟨hβ_pos, hα_pos, hcop_βα, hnew_eq⟩, ?_⟩
      · -- B' < B
        rw [hBk]
        have hα_le_a : α ≤ a := by rw [ha_eq]; exact le_mul_of_one_le_right hα_pos.le hβ_pos
        have ha_le_B₁ : a ≤ B₁ := by rw [hB₁_eq_ab]; exact le_mul_of_one_le_right ha.le hb
        have hB₁_lt_4k : B₁ < 4*k := by rw [hB₁_val]; nlinarith
        have hα_lt : α < 4*k := by linarith
        exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hα_pos.le hα_lt
  · -- Odd B case: directly impossible
    exact (quartic_minus_odd_B_impossible hr hB hcop hBodd heq).elim

/-! ## Strong induction closure -/

/-- No positive coprime solution exists: any solution leads to an infinite
    descent, which is impossible by well-foundedness of ℕ. -/
theorem quartic_minus_no_solution
    {r B s : ℤ} (hsol : QuarticMinusZ r B s) : False := by
  suffices h : ∀ N, ∀ r B s : ℤ, B.natAbs = N → QuarticMinusZ r B s → False from
    h B.natAbs r B s rfl hsol
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro r B s hBN hsol
    obtain ⟨r', B', s', hsol', hlt'⟩ := quartic_minus_descent_step hsol
    exact ih B'.natAbs (by omega) r' B' s' rfl hsol'

/-! ## Final theorem (matches expected axiom signature) -/

/-- The equation s² = r⁴ - r²B² - B⁴ has no positive coprime integer solutions,
    so the conclusion r = 1 ∧ B = 1 holds vacuously. -/
theorem quartic_minus_proved (r B s : ℤ) (hB : 0 < B) (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s ^ 2 = r ^ 4 - r ^ 2 * B ^ 2 - B ^ 4) : r = 1 ∧ B = 1 :=
  (quartic_minus_no_solution ⟨hr, hB, hcop, h⟩).elim

end MazurProof.QuarticDescentN16
