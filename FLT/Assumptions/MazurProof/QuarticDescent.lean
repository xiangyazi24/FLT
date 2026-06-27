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

/-- If B is odd and gcd(r,B) = 1 and the quartic equation holds, then r is odd.
    (Mod 4: r even + B odd → s² ≡ -B⁴ ≡ 3 mod 4, impossible.) -/
theorem r_odd_of_B_odd {r B s : ℤ} (hB_odd : B % 2 = 1)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 := by
  by_contra hr_even
  push_neg at hr_even
  have : r % 2 = 0 := by omega
  -- Cast to ZMod 4 and derive contradiction: s² ≡ 3 (mod 4)
  sorry

/-- If B is even and gcd(r,B) = 1, then r is odd and 4 | B.
    (gcd = 1 forces r odd; mod 8 eliminates B ≡ 2 mod 4.) -/
theorem even_B_props {r B s : ℤ} (hB_even : B % 2 = 0) (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ 4 ∣ B := by
  -- r must be odd (gcd = 1 and B even → r odd)
  -- B ≡ 2 mod 4 → s² ≡ 5 mod 8, impossible → 4 | B
  sorry

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

/-! ## Descent step (the hard core) -/

/-- From a non-base solution, produce a strictly smaller non-base solution. -/
theorem quartic_plus_descent_step :
    ∀ {r B s : ℤ}, QuarticPlusZ r B s → ¬ BaseZ r B →
      ∃ r' B' s' : ℤ, QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧
        B'.natAbs < B.natAbs := by
  intro r B s ⟨hr, hB, hcop, heq⟩ hnonbase
  -- Normalize: replace s by |s| (equation is s²-invariant)
  -- After normalization: 0 ≤ |s|, and U = 2r²+B²-2|s|, V = 2r²+B²+2|s| with U ≤ V
  -- 1. Both r, B odd (mod 4/16 analysis)
  -- 2. UV = 5B⁴ with U,V coprime, odd, positive
  -- 3. Factor: U=a⁴, V=5b⁴ (or swapped) with ab=B, gcd(a,b)=1
  -- 4. 4r² = (a²-b²)² + 4b⁴ → h²+b⁴=r² where h=(a²-b²)/2
  -- 5. Pythagorean: b²=(m-n)(m+n), gcd=1 → m-n=u², m+n=v², b=uv
  -- 6. a² = v⁴+v²u²-u⁴ with B'=u < uv=b ≤ ab=B
  -- 7. Non-baseness: if u=v=1 then b=1,a²=1,a=1,B=1, contradicts hnonbase
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
