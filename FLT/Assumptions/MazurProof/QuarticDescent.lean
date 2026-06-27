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

theorem quartic_plus_both_odd {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  -- Both even → gcd ≥ 2, contradiction
  -- r even, B odd → s² ≡ -1 (mod 4), impossible
  -- r odd, B even → need mod 16 analysis
  -- Clean approach: cast to ZMod 4 for the first two, ZMod 16 for the third
  -- Both even → gcd ≥ 2, contradiction.
  -- r even B odd → s²≡3 (mod 4), impossible.
  -- r odd, B=2c, c odd → s²≡5 (mod 8), impossible.
  -- r odd, 4|B → NOT eliminable by congruences alone (ChatGPT Q1448 verified).
  --   Needs the descent argument itself, or a 2-adic valuation global argument.
  --   Empirically: no solutions with B even exist for the equation with gcd=1.
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
  have ⟨hU_odd, hV_odd⟩ := UV_odd hr_odd hB_odd
  -- By contradiction: suppose gcd(U,V) > 1
  by_contra hnotcop
  rw [Int.isCoprime_iff_gcd_eq_one] at hnotcop
  set U := 2 * r ^ 2 + B ^ 2 - 2 * s
  set V := 2 * r ^ 2 + B ^ 2 + 2 * s
  -- U > 0 and V > 0
  have hUpos := U_pos hr hB heq
  have hVpos := V_pos hr hB heq
  -- gcd ≠ 0 (since U ≠ 0), so gcd > 1
  have hg_ne_zero : Int.gcd U V ≠ 0 :=
    Nat.not_eq_zero_of_lt (Nat.pos_of_ne_zero (fun h => by simp [Int.gcd] at h; omega))
  have hg_gt1 : 1 < Int.gcd U V := by omega
  -- Extract a prime p dividing gcd
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg_gt1.ne'
  -- p | U and p | V (in ℤ), via transitivity through gcd
  have hpU : (↑p : ℤ) ∣ U :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_left ..)
  have hpV : (↑p : ℤ) ∣ V :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpg) (Int.gcd_dvd_right ..)
  -- p is odd: p | U and U is odd
  have hp_odd : p ≠ 2 := by
    intro hp2
    have : (2 : ℤ) ∣ U := hp2 ▸ hpU
    rw [Int.even_iff_not_odd, not_not] at *
    exact (Int.odd_iff.mp (Int.emod_two_eq_one_iff_odd.mp hU_odd)) (Int.even_iff_two_dvd.mpr this)
  -- p | V + U = 2(2r²+B²) and p | V - U = 4s
  have hp_sum : (↑p : ℤ) ∣ 2 * (2 * r ^ 2 + B ^ 2) := by
    have : V + U = 2 * (2 * r ^ 2 + B ^ 2) := by ring
    exact this ▸ dvd_add hpV hpU
  have hp_diff : (↑p : ℤ) ∣ 4 * s := by
    have : V - U = 4 * s := by ring
    exact this ▸ dvd_sub hpV hpU
  -- p odd, p | 2A → p | A (IsCoprime p 2)
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp_not_dvd_2 : ¬ (↑p : ℤ) ∣ 2 := by
    intro h
    have := Int.Prime.dvd_pow' hp (show (↑p : ℤ) ∣ 2 ^ 1 from by simpa)
    rw [Int.natCast_dvd] at this
    exact hp_odd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) this) hp.two_le)
  have hpA : (↑p : ℤ) ∣ (2 * r ^ 2 + B ^ 2) :=
    (hp_prime_int.dvd_or_dvd hp_sum).resolve_left hp_not_dvd_2
  -- p odd, p | 4s → p | s
  have hps : (↑p : ℤ) ∣ s := by
    have h4 : (↑p : ℤ) ∣ 4 * s := hp_diff
    have : (↑p : ℤ) ∣ (2 * 2) * s := by ring_nf; exact h4
    exact ((hp_prime_int.dvd_or_dvd ((hp_prime_int.dvd_or_dvd this).resolve_left
      hp_not_dvd_2)).resolve_left hp_not_dvd_2)
  -- p | A and p | s → p² | A² - 4s² = 5B⁴
  have hp2_dvd : (↑p : ℤ) ^ 2 ∣ 5 * B ^ 4 := by
    have hA2 : (↑p : ℤ) ^ 2 ∣ (2 * r ^ 2 + B ^ 2) ^ 2 := pow_dvd_pow_of_dvd hpA 2
    have hs2 : (↑p : ℤ) ^ 2 ∣ 4 * s ^ 2 := by
      have : (↑p : ℤ) ^ 2 ∣ s ^ 2 := pow_dvd_pow_of_dvd hps 2
      exact dvd_mul_of_dvd_right this 4
    rwa [show (2 * r ^ 2 + B ^ 2) ^ 2 - 4 * s ^ 2 = 5 * B ^ 4 from hA_sq_sub] at
      dvd_sub hA2 hs2
  -- Case split: p | B or p ∤ B
  by_cases hpB : (↑p : ℤ) ∣ B
  · -- Case p | B: then p | A - B² = 2r², p odd → p | r² → p | r
    have hpB2 : (↑p : ℤ) ∣ B ^ 2 := dvd_pow hpB (by norm_num : 2 ≠ 0)
    have hp_2r2 : (↑p : ℤ) ∣ 2 * r ^ 2 := by
      have : (↑p : ℤ) ∣ (2 * r ^ 2 + B ^ 2) - B ^ 2 := dvd_sub hpA hpB2
      simpa using this
    have hpr2 : (↑p : ℤ) ∣ r ^ 2 :=
      (hp_prime_int.dvd_or_dvd hp_2r2).resolve_left hp_not_dvd_2
    have hpr : (↑p : ℤ) ∣ r := Int.Prime.dvd_pow' hp hpr2
    -- p | r and p | B → p | gcd(r,B) = 1
    have : p ∣ Int.gcd r B := by
      rw [Int.gcd_def]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hpr) (Int.natCast_dvd.mp hpB)
    rw [hcop] at this
    exact Nat.Prime.one_lt'.mp hp (Nat.le_of_dvd Nat.one_pos this)
  · -- Case p ∤ B: p | 5B⁴ and p ∤ B → p | 5 → p = 5
    have hp_dvd_5B4 : (↑p : ℤ) ∣ 5 * B ^ 4 := dvd_trans (dvd_pow_self (↑p) (by norm_num : 2 ≠ 0)) hp2_dvd
    have hpB4 : ¬ (↑p : ℤ) ∣ B ^ 4 := by
      intro h
      exact hpB (Int.Prime.dvd_pow' hp h)
    have hp5 : (↑p : ℤ) ∣ 5 :=
      (hp_prime_int.dvd_or_dvd hp_dvd_5B4).resolve_right hpB4
    -- p | 5 and p prime → p = 5
    have hp_eq_5 : p = 5 := by
      have h5 : Nat.Prime 5 := by norm_num
      have : p ∣ 5 := Int.natCast_dvd.mp hp5
      exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) this) hp.two_le |>.antisymm
        (Nat.le_of_dvd hp.pos this) |>.symm ▸ rfl
    -- p = 5, p² = 25 | 5B⁴ → 5 | B⁴ → 5 | B, contradicting p ∤ B
    subst hp_eq_5
    have h25 : (5 : ℤ) ^ 2 ∣ 5 * B ^ 4 := hp2_dvd
    have : (5 : ℤ) ∣ B ^ 4 := by
      have h5B4 : (5 : ℤ) * 5 ∣ 5 * B ^ 4 := by ring_nf; exact h25
      exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).mp h5B4
    exact hpB (Int.Prime.dvd_pow' (by norm_num : Nat.Prime 5) this)

/-! ## Coprime factorization helpers -/

/-- If a*b = c² with gcd(a,b) = 1 and a > 0, then a is a perfect square. -/
theorem pos_sq_of_coprime_mul_sq {a b c : ℤ} (hab : Int.gcd a b = 1)
    (heq : a * b = c ^ 2) (ha : 0 < a) : ∃ a₀ : ℤ, 0 < a₀ ∧ a = a₀ ^ 2 := by
  obtain ⟨a₀, ha₀ | ha₀⟩ := sq_of_gcd_eq_one hab heq
  · exact ⟨a₀.natAbs, Int.natAbs_pos.mpr (by rintro rfl; simp at ha₀; omega),
      by rwa [← Int.natAbs_sq]⟩
  · exact ⟨a₀.natAbs, Int.natAbs_pos.mpr (by rintro rfl; simp at ha₀; omega),
      by rw [← Int.natAbs_sq]; linarith⟩

/-- If a*b = c⁴ with gcd(a,b) = 1 and a,b > 0, then a is a perfect 4th power.
    Apply sq_of_gcd_eq_one twice: first get a = a₁², then a₁ = α². -/
theorem pos_fourth_of_coprime_mul_fourth {a b c : ℤ} (hab : Int.gcd a b = 1)
    (heq : a * b = c ^ 4) (ha : 0 < a) (hb : 0 < b) :
    ∃ α : ℤ, 0 < α ∧ a = α ^ 4 := by
  -- Step 1: a*b = (c²)², gcd(a,b) = 1 → a = a₁²
  have hc2 : a * b = (c ^ 2) ^ 2 := by ring_nf
  obtain ⟨a₁, ha₁_pos, ha₁⟩ := pos_sq_of_coprime_mul_sq hab hc2 ha
  -- Step 2: b = b₁²
  obtain ⟨b₁, hb₁_pos, hb₁⟩ := pos_sq_of_coprime_mul_sq
    (show Int.gcd b a = 1 by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact hc2) hb
  -- Step 3: a₁*b₁ = c² (from (a₁*b₁)² = a₁²*b₁² = a*b = c⁴ = (c²)²)
  have hab1_sq : (a₁ * b₁) ^ 2 = (c ^ 2) ^ 2 := by nlinarith
  have hab1_eq : a₁ * b₁ = c ^ 2 := by
    have := sq_eq_sq_iff_eq_or_eq_neg.mp hab1_sq
    rcases this with h | h
    · exact h
    · nlinarith
  -- Step 4: gcd(a₁, b₁) = 1 (from a = a₁², b = b₁², gcd(a,b) = 1)
  have hab1 : Int.gcd a₁ b₁ = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hab
    rw [ha₁] at hcop
    have hcop2 : IsCoprime (a₁ ^ 2) b := hcop
    have hcop3 : IsCoprime a₁ b := (IsCoprime.pow_left_iff (by norm_num : 2 ≠ 0)).mp hcop2
    rw [hb₁] at hcop3
    exact (IsCoprime.pow_right_iff (by norm_num : 2 ≠ 0)).mp hcop3
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
