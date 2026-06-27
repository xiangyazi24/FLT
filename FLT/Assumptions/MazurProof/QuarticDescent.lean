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
  sorry -- ZMod 4/16 case analysis: r even B odd → s²≡3(mod 4), both even → gcd≥2, r odd B even → s²≡5(mod 8)

/-! ## U, V properties -/

/-- U and V are both positive: UV = 5B⁴ > 0 and U+V = 4r²+2B² > 0 forces both positive. -/
theorem V_pos {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < 2 * r ^ 2 + B ^ 2 + 2 * s := by
  -- UV = 5B⁴ > 0, U+V = 4r²+2B² > 0 → both positive
  sorry

theorem U_pos {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < 2 * r ^ 2 + B ^ 2 - 2 * s := by
  sorry

/-- U and V are both odd when r, B are both odd. -/
theorem UV_odd {r B s : ℤ}
    (hr_odd : r % 2 = 1) (hB_odd : B % 2 = 1) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) % 2 = 1 ∧
    (2 * r ^ 2 + B ^ 2 + 2 * s) % 2 = 1 := by
  -- 2r²+B² ≡ 0+1 = 1 (mod 2) since B odd → B²≡1, and 2r²≡0. Then ±2s≡0.
  sorry

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
  sorry -- prime factor analysis: any common odd prime divides s and 2r²+B²,
        -- hence divides B⁴ (from equation) and 2r²+B², then divides r, contradicting gcd=1

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
