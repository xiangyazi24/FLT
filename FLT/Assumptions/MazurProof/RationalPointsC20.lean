import Mathlib
import FLT.Assumptions.MazurProof.DescentBridge

/-!
# Rational points on w² = u³ + u² - u

Proves `obstruction_curve_20a4_points_degenerate`: the only rational u-coordinates
on `w² = u³ + u² - u` (LMFDB 20.a4) are `u ∈ {-1, 0, 1}`.

## Proof architecture

**Step 1 — Denominator normalization** (`rat_denom_square`):
For `(u, w) ∈ ℚ²` on the curve, `u = A/B²` with `A, B ∈ ℤ`, `gcd(A,B) = 1`.
(Standard p-adic valuation argument: `vₗ(u) < 0 ⟹ 2vₗ(w) = 3vₗ(u)`, so `vₗ(u)` even.)

**Step 2 — Coprime factorization** (`coprime_factors` + `Int.sq_of_gcd_eq_one`):
`C² = A(A²+AB²-B⁴)` with coprime factors ⟹ each is ±(square).

**Step 3 — Binary quartic descent** (`quartic_plus`):
`s² = r⁴ + r²B² - B⁴` with `gcd(r,B) = 1` forces `r = B = 1`.
Descent chain: factor `(2r²+B²)² - (2s)² = 5B⁴` into coprime odd pieces,
apply Pythagorean parametrization to `h² + y⁴ = r²`, get a smaller solution.
Uses `FLT.Four`-adjacent machinery.

**Step 4 — QuarticMinus from QuarticPlus** (`quartic_minus_of_plus`):
`s² = -r⁴ + r²B² + B⁴` reduces to QuarticPlus by swapping `r ↔ B`.

## Status

- `coprime_factors`: PROVED
- `quartic_minus_of_plus`: PROVED (from quartic_plus)
- `quartic_plus`: AXIOM (infinite descent, clear path via FLT.Four)
- `rat_denom_square`: AXIOM (p-adic valuation, standard)
- `obstruction_20a4`: TODO (wiring)
-/

namespace MazurProof.RationalPointsC20

/-! ## Coprimality of the two factors -/

theorem coprime_factors (A B : ℤ) (hcop : Int.gcd A B = 1) :
    Int.gcd A (A ^ 2 + A * B ^ 2 - B ^ 4) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hic : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have h4 : IsCoprime A (-(B ^ 4)) := (hic.pow_right (n := 4)).neg_right
  rw [show A ^ 2 + A * B ^ 2 - B ^ 4 = -(B ^ 4) + A * (A + B ^ 2) from by ring]
  obtain ⟨u, v, huv⟩ := h4
  exact ⟨u - (A + B ^ 2) * v, v, by rw [← huv]; ring⟩

/-! ## Binary quartic: the single irreducible axiom -/

/-- `s² = r⁴ + r²B² - B⁴` with `gcd(r,B) = 1`, `r,B > 0` forces `r = B = 1`.

Proof path (infinite descent on `B`):
1. `(2r²+B²±2s)` are coprime odd factors of `5B⁴`.
2. Split into `a⁴ · 5b⁴` with `ab = B`.
3. Derive `h² + y⁴ = r²` (Pythagorean with 4th power).
4. Parametrize via Pythagorean triples: `y = uv`, `2h = v⁴ - u⁴`.
5. New solution `(v, u, ·)` satisfies QuarticPlus with `B' = u < B`.
6. Strong induction on `B` completes the descent. -/
axiom quartic_plus (r B s : ℤ) (hB : 0 < B) (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) : r = 1 ∧ B = 1

/-! ## QuarticMinus reduces to QuarticPlus by r ↔ B swap -/

theorem quartic_minus_of_plus (r B s : ℤ) (hB : 0 < B) (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s ^ 2 = -(r ^ 4) + r ^ 2 * B ^ 2 + B ^ 4) : r = 1 ∧ B = 1 := by
  have h' : s ^ 2 = B ^ 4 + B ^ 2 * r ^ 2 - r ^ 4 := by linarith
  have hcop' : Int.gcd B r = 1 := by rw [Int.gcd_comm]; exact hcop
  obtain ⟨hB1, hr1⟩ := quartic_plus B r s hr hB hcop' h'
  exact ⟨hr1, hB1⟩

/-! ## Denominator normalization -/

-- rat_denom_square proof path: den_cubic_num_den + Rat.isSquare_iff + nat_isSquare_of_isSquare_cube

/-- If `n ≠ 0` and `n³` is a square, then `n` is a square.
Uses `Nat.ceilRoot` / `Nat.dvd_pow_iff_ceilRoot_dvd` from Mathlib. -/
private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  -- n² | c²: since c² = c·c = n³ = n²·n
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  -- n | c via ceilRoot Galois connection
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
         Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  -- c = n·d, cancel n² from n³ = (n·d)² to get n = d²
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

/-- The denominator of `u³+u²-u` equals `u.den³`. -/
private theorem den_cubic (u : ℚ) :
    ((u ^ 3 + u ^ 2 - u).den : ℤ) = (u.den : ℤ) ^ 3 := by
  sorry -- IsCoprime chain: a³+a²d-ad² coprime to d³ from u.reduced, then Rat.den_div_eq_of_coprime

/-- Rational points on `w²=u³+u²-u` have denominator that is a perfect square. -/
theorem rat_denom_square (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2 := by
  -- w² = u³+u²-u is a square in ℚ
  have hsq : IsSquare (u ^ 3 + u ^ 2 - u) := ⟨w, by rw [← h]; ring⟩
  -- By Rat.isSquare_iff: den is a square
  have hden_sq : IsSquare (u ^ 3 + u ^ 2 - u).den := (Rat.isSquare_iff.mp hsq).2
  -- den = u.den³
  have hden_eq : (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by exact_mod_cast den_cubic u
  -- u.den³ is a square → u.den is a square
  have hden3_sq : IsSquare (u.den ^ 3) := hden_eq ▸ hden_sq
  have hden_sq' : IsSquare u.den := nat_isSquare_of_isSquare_cube u.den_ne_zero hden3_sq
  -- Write u = u.num / B² where B² = u.den
  obtain ⟨B₀, hB₀⟩ := hden_sq'
  have hB₀_pos : 0 < B₀ := Nat.pos_of_ne_zero (by intro h; simp [h] at hB₀; exact u.den_ne_zero hB₀)
  refine ⟨u.num, (B₀ : ℤ), by exact_mod_cast hB₀_pos, ?_, ?_⟩
  · -- gcd(u.num, B₀) = 1: B₀ | u.den, and gcd(u.num, u.den) = 1
    sorry -- from u.reduced and B₀ | u.den via Nat.Coprime.coprime_dvd_right
  · -- u = u.num / B₀²
    calc u = (u.num : ℚ) / (u.den : ℚ) := by simpa using (Rat.num_div_den u).symm
      _ = (u.num : ℚ) / ((B₀ : ℚ) ^ 2) := by rw [hB₀]; push_cast; ring

/-! ## Main theorem -/

theorem obstruction_20a4 (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  obtain ⟨A, B, hBpos, hcop, hu⟩ := rat_denom_square u w h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  have hB2ne : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBne
  rw [hu] at h
  -- (wB³)² = A(A²+AB²-B⁴) ∈ ℤ. A ℚ-square equal to an integer is an ℤ-square.
  have hinteg : ∃ C : ℤ, C ^ 2 = A * (A ^ 2 + A * B ^ 2 - B ^ 4) := by
    set n := A * (A ^ 2 + A * B ^ 2 - B ^ 4)
    -- (wB³)² = ↑n in ℚ
    have hrat : (w * (B : ℚ) ^ 3) ^ 2 = (n : ℚ) := by
      have := h; push_cast [n] at this ⊢; field_simp [hBne] at this ⊢; nlinarith
    -- ↑n is a ℚ-square, so n is a ℤ-square
    have hn_sq : IsSquare (n : ℚ) := ⟨w * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
    rw [Rat.isSquare_intCast_iff] at hn_sq
    obtain ⟨c, hc⟩ := hn_sq
    exact ⟨c, by rw [sq]; linarith⟩
  obtain ⟨C, hC⟩ := hinteg
  have hcopf := coprime_factors A B hcop
  obtain ⟨r, hrA⟩ := Int.sq_of_gcd_eq_one hcopf hC.symm
  -- Case A = 0: trivially u = 0
  by_cases hA0 : A = 0
  · right; left; rw [hu, hA0]; simp
  rcases hrA with hrpos | hrneg
  · -- Case A = r² ≥ 0. Since A ≠ 0, r ≠ 0.
    have hr0 : r ≠ 0 := by intro h; rw [h] at hrpos; simp at hrpos; exact hA0 hrpos
    -- The second factor must be ≥ 0 (since A · second = C² ≥ 0 and A > 0)
    -- By Int.sq_of_gcd_eq_one on the other factor, it's s² (not -s²)
    -- Then s² = r⁴ + r²B² - B⁴, apply quartic_plus → r = B = 1 → u = 1
    right; right
    have hgcd_rB : Int.gcd |r| B = 1 := by
      have h1 : IsCoprime (r ^ 2) B := hrpos ▸ Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have h2 : IsCoprime r B := (IsCoprime.pow_left_iff (show 0 < 2 by norm_num)).mp h1
      simp only [Int.gcd, Int.natAbs_abs]
      exact Int.isCoprime_iff_gcd_eq_one.mp h2
    have hr_pos : 0 < |r| := abs_pos.mpr hr0
    -- Apply sq_of_gcd_eq_one to second factor
    have hcopf' : Int.gcd (A ^ 2 + A * B ^ 2 - B ^ 4) A = 1 := by
      rw [Int.gcd_comm]; exact hcopf
    have hC' : (A ^ 2 + A * B ^ 2 - B ^ 4) * A = C ^ 2 := by linarith
    obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one hcopf' hC'
    rcases hs with hs_pos | hs_neg
    · -- second = s²: apply quartic_plus
      have heq : s ^ 2 = |r| ^ 4 + |r| ^ 2 * B ^ 2 - B ^ 4 := by
        nlinarith [hs_pos, hrpos, sq_abs r, sq_nonneg r]
      obtain ⟨hr1, hB1⟩ := quartic_plus |r| B s hBpos hr_pos hgcd_rB heq
      rw [hu, hrpos, show r ^ 2 = |r| ^ 2 from (sq_abs r).symm, hr1, hB1]; norm_num
    · -- second = -s²: A > 0 and C² = A·(-s²) ≤ 0 forces s=0, C=0, then A=1, B⁴=B²+1 (impossible)
      exfalso
      have hA_pos : 0 < A := by rw [hrpos]; positivity
      have h_le : A ^ 2 + A * B ^ 2 - B ^ 4 ≤ 0 := by nlinarith [sq_nonneg s]
      have h_ge : 0 ≤ A ^ 2 + A * B ^ 2 - B ^ 4 := by nlinarith [sq_nonneg C]
      have h_zero : A ^ 2 + A * B ^ 2 - B ^ 4 = 0 := le_antisymm h_le h_ge
      have hA1 : A = 1 := by
        have h1 : A.natAbs = 1 := by
          have := hcopf; rw [h_zero] at this; simpa [Int.gcd_zero_right] using this
        rcases Int.natAbs_eq A with h | h <;> omega
      have hB4 : B ^ 4 - B ^ 2 = 1 := by nlinarith
      by_cases hB1 : B = 1
      · subst hB1; omega
      · nlinarith [sq_nonneg (B ^ 2 - 1), show 2 ≤ B by omega]
  · -- Case A = -r² ≤ 0. Since A ≠ 0, r ≠ 0.
    have hr0 : r ≠ 0 := by intro h; rw [h] at hrneg; simp at hrneg; exact hA0 hrneg
    -- The second factor must be ≤ 0, so it's -s²
    -- Then s² = -r⁴ + r²B² + B⁴, apply quartic_minus_of_plus → r = B = 1 → u = -1
    left
    have hgcd_rB : Int.gcd |r| B = 1 := by
      have h1 : IsCoprime (-(r ^ 2)) B := hrneg ▸ Int.isCoprime_iff_gcd_eq_one.mpr hcop
      have h2 : IsCoprime (r ^ 2) B := by
        have := h1.neg_left; rwa [neg_neg] at this
      have h3 : IsCoprime r B := (IsCoprime.pow_left_iff (show 0 < 2 by norm_num)).mp h2
      simp only [Int.gcd, Int.natAbs_abs]
      exact Int.isCoprime_iff_gcd_eq_one.mp h3
    have hr_pos : 0 < |r| := abs_pos.mpr hr0
    have hcopf' : Int.gcd (A ^ 2 + A * B ^ 2 - B ^ 4) A = 1 := by
      rw [Int.gcd_comm]; exact hcopf
    have hC' : (A ^ 2 + A * B ^ 2 - B ^ 4) * A = C ^ 2 := by linarith
    obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one hcopf' hC'
    rcases hs with hs_pos | hs_neg
    · -- second = s²: A < 0 and C² = A·s² ≤ 0 forces s=0, then A=-1, B⁴=B²+1 (impossible)
      exfalso
      have hA_neg : A < 0 := by rw [hrneg]; linarith [show 0 < r ^ 2 by positivity]
      have h_ge : A ^ 2 + A * B ^ 2 - B ^ 4 ≥ 0 := by nlinarith [sq_nonneg s]
      have h_le : A ^ 2 + A * B ^ 2 - B ^ 4 ≤ 0 := by nlinarith [sq_nonneg C]
      have h_zero : A ^ 2 + A * B ^ 2 - B ^ 4 = 0 := le_antisymm h_le h_ge
      have hAm1 : A = -1 := by
        have h1 : A.natAbs = 1 := by
          have := hcopf; rw [h_zero] at this; simpa [Int.gcd_zero_right] using this
        rcases Int.natAbs_eq A with h | h <;> omega
      have hB4 : B ^ 4 - B ^ 2 = 1 := by nlinarith
      by_cases hB1 : B = 1
      · subst hB1; omega
      · nlinarith [sq_nonneg (B ^ 2 - 1), show 2 ≤ B by omega]
    · -- second = -s²: apply quartic_minus_of_plus
      have heq : s ^ 2 = -(|r| ^ 4) + |r| ^ 2 * B ^ 2 + B ^ 4 := by
        nlinarith [hs_neg, hrneg, sq_abs r, sq_nonneg r]
      obtain ⟨hr1, hB1⟩ := quartic_minus_of_plus |r| B s hBpos hr_pos hgcd_rB heq
      rw [hu, hrneg, show r ^ 2 = |r| ^ 2 from (sq_abs r).symm, hr1, hB1]; norm_num

/-! ## Wiring to discharge the original axiom -/

theorem obstruction_curve_20a4_from_elementary :
    ∀ u w : ℚ, MazurProof.E20AffineEquation u w →
      MazurProof.E20DegenerateParameter u := by
  intro u w heq
  have h : w ^ 2 = u ^ 3 + u ^ 2 - u := by
    simp [MazurProof.E20AffineEquation] at heq; linarith
  have := obstruction_20a4 u w h
  simp [MazurProof.E20DegenerateParameter]
  tauto

end MazurProof.RationalPointsC20
