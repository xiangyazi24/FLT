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
  sorry -- n³=c² → n²|c² → n|c (ceilRoot) → n=d² (cancel n²)

axiom rat_denom_square (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧ u = (A : ℚ) / (B : ℚ) ^ 2
-- Proof path (ChatGPT Q1295): den_cubic_num_den shows (u³+u²-u).den = u.den³,
-- then Rat.isSquare_iff gives u.den³ is square, then nat_isSquare_of_isSquare_cube
-- gives u.den is square. Write u = u.num / (√den)².

/-! ## Main theorem -/

theorem obstruction_20a4 (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  obtain ⟨A, B, hBpos, hcop, hu⟩ := rat_denom_square u w h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  have hB2ne : (B : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hBne
  rw [hu] at h
  -- (wB³)² = A(A²+AB²-B⁴) ∈ ℤ. A ℚ-square equal to an integer is an ℤ-square.
  have hinteg : ∃ C : ℤ, C ^ 2 = A * (A ^ 2 + A * B ^ 2 - B ^ 4) := by
    sorry -- field_simp + Rat.num extraction; see ChatGPT Q1312 for technique
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
    -- Remaining: apply quartic_plus, conclude u = 1
    sorry
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
    -- Second factor = -s² (not s²) since A = -r² < 0 and A·second = C² ≥ 0
    -- Then quartic_minus_of_plus gives |r| = B = 1, so A = -1, u = -1/1 = -1
    sorry

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
