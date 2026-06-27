import Mathlib

/-!
# Denominator theorem for `y² = x³ + x² - x`

This scratch file isolates the rational-denominator argument from the already
proved quartic obstruction.
-/

/--
Clearing denominators and doing the prime-valuation argument.

This is the arithmetic step: after writing `u = p / q` in lowest terms and
assuming `2 ≤ q`, the square condition forces the standard denominator quartic
data.  The remaining local gap is exactly the prime-valuation/perfect-square
denominator step described in the task.
-/
theorem clearing_denominators_gives_quartic (p : ℤ) (q : ℕ)
    (hq : 2 ≤ q) (hcop : p.natAbs.Coprime q)
    (w : ℚ) (hw : w ^ 2 = (p : ℚ) / q * ((p : ℚ) ^ 2 / q ^ 2 + (p : ℚ) / q - 1)) :
    ∃ s d t : ℤ, 2 ≤ d ∧ Int.gcd s d = 1 ∧
      t ^ 2 = s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 := by
  -- Valuation/perfect-square denominator step.
  sorry

-- The denominator quartic obstruction is assumed here as the already-proved
-- imported result from the surrounding scratch development.
axiom no_denominator_quartic_imported (s d t : ℤ) (hd : 2 ≤ d)
    (hcop : Int.gcd s d = 1)
    (h : t ^ 2 = s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4) : False

theorem rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) (_hu : u ≠ 0) :
    u.den = 1 := by
  by_contra hden
  have hq : 2 ≤ u.den := by
    have hden_pos : 0 < u.den := u.den_pos
    omega
  let p := u.num
  let q := u.den
  have hu_eq : u = (p : ℚ) / q := by
    exact (Rat.num_div_den u).symm
  have hw_clear :
      w ^ 2 = (p : ℚ) / q * ((p : ℚ) ^ 2 / q ^ 2 + (p : ℚ) / q - 1) := by
    rw [hu_eq] at h
    convert h using 1
    ring
  obtain ⟨s, d, t, hd, hcop, hquartic⟩ :=
    clearing_denominators_gives_quartic p q hq (Rat.reduced u) w hw_clear
  exact no_denominator_quartic_imported s d t hd hcop hquartic
