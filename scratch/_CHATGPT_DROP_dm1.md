# Q1460 (dm1): `den_cubic` for `u^3 + u^2 - u`

The useful point is that `Rat.den_div_eq_of_coprime` already returns the denominator as an integer:

```lean
Rat.den_div_eq_of_coprime
  {a b : ℤ} (hb0 : 0 < b)
  (h : Nat.Coprime a.natAbs b.natAbs) :
  ((a / b : ℚ).den : ℤ) = b
```

So the proof can target the requested `ℤ` statement directly.

```lean
import Mathlib

namespace DM1

/-- Denominator of the cubic expression on the curve chart. -/
theorem den_cubic (u : ℚ) :
    ((u ^ 3 + u ^ 2 - u).den : ℤ) = (u.den : ℤ) ^ 3 := by
  let a : ℤ := u.num
  let d : ℤ := (u.den : ℤ)
  let N : ℤ := a ^ 3 + a ^ 2 * d - a * d ^ 2

  have hdpos : 0 < d := by
    exact_mod_cast u.den_pos
  have hd3pos : 0 < d ^ 3 := pow_pos hdpos 3
  have hdq : (d : ℚ) ≠ 0 := by
    have hdz : d ≠ 0 := ne_of_gt hdpos
    exact_mod_cast hdz

  -- Reduced numerator/denominator for `u`, as an integer coprimality statement.
  have hred : IsCoprime a d := by
    simpa [a, d] using Rat.isCoprime_num_den u

  -- `N ≡ a^3 (mod d)`, hence `N` is coprime to `d`.
  have ha3copd : IsCoprime (a ^ 3) d := by
    simpa using (hred.pow_left (m := 3))
  have hNcopd0 : IsCoprime (a ^ 3 + d * (a ^ 2 - a * d)) d :=
    ha3copd.add_mul_left_left (a ^ 2 - a * d)
  have hNcopd : IsCoprime N d := by
    convert hNcopd0 using 1
    ring_nf [N]

  -- Therefore `N` is coprime to `d^3`.
  have hNcopd3 : IsCoprime N (d ^ 3) := by
    simpa using (hNcopd.pow_right (n := 3))
  have hNcopd3Nat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hNcopd3

  -- Rewrite the rational expression with numerator `N` and denominator `d^3`.
  have hu : u = (a : ℚ) / (d : ℚ) := by
    rw [← Rat.num_div_den u]
    simp [a, d]
  have hval : u ^ 3 + u ^ 2 - u = (N : ℚ) / (d ^ 3 : ℚ) := by
    rw [hu]
    field_simp [hdq]
    ring_nf [N]

  -- Exact denominator of a reduced rational quotient.
  rw [hval]
  simpa [d] using
    (Rat.den_div_eq_of_coprime (a := N) (b := d ^ 3) hd3pos hNcopd3Nat)

end DM1
```

The most important line is the final one: because `b = d^3` is positive and coprime to `N`, Mathlib returns the exact integer denominator immediately.