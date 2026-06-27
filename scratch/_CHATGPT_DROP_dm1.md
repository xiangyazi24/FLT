# Q1451 (dm1/dm3): `rat_denom_square` for `w^2 = u^3 + u^2 - u`

This is the drop-in shape I would use.  It is written against the FLT repo's pinned Mathlib rev `96fd0fff...`.

The only outside dependency below is the lemma you said you already have:

```lean
nat_isSquare_of_isSquare_cube : ∀ {n : ℕ}, IsSquare (n ^ 3) → IsSquare n
```

If that lemma is already in scope with exactly that name, delete the `variable` line before `rat_denom_square`.

```lean
import Mathlib

namespace DM3

/-- The denominator of `u^3 + u^2 - u` is exactly `u.den^3`. -/
lemma den_cubic_num_den (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  let a : ℤ := u.num
  let d : ℤ := (u.den : ℤ)
  let N : ℤ := a ^ 3 + a ^ 2 * d - a * d ^ 2
  let D : ℕ := u.den ^ 3

  have hdpos : 0 < d := by
    exact_mod_cast u.den_pos
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hdpos)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDpos_int : (0 : ℤ) < (D : ℤ) := by
    exact_mod_cast hDpos

  -- `u.num` and `u.den` are coprime, as integers.
  have hred : IsCoprime a d := by
    simpa [a, d] using Rat.isCoprime_num_den u

  -- The numerator candidate is coprime to `d`.
  have ha3copd : IsCoprime (a ^ 3) d := by
    simpa using (hred.pow_left (m := 3))
  have hNcopd0 : IsCoprime (a ^ 3 + d * (a ^ 2 - a * d)) d :=
    ha3copd.add_mul_left_left (a ^ 2 - a * d)
  have hNcopd : IsCoprime N d := by
    convert hNcopd0 using 1
    ring_nf [N]

  -- Therefore it is coprime to `d^3`, hence to `D = u.den^3`.
  have hNcopd3 : IsCoprime N (d ^ 3) := by
    simpa using (hNcopd.pow_right (n := 3))
  have hNcopD : Nat.Coprime N.natAbs D := by
    have htmp : Nat.Coprime N.natAbs (d ^ 3).natAbs := by
      rw [← Int.isCoprime_iff_nat_coprime]
      exact hNcopd3
    simpa [D, d, Int.natAbs_pow] using htmp

  -- Rewrite the rational value with numerator `N` and denominator `D`.
  have hu : u = (a : ℚ) / (d : ℚ) := by
    rw [← Rat.num_div_den u]
    simp [a, d]
  have hD_cast : (D : ℚ) = (d : ℚ) ^ 3 := by
    simp [D, d]
  have hval : u ^ 3 + u ^ 2 - u = (N : ℚ) / (D : ℚ) := by
    rw [hu, hD_cast]
    field_simp [hdq]
    ring_nf [N]

  -- Now use the reduced-denominator theorem for rationals.
  have hden : ((N : ℚ) / (D : ℚ)).den = D := by
    simpa using
      (Rat.den_div_eq_of_coprime N (D : ℤ) hDpos_int (by simpa using hNcopD))
  rw [hval]
  exact hden

-- Delete this line if your lemma is already globally in scope.
variable (nat_isSquare_of_isSquare_cube : ∀ {n : ℕ}, IsSquare (n ^ 3) → IsSquare n)

/-- If `w^2 = u^3 + u^2 - u`, then the denominator of `u` is a square. -/
theorem rat_denom_square {u w : ℚ}
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    IsSquare u.den := by
  have hsq : IsSquare (u ^ 3 + u ^ 2 - u) := by
    refine ⟨w, ?_⟩
    rw [← h]
    ring
  have hden_sq0 : IsSquare ((u ^ 3 + u ^ 2 - u).den) :=
    (Rat.isSquare_iff.mp hsq).2
  have hden_sq3 : IsSquare (u.den ^ 3) := by
    simpa [den_cubic_num_den (u := u)] using hden_sq0
  exact nat_isSquare_of_isSquare_cube hden_sq3

end DM3
```

The important denominator step is this one:

```lean
have hNcopD : Nat.Coprime N.natAbs D := ...
have hden : ((N : ℚ) / (D : ℚ)).den = D := by
  simpa using
    (Rat.den_div_eq_of_coprime N (D : ℤ) hDpos_int (by simpa using hNcopD))
```

This avoids trying to use `Rat.add_den_dvd`/`mul_den_dvd`, which only give divisibility bounds and are too weak for the exact denominator.