# Q1451 (dm1/dm3): `rat_denom_square` for `w^2 = u^3 + u^2 - u`

Here is the self-contained proof block, except that `nat_isSquare_of_isSquare_cube` is kept as a parameter because you said it is already proved in your file.  If your lemma is already globally available with that exact name, delete the `variable` line and the theorem will use the global lemma.

```lean
import Mathlib

namespace DM3

/-- Exact denominator of `u^3 + u^2 - u`. -/
lemma den_cubic_num_den (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  let a : ℤ := u.num
  let d : ℤ := (u.den : ℤ)
  let N : ℤ := a ^ 3 + a ^ 2 * d - a * d ^ 2

  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast u.den_pos
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hd3pos : 0 < d ^ 3 := pow_pos hdpos 3
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast hdne
  have hd3q : ((d ^ 3 : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 3 hdne)

  -- Reduced numerator/denominator of `u`, as integer coprimality.
  have hred : IsCoprime a d := by
    simpa [a, d] using Rat.isCoprime_num_den u

  -- `N` is congruent to `a^3` modulo `d`, so it is coprime to `d`.
  have ha3copd : IsCoprime (a ^ 3) d := by
    simpa using (hred.pow_left (m := 3))
  have hNcopd0 : IsCoprime (a ^ 3 + d * (a ^ 2 - a * d)) d :=
    ha3copd.add_mul_left_left (a ^ 2 - a * d)
  have hNcopd : IsCoprime N d := by
    have hN_eq : N = a ^ 3 + d * (a ^ 2 - a * d) := by
      dsimp [N]
      ring
    rw [hN_eq]
    exact hNcopd0

  -- Hence `N` is coprime to `d^3`.
  have hNcopd3 : IsCoprime N (d ^ 3) := by
    simpa using (hNcopd.pow_right (n := 3))
  have hNcopd3_nat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hNcopd3

  -- Rewrite the cubic expression as the reduced rational `N / d^3`.
  have hu : u = (a : ℚ) / (d : ℚ) := by
    rw [← Rat.num_div_den u]
    simp [a, d]
  have hval : u ^ 3 + u ^ 2 - u = (N : ℚ) / (d ^ 3 : ℚ) := by
    rw [hu]
    field_simp [hdq, hd3q]
    ring_nf [N]

  -- `Rat.den_div_eq_of_coprime` returns an integer denominator equality.
  have hdenZ : (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3 :=
    Rat.den_div_eq_of_coprime (a := N) (b := d ^ 3) hd3pos hNcopd3_nat
  have hdenNat : ((N : ℚ) / (d ^ 3 : ℚ)).den = u.den ^ 3 := by
    exact Int.ofNat_injective (by
      simpa [d, Int.natCast_pow] using hdenZ)

  simpa [hval] using hdenNat

/--
External arithmetic input: if a cube is a square, then the base is a square.
Delete this variable line if your already-proved lemma is globally in scope as
`nat_isSquare_of_isSquare_cube`.
-/
variable (nat_isSquare_of_isSquare_cube : ∀ {n : ℕ}, IsSquare (n ^ 3) → IsSquare n)

/-- If `w^2 = u^3 + u^2 - u`, then the denominator of `u` is a square. -/
theorem rat_denom_square {u w : ℚ}
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    IsSquare u.den := by
  have hsq_expr : IsSquare (u ^ 3 + u ^ 2 - u) := by
    refine ⟨w, ?_⟩
    rw [← h]
    ring
  have hden_sq : IsSquare ((u ^ 3 + u ^ 2 - u).den) :=
    (Rat.isSquare_iff.mp hsq_expr).2
  have hden_cube_sq : IsSquare (u.den ^ 3) := by
    simpa [den_cubic_num_den (u := u)] using hden_sq
  exact nat_isSquare_of_isSquare_cube hden_cube_sq

end DM3
```

The core denominator proof is the `hNcopd → hNcopd3 → Rat.den_div_eq_of_coprime` chain.  The square-denominator theorem then becomes just `Rat.isSquare_iff` plus your cube-square arithmetic lemma.