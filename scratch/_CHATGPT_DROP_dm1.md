# Q1361 (dm1/dm4): denominator square bridge for `w^2 = u^3+u^2-u`

Below is the Lean structure that compiles once the two intended local arithmetic facts are supplied:

1. `nat_isSquare_of_isSquare_cube`, which you explicitly allowed to be `sorry`.
2. `curve_rhs_den_eq_den_cube`, the curve-specific `Rat.den` normalization
   ```lean
   (u^3 + u^2 - u).den = u.den^3
   ```
   This is exactly the step that proves the numerator of
   `u^3+u^2-u = u.num * (u.num^2 + u.num*u.den^2 - u.den^4) / u.den^3`
   is coprime to `u.den^3`.

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace DM4

/-- If `n^3` is a square and `n ≠ 0`, then `n` is a square. -/
theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  -- Allowed local lemma from Q1338.
  sorry

/--
The curve-specific denominator computation.
For `u = a/b` in lowest terms, the numerator
`a*(a^2+a*b^2-b^4)` is coprime to `b`, hence the denominator is `b^3`.
-/
lemma curve_rhs_den_eq_den_cube (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  -- This is the nontrivial `Rat.den` normalization step.
  -- Prove it separately using `Rat.num_div_den`, `Rat.reduced`, and gcd arithmetic.
  sorry

/--
For a rational point `(u,w)` on `w^2 = u^3+u^2-u`, the denominator of `u`
is a square, so `u = A / B^2` in lowest terms.
-/
theorem rat_denom_square
    {u w : ℚ}
    (hcurve : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ A B : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
        u = (A : ℚ) / (B : ℚ) ^ 2 := by
  -- The right-hand side is a square in `ℚ` because it equals `w^2`.
  have hsq_rhs : IsSquare (u ^ 3 + u ^ 2 - u) := by
    refine ⟨w, ?_⟩
    rw [← hcurve]
    ring

  -- `Rat.isSquare_iff` says a rational is square iff its reduced numerator
  -- and denominator are squares.  We only need the denominator component.
  have hden_sq : IsSquare ((u ^ 3 + u ^ 2 - u).den) :=
    (Rat.isSquare_iff.mp hsq_rhs).2

  have hden_cube_sq : IsSquare (u.den ^ 3) := by
    simpa [curve_rhs_den_eq_den_cube u] using hden_sq

  have hden_ne : u.den ≠ 0 := Rat.den_ne_zero u
  have hden_isSquare : IsSquare u.den :=
    nat_isSquare_of_isSquare_cube hden_ne hden_cube_sq

  rcases hden_isSquare with ⟨B₀, hB₀sq⟩

  have hB₀_ne : B₀ ≠ 0 := by
    intro hB₀_zero
    apply hden_ne
    simpa [hB₀_zero] using hB₀sq

  have hB₀_pos : 0 < B₀ := Nat.pos_of_ne_zero hB₀_ne

  -- Since `B₀ ∣ u.den` and `u.num` is coprime to `u.den`, it is also
  -- coprime to `B₀`.
  have hB₀_dvd_den : B₀ ∣ u.den := by
    rw [hB₀sq]
    exact dvd_mul_right B₀ B₀

  have hcop_nat : Nat.Coprime u.num.natAbs B₀ :=
    Nat.Coprime.of_dvd_right hB₀_dvd_den u.reduced

  have hcop_int : Int.gcd u.num (B₀ : ℤ) = 1 := by
    simpa [Int.gcd, Int.natAbs_natCast] using
      (Nat.coprime_iff_gcd_eq_one.mp hcop_nat)

  refine ⟨u.num, (B₀ : ℤ), ?_, hcop_int, ?_⟩
  · exact_mod_cast hB₀_pos
  · -- Rewrite `u = u.num/u.den` and `u.den = B₀^2`.
    have hden_eq : u.den = B₀ ^ 2 := by
      simpa [pow_two] using hB₀sq
    calc
      u = (u.num : ℚ) / (u.den : ℚ) := by
        simpa using (Rat.num_div_den u).symm
      _ = (u.num : ℚ) / ((B₀ : ℤ) : ℚ) ^ 2 := by
        rw [hden_eq]
        norm_num [pow_two]

end DM4
```

The important imported Mathlib facts are:

```lean
Rat.isSquare_iff
Rat.num_div_den
Rat.den_ne_zero
Rat.reduced
Nat.Coprime.of_dvd_right
```

If you want the final file to have only one `sorry`, replace `curve_rhs_den_eq_den_cube` by your denominator computation from step (1), and keep only `nat_isSquare_of_isSquare_cube` as the allowed `sorry`.
