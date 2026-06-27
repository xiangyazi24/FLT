# Q1372 (dm1/dm4): `rat_denom_square` for `w^2 = u^3+u^2-u`

The square-denominator bridge after the denominator computation is short.  The exact hard step is the `Rat.den` normalization

```lean
(u ^ 3 + u ^ 2 - u).den = u.den ^ 3
```

which is not a one-line `ring`/`field_simp` result: it requires proving the numerator

```lean
u.num * (u.num ^ 2 + u.num * (u.den : ℤ)^2 - (u.den : ℤ)^4)
```

is coprime to `u.den^3`.  That is precisely where `u.reduced` and `den_div_eq_of_coprime` enter.

Below is compilable Lean structure with the denominator lemma isolated as the exact remaining proof obligation.  The rest is the complete bridge.

```lean
import Mathlib

namespace DM4

/-- If `n^3` is a square and `n ≠ 0`, then `n` is a square. -/
theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases (isSquare_iff_exists_sq (n ^ 3)).1 h with ⟨c, hc⟩

  have hndvd : n ^ 2 ∣ c ^ 2 := by
    rw [← hc]
    exact ⟨n, by ring⟩

  have hceil : Nat.ceilRoot 2 (n ^ 2) = n := by
    simpa using
      (Nat.ceilRoot_pow_self (n := 2) (a := n)
        (by norm_num : (2 : ℕ) ≠ 0))

  have hn_dvd_c : n ∣ c := by
    have hraw : Nat.ceilRoot 2 (n ^ 2) ∣ c :=
      ((Nat.dvd_pow_iff_ceilRoot_dvd
        (a := n ^ 2) (b := c) (n := 2)
        (by norm_num : (2 : ℕ) ≠ 0)).1 hndvd)
    simpa [hceil] using hraw

  rcases hn_dvd_c with ⟨d, rfl⟩

  refine (isSquare_iff_exists_sq n).2 ⟨d, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pos_of_ne_zero hn) 2)
  calc
    n ^ 2 * n = n ^ 3 := by ring
    _ = (n * d) ^ 2 := hc
    _ = n ^ 2 * d ^ 2 := by ring

/--
Exact denominator computation needed for the curve.

Proof route:
1. Rewrite `u = u.num / u.den` using `Rat.num_div_den`.
2. Show
   `u^3+u^2-u = N /. (u.den : ℤ)^3`, where
   `N = u.num * (u.num^2 + u.num*(u.den:ℤ)^2 - (u.den:ℤ)^4)`.
3. Prove `Int.gcd N ((u.den : ℤ)^3) = 1` from `u.reduced`.
4. Apply `den_div_eq_of_coprime`.
-/
lemma curve_rhs_den_eq_den_cube (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  -- This is the exact remaining `Rat.den`/gcd normalization.
  -- The low-level API is `den_div_eq_of_coprime`; the needed coprimality
  -- is the polynomial-gcd fact described above.
  sorry

/--
If `(u,w)` lies on `w^2 = u^3+u^2-u`, then `u` has square denominator:
`u = A / B^2` with `A,B : ℤ`, `0 < B`, and `gcd(A,B)=1`.
-/
theorem rat_denom_square
    {u w : ℚ}
    (hcurve : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ A B : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
        u = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq_rhs : IsSquare (u ^ 3 + u ^ 2 - u) := by
    refine ⟨w, ?_⟩
    rw [← hcurve]
    ring

  have hden_sq : IsSquare ((u ^ 3 + u ^ 2 - u).den) :=
    (Rat.isSquare_iff.mp hsq_rhs).2

  have hden_cube_sq : IsSquare (u.den ^ 3) := by
    simpa [curve_rhs_den_eq_den_cube u] using hden_sq

  have hden_ne : u.den ≠ 0 := u.den_ne_zero
  have hden_isSquare : IsSquare u.den :=
    nat_isSquare_of_isSquare_cube hden_ne hden_cube_sq

  rcases hden_isSquare with ⟨B₀, hB₀sq⟩

  have hB₀_ne : B₀ ≠ 0 := by
    intro hB₀_zero
    apply hden_ne
    simpa [hB₀_zero] using hB₀sq

  have hB₀_pos : 0 < B₀ := Nat.pos_of_ne_zero hB₀_ne

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
  · have hden_eq : u.den = B₀ ^ 2 := by
      simpa [pow_two] using hB₀sq
    calc
      u = (u.num : ℚ) / (u.den : ℚ) := by
        simpa using (Rat.num_div_den u).symm
      _ = (u.num : ℚ) / ((B₀ : ℤ) : ℚ) ^ 2 := by
        rw [hden_eq]
        simp [pow_two]

end DM4
```

The exact theorem to prove next, if you want this file to have no `sorry`, is:

```lean
lemma curve_rhs_den_eq_den_cube (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3
```

and its exact inner gcd target is:

```lean
Nat.Coprime
  (u.num * (u.num ^ 2 + u.num * (u.den : ℤ)^2 - (u.den : ℤ)^4)).natAbs
  (u.den ^ 3)
```
