# Q2297: `QuarticB` wrapper via existing helpers

```lean
-- Paste this below the listed helpers in
-- FLT/Assumptions/MazurProof/RationalPointsN12.lean,
-- inside `namespace MazurProof.RationalPointsN12`.

lemma odd_odd_split_as_sum_diff {u v : ℤ}
    (hu : Odd u) (hv : Odd v) :
    ∃ R S : ℤ, u = R + S ∧ v = R - S ∧ Odd (R + S) := by
  rcases hu with ⟨U, hU⟩
  rcases hv with ⟨V, hV⟩
  refine ⟨U + V + 1, U - V, ?_, ?_, ?_⟩
  · rw [hU]
    ring
  · rw [hV]
    ring
  · exact ⟨U, by ring⟩

lemma split_mul_ne_zero_of_sq_ne {u v R S : ℤ}
    (hu : u = R + S)
    (hv : v = R - S)
    (hsqne : u ^ 2 ≠ v ^ 2) :
    R * S ≠ 0 := by
  intro hRS
  apply hsqne
  rcases mul_eq_zero.mp hRS with hR | hS
  · calc
      u ^ 2 = (R + S) ^ 2 := by rw [hu]
      _ = (R - S) ^ 2 := by rw [hR]; ring
      _ = v ^ 2 := by rw [hv]
  · calc
      u ^ 2 = (R + S) ^ 2 := by rw [hu]
      _ = (R - S) ^ 2 := by rw [hS]; ring
      _ = v ^ 2 := by rw [hv]

lemma int_gcd_of_coprime_sum_diff {u v R S : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : u = R + S)
    (hv : v = R - S) :
    Int.gcd R S = 1 := by
  have hgcd_uv : Int.gcd (R + S) (R - S) = 1 := by
    simpa [hu, hv] using hcop
  have hbez : ∃ x y : ℤ, (1 : ℤ) = (R + S) * x + (R - S) * y := by
    exact (Int.gcd_dvd_iff (a := R + S) (b := R - S) (n := 1)).mp
      (by simpa [hgcd_uv])
  have hEqInt : (1 : ℤ) = (Int.gcd R S : ℤ) := by
    refine Int.gcd_greatest (a := R) (b := S) (d := 1) ?_ ?_ ?_ ?_
    · norm_num
    · simp
    · simp
    · intro e heR heS
      rcases hbez with ⟨x, y, hxy⟩
      have he_sum : e ∣ R + S := dvd_add heR heS
      have he_diff : e ∣ R - S := dvd_sub heR heS
      rw [hxy]
      exact dvd_add
        (dvd_mul_of_dvd_left he_sum x)
        (dvd_mul_of_dvd_left he_diff y)
  exact Int.ofNat_inj.mp hEqInt.symm

-- This is the requested final wrapper, but with the necessary extra
-- non-degeneracy hypothesis `hsqne : u ^ 2 ≠ v ^ 2`.
theorem quartic_B_to_pythagoreanQuarticRhs
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u) (hv : Odd v)
    (huv0 : u * v ≠ 0)
    (hne : 3 * u ^ 2 - v ^ 2 ≠ 0)
    (hsqne : u ^ 2 ≠ v ^ 2)
    (hB : QuarticB u v Z) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧ Int.gcd m n = 1 ∧ Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  rcases quarticB_twist_factor_halves_odd hu hv with ⟨A, hA, hAOdd⟩
  rcases quarticB_sum_factor_halves_odd hu hv with ⟨B, hBhalf, _hBOdd⟩

  have hZsq_four : Z ^ 2 = 4 * (A * B) := by
    calc
      Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) := by
        simpa [QuarticB] using hB
      _ = (2 * A) * (2 * B) := by rw [hA, hBhalf]
      _ = 4 * (A * B) := by ring

  have hZeven : Even Z := even_of_sq_eq_four_mul hZsq_four
  rcases hZeven with ⟨c, hZc⟩

  have hABsq : A * B = c ^ 2 := by
    have h4 : 4 * (A * B) = 4 * c ^ 2 := by
      calc
        4 * (A * B) = Z ^ 2 := by rw [hZsq_four]
        _ = (2 * c) ^ 2 := by
          rw [hZc]
          ring
        _ = 4 * c ^ 2 := by ring
    nlinarith

  have hleft_pos : 0 < 3 * u ^ 2 - v ^ 2 :=
    quarticB_left_factor_pos huv0 hne hB
  have hsum_pos : 0 < u ^ 2 + v ^ 2 :=
    quarticB_sum_sq_pos_of_mul_ne_zero huv0
  have hA_nonneg : 0 ≤ A := by nlinarith [hA, hleft_pos]
  have hB_nonneg : 0 ≤ B := by nlinarith [hBhalf, hsum_pos]

  have hcopAB : Int.gcd A B = 1 :=
    quarticB_half_factors_coprime hcop hAOdd hA hBhalf

  rcases int_coprime_mul_eq_sq_of_nonneg hA_nonneg hB_nonneg hcopAB hABsq
    with ⟨r, s, hr, hs⟩

  have hsplit₁ : 3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 := by
    calc
      3 * u ^ 2 - v ^ 2 = 2 * A := hA
      _ = 2 * r ^ 2 := by rw [hr]
  have hsplit₂ : u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
    calc
      u ^ 2 + v ^ 2 = 2 * B := hBhalf
      _ = 2 * s ^ 2 := by rw [hs]

  rcases odd_odd_split_as_sum_diff hu hv with ⟨R, S, huRS, hvRS, hpar⟩
  have hRS0 : R * S ≠ 0 :=
    split_mul_ne_zero_of_sq_ne huRS hvRS hsqne
  have hcopRS : Int.gcd R S = 1 :=
    int_gcd_of_coprime_sum_diff hcop huRS hvRS

  exact quartic_B_split_halves_to_pythagoreanQuarticRhs
    hsplit₁ hsplit₂ huRS hvRS hRS0 hcopRS hpar
```

## Why the extra `u ^ 2 ≠ v ^ 2` hypothesis is needed

Step 5 cannot produce `R * S ≠ 0` from the originally stated assumptions. If `u = R + S` and `v = R - S`, then `R = 0` gives `u = -v`, and `S = 0` gives `u = v`; both are exactly the degeneracies covered by `u ^ 2 = v ^ 2`.

A concrete Lean-checkable obstruction is `u = v = 1`, `Z = 2`:

```lean
example :
    Int.gcd (1 : ℤ) 1 = 1 ∧
    Odd (1 : ℤ) ∧ Odd (1 : ℤ) ∧
    (1 : ℤ) * 1 ≠ 0 ∧
    3 * (1 : ℤ) ^ 2 - 1 ^ 2 ≠ 0 ∧
    QuarticB 1 1 2 := by
  norm_num [QuarticB]

example {R S : ℤ}
    (hu : (1 : ℤ) = R + S)
    (hv : (1 : ℤ) = R - S) :
    R * S = 0 := by
  have hS : S = 0 := by nlinarith
  simp [hS]
```

So the existing helper

```lean
quartic_B_split_halves_to_pythagoreanQuarticRhs
```

requires either the strengthened wrapper above, or a separate proof branch for the degenerate cases `u = v` and `u = -v` that does not go through `R * S ≠ 0`.

## Notes on the proof

The `R,S` split is division-free: if `u = 2U + 1` and `v = 2V + 1`, take

```lean
R = U + V + 1
S = U - V
```

Then `R + S = u` and `R - S = v` by `ring`, and `Odd (R + S)` is witnessed by `U`.

The gcd lemma uses Bezout from `Int.gcd_dvd_iff`: since `Int.gcd (R + S) (R - S) = 1`, any common divisor of `R` and `S` divides both `R + S` and `R - S`, hence divides `1`; `Int.gcd_greatest` then gives `Int.gcd R S = 1`.
