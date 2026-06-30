# Q2628 `primitiveCentered_N_even`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

Paste this near `primitiveCentered_N_even`, before any later-only use of `n12_eight_dvd_sq_sub_sq_of_odd`.  The helper name below is fresh, so it will not collide with the existing later helper.  It uses the exact integer divisibility cancellation API `mul_left_inj'` on the nonzero integer `4`.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

private theorem q2628_eight_dvd_sq_sub_sq_of_odd {a b : ℤ}
    (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases ha with ⟨r, rfl⟩
  rcases hb with ⟨s, rfl⟩
  have hr : (2 : ℤ) ∣ r ^ 2 + r := by
    convert Int.two_dvd_mul_add_one r using 1
    ring
  have hs : (2 : ℤ) ∣ s ^ 2 + s := by
    convert Int.two_dvd_mul_add_one s using 1
    ring
  rcases hr with ⟨u, hu⟩
  rcases hs with ⟨v, hv⟩
  refine ⟨u - v, ?_⟩
  calc
    (2 * r + 1) ^ 2 - (2 * s + 1) ^ 2
        = 4 * (r ^ 2 + r) - 4 * (s ^ 2 + s) := by ring
    _ = 8 * (u - v) := by
      rw [hu, hv]
      ring

theorem primitiveCentered_N_even (S : PrimitiveCenteredFourSqAP) : Even S.N := by
  have hpOdd : Odd S.p := Int.odd_iff.mpr S.hp_odd
  have hqOdd : Odd S.q := Int.odd_iff.mpr S.hq_odd
  have h8gap : (8 : ℤ) ∣ S.q ^ 2 - S.p ^ 2 :=
    q2628_eight_dvd_sq_sub_sq_of_odd hqOdd hpOdd
  have h8N : (8 : ℤ) ∣ 4 * S.N := by
    rw [← primitiveCentered_gap_pq S]
    exact h8gap
  rcases h8N with ⟨k, hk⟩
  have hN : S.N = 2 * k := by
    apply (mul_left_inj' (show (4 : ℤ) ≠ 0 by norm_num)).mp
    calc
      (4 : ℤ) * S.N = 8 * k := hk
      _ = 4 * (2 * k) := by ring
  rw [hN]
  exact even_two_mul k
```

If you move the existing helper `n12_eight_dvd_sq_sub_sq_of_odd` above this theorem instead of copying the fresh helper, the body can be shortened to:

```lean
theorem primitiveCentered_N_even (S : PrimitiveCenteredFourSqAP) : Even S.N := by
  have hpOdd : Odd S.p := Int.odd_iff.mpr S.hp_odd
  have hqOdd : Odd S.q := Int.odd_iff.mpr S.hq_odd
  have h8gap : (8 : ℤ) ∣ S.q ^ 2 - S.p ^ 2 :=
    n12_eight_dvd_sq_sub_sq_of_odd hqOdd hpOdd
  have h8N : (8 : ℤ) ∣ 4 * S.N := by
    rw [← primitiveCentered_gap_pq S]
    exact h8gap
  rcases h8N with ⟨k, hk⟩
  have hN : S.N = 2 * k := by
    apply (mul_left_inj' (show (4 : ℤ) ≠ 0 by norm_num)).mp
    calc
      (4 : ℤ) * S.N = 8 * k := hk
      _ = 4 * (2 * k) := by ring
  rw [hN]
  exact even_two_mul k
```

The key cancellation step is:

```lean
apply (mul_left_inj' (show (4 : ℤ) ≠ 0 by norm_num)).mp
```

It turns the goal `S.N = 2*k` into `4*S.N = 4*(2*k)`, which is exactly the divisibility witness equation `hk : 4*S.N = 8*k` after `ring` normalizes `8*k` to `4*(2*k)`.
