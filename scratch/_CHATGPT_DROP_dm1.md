# Q1413 (dm1/dm2): parity of `r,B` in the quartic equation

I do **not** think the requested ZMod proof of the full statement is valid as written.

The gap is the branch

```text
r odd, B even.
```

From `B` even one can write `B = 2*k`, but one **cannot** conclude `k` is odd.  The proposed `ZMod 8`/`ZMod 16` contradiction only excludes the subcase `B % 4 = 2`, i.e. `B = 2*k` with `k` odd.  It does not exclude `4 ∣ B`.  For example, if `r` is odd and `4 ∣ B`, then the right-hand side is congruent to `1` modulo `16`, which is compatible with an odd square.

So the honest Lean deliverable is:

1. the `ZMod 4` contradiction for `r` even, `B` odd;
2. the gcd contradiction for both even;
3. the `ZMod 8` contradiction for `r` odd, `B % 4 = 2`;
4. the corrected theorem: if the missing branch `4 ∣ B` is ruled out, then `r % 2 = 1 ∧ B % 2 = 1`.

The full requested theorem still needs an additional argument excluding `r` odd and `4 ∣ B`; it is not discharged by the proposed modular proof.

```lean
import Mathlib

namespace DM2

/-- The quartic equation used in the descent. -/
def QuarticPlusEq (r B s : ℤ) : Prop :=
  s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

lemma zmod4_sq_ne_three (z : ZMod 4) : z * z ≠ (3 : ZMod 4) := by
  change Fin 4 at z
  fin_cases z <;> decide

lemma zmod4_pow_two_ne_three (z : ZMod 4) : z ^ 2 ≠ (3 : ZMod 4) := by
  rw [pow_two]
  exact zmod4_sq_ne_three z

lemma zmod8_sq_ne_five (z : ZMod 8) : z * z ≠ (5 : ZMod 8) := by
  change Fin 8 at z
  fin_cases z <;> decide

lemma zmod8_pow_two_ne_five (z : ZMod 8) : z ^ 2 ≠ (5 : ZMod 8) := by
  rw [pow_two]
  exact zmod8_sq_ne_five z

lemma odd_of_emod_two_eq_one {z : ℤ} (hz : z % 2 = 1) : Odd z := by
  obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hz)
  rw [sub_eq_iff_eq_add] at hk
  exact ⟨k, by simpa [mul_comm] using hk⟩

lemma zmod4_pow_two_of_even {z : ℤ} (hz : z % 2 = 0) :
    (z : ZMod 4) ^ 2 = 0 := by
  rcases Int.dvd_of_emod_eq_zero hz with ⟨k, hk⟩
  rw [hk]
  change (((2 : ZMod 4) * (k : ZMod 4)) ^ 2) = 0
  ring_nf

lemma zmod4_pow_two_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 4) ^ 2 = 1 := by
  rcases odd_of_emod_two_eq_one hz with ⟨k, hk⟩
  rw [hk]
  change (((2 : ZMod 4) * (k : ZMod 4) + 1) ^ 2) = 1
  ring_nf

lemma zmod4_pow_four_of_even {z : ℤ} (hz : z % 2 = 0) :
    (z : ZMod 4) ^ 4 = 0 := by
  calc
    (z : ZMod 4) ^ 4 = ((z : ZMod 4) ^ 2) ^ 2 := by ring
    _ = 0 := by rw [zmod4_pow_two_of_even hz]; norm_num

lemma zmod4_pow_four_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 4) ^ 4 = 1 := by
  calc
    (z : ZMod 4) ^ 4 = ((z : ZMod 4) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [zmod4_pow_two_of_odd hz]; norm_num

lemma zmod8_pow_two_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 8) ^ 2 = 1 := by
  rcases odd_of_emod_two_eq_one hz with ⟨k, hk⟩
  rw [hk]
  change (((2 : ZMod 8) * (k : ZMod 8) + 1) ^ 2) = 1
  ring_nf

lemma zmod8_pow_four_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 8) ^ 4 = 1 := by
  calc
    (z : ZMod 8) ^ 4 = ((z : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [zmod8_pow_two_of_odd hz]; norm_num

lemma zmod8_pow_two_of_emod_four_eq_two {z : ℤ} (hz : z % 4 = 2) :
    (z : ZMod 8) ^ 2 = 4 := by
  obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hz)
  rw [sub_eq_iff_eq_add] at hk
  rw [hk]
  change (((k : ZMod 8) * 4 + 2) ^ 2) = 4
  ring_nf

lemma zmod8_pow_four_of_emod_four_eq_two {z : ℤ} (hz : z % 4 = 2) :
    (z : ZMod 8) ^ 4 = 0 := by
  calc
    (z : ZMod 8) ^ 4 = ((z : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 0 := by rw [zmod8_pow_two_of_emod_four_eq_two hz]; norm_num

lemma quartic_eq_zmod4 {r B s : ℤ} (h : QuarticPlusEq r B s) :
    (s : ZMod 4) ^ 2 =
      (r : ZMod 4) ^ 4 + (r : ZMod 4) ^ 2 * (B : ZMod 4) ^ 2 -
        (B : ZMod 4) ^ 4 := by
  dsimp [QuarticPlusEq] at h
  exact_mod_cast h

lemma quartic_eq_zmod8 {r B s : ℤ} (h : QuarticPlusEq r B s) :
    (s : ZMod 8) ^ 2 =
      (r : ZMod 8) ^ 4 + (r : ZMod 8) ^ 2 * (B : ZMod 8) ^ 2 -
        (B : ZMod 8) ^ 4 := by
  dsimp [QuarticPlusEq] at h
  exact_mod_cast h

/-- If `r` is even and `B` is odd, the equation gives `s^2 = 3` in `ZMod 4`,
impossible because the squares modulo `4` are only `0,1`. -/
lemma quartic_plus_no_r_even_B_odd
    {r B s : ℤ}
    (hr_even : r % 2 = 0)
    (hB_odd : B % 2 = 1)
    (h : QuarticPlusEq r B s) :
    False := by
  have h4 := quartic_eq_zmod4 h
  have hr2 : (r : ZMod 4) ^ 2 = 0 := zmod4_pow_two_of_even hr_even
  have hr4 : (r : ZMod 4) ^ 4 = 0 := zmod4_pow_four_of_even hr_even
  have hB2 : (B : ZMod 4) ^ 2 = 1 := zmod4_pow_two_of_odd hB_odd
  have hB4 : (B : ZMod 4) ^ 4 = 1 := zmod4_pow_four_of_odd hB_odd
  have hs3 : (s : ZMod 4) ^ 2 = 3 := by
    calc
      (s : ZMod 4) ^ 2 =
          (r : ZMod 4) ^ 4 + (r : ZMod 4) ^ 2 * (B : ZMod 4) ^ 2 -
            (B : ZMod 4) ^ 4 := h4
      _ = 3 := by rw [hr4, hr2, hB2, hB4]; norm_num
  exact zmod4_pow_two_ne_three (s : ZMod 4) hs3

/-- Both even contradict `gcd(r,B)=1`. -/
lemma not_both_even_of_gcd_one
    {r B : ℤ}
    (hcop : Int.gcd r B = 1)
    (hr_even : r % 2 = 0)
    (hB_even : B % 2 = 0) :
    False := by
  have h2r : (2 : ℤ) ∣ r := Int.dvd_of_emod_eq_zero hr_even
  have h2B : (2 : ℤ) ∣ B := Int.dvd_of_emod_eq_zero hB_even
  have h2g : (2 : ℤ) ∣ (Int.gcd r B : ℤ) := Int.dvd_coe_gcd h2r h2B
  rw [hcop] at h2g
  norm_num at h2g

/-- If `r` is odd and `B % 4 = 2`, the equation gives `s^2 = 5` in `ZMod 8`,
impossible because the squares modulo `8` are only `0,1,4`. -/
lemma quartic_plus_no_r_odd_B_two_mod_four
    {r B s : ℤ}
    (hr_odd : r % 2 = 1)
    (hB_two : B % 4 = 2)
    (h : QuarticPlusEq r B s) :
    False := by
  have h8 := quartic_eq_zmod8 h
  have hr2 : (r : ZMod 8) ^ 2 = 1 := zmod8_pow_two_of_odd hr_odd
  have hr4 : (r : ZMod 8) ^ 4 = 1 := zmod8_pow_four_of_odd hr_odd
  have hB2 : (B : ZMod 8) ^ 2 = 4 := zmod8_pow_two_of_emod_four_eq_two hB_two
  have hB4 : (B : ZMod 8) ^ 4 = 0 := zmod8_pow_four_of_emod_four_eq_two hB_two
  have hs5 : (s : ZMod 8) ^ 2 = 5 := by
    calc
      (s : ZMod 8) ^ 2 =
          (r : ZMod 8) ^ 4 + (r : ZMod 8) ^ 2 * (B : ZMod 8) ^ 2 -
            (B : ZMod 8) ^ 4 := h8
      _ = 5 := by rw [hr4, hr2, hB2, hB4]; norm_num
  exact zmod8_pow_two_ne_five (s : ZMod 8) hs5

/-- The corrected theorem obtained from exactly the modular facts above.

The extra hypothesis `¬ 4 ∣ B` is precisely the missing branch in the proposed proof. -/
theorem quartic_plus_both_odd_of_not_four_dvd_B
    {r B s : ℤ}
    (h : QuarticPlusEq r B s)
    (hcop : Int.gcd r B = 1)
    (hB_not_four : ¬ (4 : ℤ) ∣ B) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one r with hr_even | hr_odd
  · rcases Int.emod_two_eq_zero_or_one B with hB_even | hB_odd
    · exact False.elim (not_both_even_of_gcd_one hcop hr_even hB_even)
    · exact False.elim (quartic_plus_no_r_even_B_odd hr_even hB_odd h)
  · rcases Int.emod_two_eq_zero_or_one B with hB_even | hB_odd
    · have hB_mod4 : B % 4 = 0 ∨ B % 4 = 2 := by omega
      rcases hB_mod4 with hB0 | hB2
      · exact False.elim (hB_not_four (Int.dvd_of_emod_eq_zero hB0))
      · exact False.elim (quartic_plus_no_r_odd_B_two_mod_four hr_odd hB2 h)
    · exact ⟨hr_odd, hB_odd⟩

/-
This is the originally requested theorem.  The attempted ZMod proof does not close
without an additional argument excluding the branch `r % 2 = 1` and `4 ∣ B`.

Do not add this theorem with a fake proof:

theorem quartic_plus_both_odd
    {r B s : ℤ}
    (h : QuarticPlusEq r B s)
    (hcop : Int.gcd r B = 1)
    (hrpos : 0 < r)
    (hBpos : 0 < B) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  -- blocked at: `r % 2 = 1`, `B % 2 = 0`, `B % 4 = 0`
  -- the supplied `B = 2*k, k odd` step is not justified.
  sorry
-/

end DM2
```

## How to use this downstream

If you can prove or already have `¬ (4 : ℤ) ∣ B`, then use:

```lean
DM2.quartic_plus_both_odd_of_not_four_dvd_B
```

If the goal is the original theorem with only positivity and coprimality, one more lemma is needed:

```lean
lemma quartic_plus_no_r_odd_four_dvd_B
    {r B s : ℤ}
    (h : DM2.QuarticPlusEq r B s)
    (hcop : Int.gcd r B = 1)
    (hr_odd : r % 2 = 1)
    (hB_four : (4 : ℤ) ∣ B) : False := by
  -- not a ZMod-4/8/16 one-line contradiction; needs an additional argument
  sorry
```

Once that lemma exists, the original `quartic_plus_both_odd` is a short case split using the three exclusions above.
