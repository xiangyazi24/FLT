# Q1424 (dm1/dm3): parity in the quartic equation

I cannot honestly give a complete proof of the full theorem using only the proposed ZMod argument.

The ZMod facts prove these three branches:

1. `r` even, `B` odd: contradiction modulo `4` because `s^2 = 3` in `ZMod 4`.
2. `r` even, `B` even: contradiction from `2 ∣ gcd(r,B)`.
3. `r` odd, `B % 4 = 2`: contradiction modulo `16` because `s^2 = 5` in `ZMod 16`.

The remaining branch is:

```text
r % 2 = 1,  B % 2 = 0,  B % 4 = 0.
```

For this branch, the RHS is congruent to `1` modulo `16`, and in fact it remains compatible with 2-adic square residues. So the missing step is not a one-line `ZMod 16` contradiction. It needs a different global/descent argument.

Below is the Lean code for the modular exclusions, plus a corrected theorem that proves `r%2=1 ∧ B%2=1` under the extra hypothesis `¬ 4 ∣ B`.  This is the strongest result delivered by the stated ZMod route alone.

```lean
import Mathlib

namespace DM3

/-- The quartic equation in the parity lemma. -/
def QuarticPlusEq (r B s : ℤ) : Prop :=
  s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

lemma zmod4_sq_ne_three (z : ZMod 4) : z * z ≠ (3 : ZMod 4) := by
  change Fin 4 at z
  fin_cases z <;> decide

lemma zmod4_pow_two_ne_three (z : ZMod 4) : z ^ 2 ≠ (3 : ZMod 4) := by
  rw [pow_two]
  exact zmod4_sq_ne_three z

lemma zmod16_sq_ne_five (z : ZMod 16) : z * z ≠ (5 : ZMod 16) := by
  change Fin 16 at z
  fin_cases z <;> decide

lemma zmod16_pow_two_ne_five (z : ZMod 16) : z ^ 2 ≠ (5 : ZMod 16) := by
  rw [pow_two]
  exact zmod16_sq_ne_five z

lemma odd_of_emod_two_eq_one {z : ℤ} (hz : z % 2 = 1) : Odd z := by
  rw [Int.odd_iff]
  exact hz

lemma zmod4_pow_two_of_even {z : ℤ} (hz : z % 2 = 0) :
    (z : ZMod 4) ^ 2 = 0 := by
  rcases Int.dvd_of_emod_eq_zero hz with ⟨k, rfl⟩
  change (((2 : ZMod 4) * (k : ZMod 4)) ^ 2) = 0
  ring_nf

lemma zmod4_pow_two_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 4) ^ 2 = 1 := by
  rcases odd_of_emod_two_eq_one hz with ⟨k, rfl⟩
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

lemma zmod16_pow_two_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 16) ^ 2 = 1 ∨ (z : ZMod 16) ^ 2 = 9 := by
  -- Finite check: odd residues modulo 16 are `1,3,5,7,9,11,13,15`;
  -- their squares are `1` or `9`.
  have hzmod : z % 16 = 0 ∨ z % 16 = 1 ∨ z % 16 = 2 ∨ z % 16 = 3 ∨
      z % 16 = 4 ∨ z % 16 = 5 ∨ z % 16 = 6 ∨ z % 16 = 7 ∨
      z % 16 = 8 ∨ z % 16 = 9 ∨ z % 16 = 10 ∨ z % 16 = 11 ∨
      z % 16 = 12 ∨ z % 16 = 13 ∨ z % 16 = 14 ∨ z % 16 = 15 := by omega
  rcases hzmod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  all_goals
    try omega
    first
    | left; apply ZMod.intCast_eq_intCast_iff.mpr; omega
    | right; apply ZMod.intCast_eq_intCast_iff.mpr; omega

lemma zmod16_pow_four_of_odd {z : ℤ} (hz : z % 2 = 1) :
    (z : ZMod 16) ^ 4 = 1 := by
  rcases zmod16_pow_two_of_odd hz with h | h
  · calc
      (z : ZMod 16) ^ 4 = ((z : ZMod 16) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h]; norm_num
  · calc
      (z : ZMod 16) ^ 4 = ((z : ZMod 16) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h]; norm_num

lemma zmod16_pow_two_of_emod_four_eq_two {z : ℤ} (hz : z % 4 = 2) :
    (z : ZMod 16) ^ 2 = 4 := by
  have hzmod : z % 16 = 2 ∨ z % 16 = 6 ∨ z % 16 = 10 ∨ z % 16 = 14 := by omega
  rcases hzmod with h2 | h6 | h10 | h14
  all_goals
    apply ZMod.intCast_eq_intCast_iff.mpr
    omega

lemma zmod16_pow_four_of_emod_four_eq_two {z : ℤ} (hz : z % 4 = 2) :
    (z : ZMod 16) ^ 4 = 0 := by
  calc
    (z : ZMod 16) ^ 4 = ((z : ZMod 16) ^ 2) ^ 2 := by ring
    _ = 0 := by rw [zmod16_pow_two_of_emod_four_eq_two hz]; norm_num

lemma quartic_eq_zmod4 {r B s : ℤ} (h : QuarticPlusEq r B s) :
    (s : ZMod 4) ^ 2 =
      (r : ZMod 4) ^ 4 + (r : ZMod 4) ^ 2 * (B : ZMod 4) ^ 2 -
        (B : ZMod 4) ^ 4 := by
  dsimp [QuarticPlusEq] at h
  exact_mod_cast h

lemma quartic_eq_zmod16 {r B s : ℤ} (h : QuarticPlusEq r B s) :
    (s : ZMod 16) ^ 2 =
      (r : ZMod 16) ^ 4 + (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 -
        (B : ZMod 16) ^ 4 := by
  dsimp [QuarticPlusEq] at h
  exact_mod_cast h

/-- Branch 1: `r` even and `B` odd is impossible modulo `4`. -/
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

/-- Branch 2: both even contradict `gcd(r,B)=1`. -/
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

/-- Branch 3: `r` odd and `B ≡ 2 mod 4` is impossible modulo `16`. -/
lemma quartic_plus_no_r_odd_B_two_mod_four
    {r B s : ℤ}
    (hr_odd : r % 2 = 1)
    (hB_two : B % 4 = 2)
    (h : QuarticPlusEq r B s) :
    False := by
  have h16 := quartic_eq_zmod16 h
  have hr4 : (r : ZMod 16) ^ 4 = 1 := zmod16_pow_four_of_odd hr_odd
  have hB2 : (B : ZMod 16) ^ 2 = 4 := zmod16_pow_two_of_emod_four_eq_two hB_two
  have hB4 : (B : ZMod 16) ^ 4 = 0 := zmod16_pow_four_of_emod_four_eq_two hB_two
  have hs5 : (s : ZMod 16) ^ 2 = 5 := by
    calc
      (s : ZMod 16) ^ 2 =
          (r : ZMod 16) ^ 4 + (r : ZMod 16) ^ 2 * (B : ZMod 16) ^ 2 -
            (B : ZMod 16) ^ 4 := h16
      _ = 5 := by
        rcases zmod16_pow_two_of_odd hr_odd with hr2 | hr2
        · rw [hr4, hr2, hB2, hB4]; norm_num
        · rw [hr4, hr2, hB2, hB4]; norm_num
  exact zmod16_pow_two_ne_five (s : ZMod 16) hs5

/-- Corrected theorem delivered by the ZMod argument alone.

The extra hypothesis `¬ 4 ∣ B` removes the remaining branch `r` odd and `4 ∣ B`.
-/
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
The originally requested theorem is blocked at the branch:

  r % 2 = 1, B % 2 = 0, B % 4 = 0.

Modulo `16`, this branch gives RHS ≡ 1, so it is not contradictory.
A correct full proof needs an additional non-local lemma, for example:

lemma quartic_plus_no_r_odd_four_dvd_B
    {r B s : ℤ}
    (h : QuarticPlusEq r B s)
    (hcop : Int.gcd r B = 1)
    (hrpos : 0 < r)
    (hBpos : 0 < B)
    (hr_odd : r % 2 = 1)
    (hB_four : (4 : ℤ) ∣ B) : False := by
  -- Not a ZMod 4/8/16 contradiction; use descent or a sharper global argument.
  sorry

Then the full theorem is immediate by the same case split.
-/

end DM3
```

## Bottom line

A theorem named exactly

```lean
quartic_plus_both_odd
```

cannot be proved from the ZMod checks listed in the prompt, because the branch `r` odd and `4 ∣ B` survives every one of those checks.  The file above gives the strongest clean modular result and isolates the missing lemma needed for the full statement.
