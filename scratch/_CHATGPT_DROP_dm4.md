# Q1494 (dm4): complete Lean proofs for the parity/modular lemmas

Below is a self-contained Mathlib proof.  I used explicit `ZMod 4` and `ZMod 8` helper lemmas, plus `omega` only to derive the possible integer remainders.

The two key contradiction facts are:

* no square in `ZMod 4` is `3`;
* no square in `ZMod 8` is `5`.

```lean
import Mathlib

private lemma int_mod_two_cases (x : ℤ) :
    x % 2 = 0 ∨ x % 2 = 1 := by
  have hnonneg : 0 ≤ x % (2 : ℤ) :=
    Int.emod_nonneg x (by norm_num : (2 : ℤ) ≠ 0)
  have hlt : x % (2 : ℤ) < 2 :=
    Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
  omega

private lemma zmod4_sq_zero_of_even {x : ℤ} (hx : x % 2 = 0) :
    (x : ZMod 4) ^ 2 = 0 := by
  have hx4 : x % 4 = 0 ∨ x % 4 = 2 := by
    have hnonneg : 0 ≤ x % (4 : ℤ) :=
      Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
    have hlt : x % (4 : ℤ) < 4 :=
      Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 4)
    omega
  rcases hx4 with hx4 | hx4
  · have hxz : (x : ZMod 4) = 0 := by
      exact (ZMod.intCast_eq_intCast_iff' x (0 : ℤ) 4).2 (by
        rw [hx4]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 4) = 2 := by
      exact (ZMod.intCast_eq_intCast_iff' x (2 : ℤ) 4).2 (by
        rw [hx4]
        norm_num)
    rw [hxz]
    norm_num

private lemma zmod4_pow4_zero_of_even {x : ℤ} (hx : x % 2 = 0) :
    (x : ZMod 4) ^ 4 = 0 := by
  have hsq := zmod4_sq_zero_of_even hx
  calc
    (x : ZMod 4) ^ 4 = ((x : ZMod 4) ^ 2) ^ 2 := by ring
    _ = 0 := by
      rw [hsq]
      norm_num

private lemma zmod4_sq_one_of_odd {x : ℤ} (hx : x % 2 = 1) :
    (x : ZMod 4) ^ 2 = 1 := by
  have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by
    have hnonneg : 0 ≤ x % (4 : ℤ) :=
      Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
    have hlt : x % (4 : ℤ) < 4 :=
      Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 4)
    omega
  rcases hx4 with hx4 | hx4
  · have hxz : (x : ZMod 4) = 1 := by
      exact (ZMod.intCast_eq_intCast_iff' x (1 : ℤ) 4).2 (by
        rw [hx4]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 4) = 3 := by
      exact (ZMod.intCast_eq_intCast_iff' x (3 : ℤ) 4).2 (by
        rw [hx4]
        norm_num)
    rw [hxz]
    norm_num

private lemma zmod4_pow4_one_of_odd {x : ℤ} (hx : x % 2 = 1) :
    (x : ZMod 4) ^ 4 = 1 := by
  have hsq := zmod4_sq_one_of_odd hx
  calc
    (x : ZMod 4) ^ 4 = ((x : ZMod 4) ^ 2) ^ 2 := by ring
    _ = 1 := by
      rw [hsq]
      norm_num

private lemma zmod4_sq_ne_three (x : ZMod 4) :
    x ^ 2 ≠ (3 : ZMod 4) := by
  fin_cases x <;> decide

private lemma zmod8_sq_ne_five (x : ZMod 8) :
    x ^ 2 ≠ (5 : ZMod 8) := by
  fin_cases x <;> decide

private lemma zmod8_sq_one_of_odd {x : ℤ} (hx : x % 2 = 1) :
    (x : ZMod 8) ^ 2 = 1 := by
  have hx8 :
      x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
    have hnonneg : 0 ≤ x % (8 : ℤ) :=
      Int.emod_nonneg x (by norm_num : (8 : ℤ) ≠ 0)
    have hlt : x % (8 : ℤ) < 8 :=
      Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 8)
    omega
  rcases hx8 with hx8 | hx8 | hx8 | hx8
  · have hxz : (x : ZMod 8) = 1 := by
      exact (ZMod.intCast_eq_intCast_iff' x (1 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 8) = 3 := by
      exact (ZMod.intCast_eq_intCast_iff' x (3 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 8) = 5 := by
      exact (ZMod.intCast_eq_intCast_iff' x (5 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 8) = 7 := by
      exact (ZMod.intCast_eq_intCast_iff' x (7 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num

private lemma zmod8_pow4_one_of_odd {x : ℤ} (hx : x % 2 = 1) :
    (x : ZMod 8) ^ 4 = 1 := by
  have hsq := zmod8_sq_one_of_odd hx
  calc
    (x : ZMod 8) ^ 4 = ((x : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 1 := by
      rw [hsq]
      norm_num

private lemma zmod8_sq_four_of_mod4_two {x : ℤ} (hx : x % 4 = 2) :
    (x : ZMod 8) ^ 2 = 4 := by
  have hx8 : x % 8 = 2 ∨ x % 8 = 6 := by
    have hnonneg : 0 ≤ x % (8 : ℤ) :=
      Int.emod_nonneg x (by norm_num : (8 : ℤ) ≠ 0)
    have hlt : x % (8 : ℤ) < 8 :=
      Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 8)
    omega
  rcases hx8 with hx8 | hx8
  · have hxz : (x : ZMod 8) = 2 := by
      exact (ZMod.intCast_eq_intCast_iff' x (2 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num
  · have hxz : (x : ZMod 8) = 6 := by
      exact (ZMod.intCast_eq_intCast_iff' x (6 : ℤ) 8).2 (by
        rw [hx8]
        norm_num)
    rw [hxz]
    norm_num

private lemma zmod8_pow4_zero_of_mod4_two {x : ℤ} (hx : x % 4 = 2) :
    (x : ZMod 8) ^ 4 = 0 := by
  have hsq := zmod8_sq_four_of_mod4_two hx
  calc
    (x : ZMod 8) ^ 4 = ((x : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 0 := by
      rw [hsq]
      norm_num

private lemma quartic_eq_zmod4 {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (s : ZMod 4) ^ 2 =
      (r : ZMod 4) ^ 4 + (r : ZMod 4) ^ 2 * (B : ZMod 4) ^ 2 -
        (B : ZMod 4) ^ 4 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 4)) heq
  simpa using h

private lemma quartic_eq_zmod8 {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (s : ZMod 8) ^ 2 =
      (r : ZMod 8) ^ 4 + (r : ZMod 8) ^ 2 * (B : ZMod 8) ^ 2 -
        (B : ZMod 8) ^ 4 := by
  have h := congrArg (fun z : ℤ => (z : ZMod 8)) heq
  simpa using h

theorem r_odd_of_B_odd {r B s : ℤ} (hB_odd : B % 2 = 1)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 := by
  rcases int_mod_two_cases r with hr_even | hr_odd
  · have hs3 : (s : ZMod 4) ^ 2 = (3 : ZMod 4) := by
      calc
        (s : ZMod 4) ^ 2 =
            (r : ZMod 4) ^ 4 + (r : ZMod 4) ^ 2 * (B : ZMod 4) ^ 2 -
              (B : ZMod 4) ^ 4 := quartic_eq_zmod4 heq
        _ = (3 : ZMod 4) := by
          rw [zmod4_pow4_zero_of_even hr_even, zmod4_sq_zero_of_even hr_even,
            zmod4_sq_one_of_odd hB_odd, zmod4_pow4_one_of_odd hB_odd]
          norm_num
    exact False.elim ((zmod4_sq_ne_three (s : ZMod 4)) hs3)
  · exact hr_odd

theorem even_B_props {r B s : ℤ} (hB_even : B % 2 = 0) (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ 4 ∣ B := by
  have hr_odd : r % 2 = 1 := by
    rcases int_mod_two_cases r with hr_even | hr_odd
    · have h2r : (2 : ℤ) ∣ r := by
        refine ⟨r / 2, ?_⟩
        omega
      have h2B : (2 : ℤ) ∣ B := by
        refine ⟨B / 2, ?_⟩
        omega
      have h2g : (2 : ℤ) ∣ (Int.gcd r B : ℤ) :=
        Int.dvd_coe_gcd h2r h2B
      rw [hcop] at h2g
      exact False.elim ((by norm_num : ¬ (2 : ℤ) ∣ (1 : ℤ)) h2g)
    · exact hr_odd
  refine ⟨hr_odd, ?_⟩
  by_contra hnot4
  have hB4_ne_zero : B % 4 ≠ 0 := by
    intro hB4_zero
    apply hnot4
    refine ⟨B / 4, ?_⟩
    omega
  have hB4 : B % 4 = 2 := by
    have hnonneg4 : 0 ≤ B % (4 : ℤ) :=
      Int.emod_nonneg B (by norm_num : (4 : ℤ) ≠ 0)
    have hlt4 : B % (4 : ℤ) < 4 :=
      Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 4)
    have hnonneg2 : 0 ≤ B % (2 : ℤ) :=
      Int.emod_nonneg B (by norm_num : (2 : ℤ) ≠ 0)
    have hlt2 : B % (2 : ℤ) < 2 :=
      Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 2)
    omega
  have hs5 : (s : ZMod 8) ^ 2 = (5 : ZMod 8) := by
    calc
      (s : ZMod 8) ^ 2 =
          (r : ZMod 8) ^ 4 + (r : ZMod 8) ^ 2 * (B : ZMod 8) ^ 2 -
            (B : ZMod 8) ^ 4 := quartic_eq_zmod8 heq
      _ = (5 : ZMod 8) := by
        rw [zmod8_pow4_one_of_odd hr_odd, zmod8_sq_one_of_odd hr_odd,
          zmod8_sq_four_of_mod4_two hB4, zmod8_pow4_zero_of_mod4_two hB4]
        norm_num
  exact (zmod8_sq_ne_five (s : ZMod 8)) hs5
```

A couple of notes:

* `hcop` is not needed in `r_odd_of_B_odd`; the mod-4 contradiction alone forces `r` odd.
* `hr` and `hB` are not needed for the stated `even_B_props`; gcd plus `B % 2 = 0` gives `r` odd, and the mod-8 contradiction gives `4 ∣ B`.
* The proof avoids relying on a fragile global `decide` over expressions with integer casts.  The finite-field contradictions are isolated as `zmod4_sq_ne_three` and `zmod8_sq_ne_five`.
```
