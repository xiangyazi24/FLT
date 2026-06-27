# Q1448 (dm1/dm2): `quartic_plus_both_odd`

I do **not** think the proposed “simple” proof proves the stated theorem as written.

The branches

* `r` even, `B` even: impossible from `gcd(r,B)=1`;
* `r` even, `B` odd: contradiction mod `4`, because the RHS is `3` mod `4`;
* `r` odd, `B = 2*c` with `c` odd: contradiction mod `8`, because the RHS is `5` mod `8`;

are fine.

But the remaining branch is

```text
r odd, 4 ∣ B.
```

In this branch the proposed repeat step is not valid.  If `B = 4*d`, then modulo `8` the equation only gives

```text
s^2 ≡ r^4 ≡ 1  (mod 8),
```

which is compatible with `s` odd.  More strongly, this is not a removable Lean annoyance: for example the local congruence with `r ≡ 1`, `B ≡ 4` gives RHS `≡ 17 (mod 32)`, and `17` is a square mod `32`.  So a proof of `B % 2 = 1` needs an additional descent/global argument; it does not follow from the stated mod-`4`/mod-`8` checks alone.

Here is the clean Lean skeleton I would use.  It isolates the genuinely proved congruence obstructions and makes the missing `4 ∣ B` branch explicit.

```lean
import Mathlib

namespace DM2

lemma int_emod_two_eq_zero_or_one (z : ℤ) : z % 2 = 0 ∨ z % 2 = 1 := by
  have h0 : 0 ≤ z % 2 := Int.emod_nonneg z (by norm_num)
  have hlt : z % 2 < 2 := Int.emod_lt_of_pos z (by norm_num)
  omega

lemma int_even_witness_of_emod_two_eq_zero {z : ℤ} (hz : z % 2 = 0) :
    ∃ k : ℤ, z = 2 * k := by
  refine ⟨z / 2, ?_⟩
  omega

lemma int_odd_witness_of_emod_two_eq_one {z : ℤ} (hz : z % 2 = 1) :
    ∃ k : ℤ, z = 2 * k + 1 := by
  refine ⟨z / 2, ?_⟩
  omega

lemma zmod4_sq_values (x : ZMod 4) : x ^ 2 = 0 ∨ x ^ 2 = 1 := by
  fin_cases x <;> decide

lemma zmod8_sq_values (x : ZMod 8) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  fin_cases x <;> decide

/-- The mod-4 obstruction: `r` even and `B` odd is impossible. -/
lemma quartic_plus_not_r_even_B_odd {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr : r % 2 = 0) (hB : B % 2 = 1) : False := by
  rcases int_even_witness_of_emod_two_eq_zero hr with ⟨a, rfl⟩
  rcases int_odd_witness_of_emod_two_eq_one hB with ⟨b, rfl⟩
  have hcast := congrArg (fun z : ℤ => (z : ZMod 4)) heq
  ring_nf at hcast
  have hs := zmod4_sq_values (s : ZMod 4)
  rcases hs with hs | hs
  · rw [hs] at hcast
    norm_num at hcast
  · rw [hs] at hcast
    norm_num at hcast

/-- The mod-8 obstruction: `r` odd and `B = 2*c` with `c` odd is impossible. -/
lemma quartic_plus_not_r_odd_B_twice_odd {r B s c : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr : r % 2 = 1) (hB : B = 2 * c) (hc : c % 2 = 1) : False := by
  subst B
  rcases int_odd_witness_of_emod_two_eq_one hr with ⟨a, rfl⟩
  rcases int_odd_witness_of_emod_two_eq_one hc with ⟨b, rfl⟩
  have hcast := congrArg (fun z : ℤ => (z : ZMod 8)) heq
  ring_nf at hcast
  have hs := zmod8_sq_values (s : ZMod 8)
  rcases hs with hs | hs | hs
  · rw [hs] at hcast
    norm_num at hcast
  · rw [hs] at hcast
    norm_num at hcast
  · rw [hs] at hcast
    norm_num at hcast

/-- Convert `B % 2 = 0` and `B % 4 ≠ 0` into the `B = 2*c`, `c` odd shape. -/
lemma even_not_four_dvd_as_twice_odd {B : ℤ}
    (hB2 : B % 2 = 0) (hB4 : B % 4 ≠ 0) :
    ∃ c : ℤ, B = 2 * c ∧ c % 2 = 1 := by
  refine ⟨B / 2, ?_, ?_⟩
  · omega
  · have hB4eq : B % 4 = 2 := by
      have h0 : 0 ≤ B % 4 := Int.emod_nonneg B (by norm_num)
      have hlt : B % 4 < 4 := Int.emod_lt_of_pos B (by norm_num)
      omega
    omega

/--
This is the precise theorem that the elementary congruence argument proves.

The extra hypothesis `hB_not_four` is exactly the missing branch in the proposed proof.
To prove the original `quartic_plus_both_odd`, replace `hB_not_four` by a real descent lemma
showing that `4 ∣ B` is impossible under the quartic equation and `gcd(r,B)=1`.
-/
theorem quartic_plus_both_odd_from_no_four_branch {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hcop2 : ¬ (r % 2 = 0 ∧ B % 2 = 0))
    (hB_not_four : B % 4 ≠ 0) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  have hrpar := int_emod_two_eq_zero_or_one r
  have hBpar := int_emod_two_eq_zero_or_one B
  constructor
  · rcases hrpar with hr0 | hr1
    · rcases hBpar with hB0 | hB1
      · exact False.elim (hcop2 ⟨hr0, hB0⟩)
      · exact False.elim (quartic_plus_not_r_even_B_odd heq hr0 hB1)
    · exact hr1
  · rcases hBpar with hB0 | hB1
    · have hr1 : r % 2 = 1 := by
        rcases hrpar with hr0 | hr1
        · exact False.elim (hcop2 ⟨hr0, hB0⟩)
        · exact hr1
      rcases even_not_four_dvd_as_twice_odd hB0 hB_not_four with ⟨c, hBc, hc⟩
      exact False.elim (quartic_plus_not_r_odd_B_twice_odd heq hr1 hBc hc)
    · exact hB1

end DM2
```

For the original theorem, the right shape is therefore:

```lean
-- genuine missing ingredient, not a congruence-only lemma
lemma quartic_plus_not_four_dvd_B {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hcop : Int.gcd r B = 1)
    (hrpos : 0 < r) (hBpos : 0 < B) :
    B % 4 ≠ 0 := by
  -- descent/global argument needed here
  sorry
```

Once that is available, `quartic_plus_both_odd` is just the wrapper above plus the standard lemma turning `Int.gcd r B = 1` into `¬ (r % 2 = 0 ∧ B % 2 = 0)`.

I would not encode the “repeat until gcd forces `B` odd” line in Lean: it is mathematically false as a standalone parity argument.  Repetition only works after proving a descent step that produces a smaller solution of the same quartic shape, and that is the real missing lemma.