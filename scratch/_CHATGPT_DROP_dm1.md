# Q1383 (dm1/dm1): `both_odd` parity for quartic-plus

The requested case split still has a real gap.  It proves:

* `r` even, `B` odd is impossible by mod `4`.
* `r,B` both even contradict `Int.gcd r B = 1`.
* `r` odd and `B = 2*m` with `m` odd is impossible by mod `8`.

But it does **not** cover the case

```text
r odd, 4 ∣ B.
```

In that case the congruence gives

```text
r^4 + r^2*B^2 - B^4 ≡ 1 + 0 - 0 ≡ 1 mod 8,
```

which is compatible with a square.  So the advertised parity proof does not prove `B % 2 = 1`.  The exact missing lemma is the `4 ∣ B` case.

## Compilable residue checks

These are the finite `ZMod` checks for the covered cases.

```lean
import Mathlib

namespace DM1

/-- Squares mod 4 are not `3`. -/
lemma zmod4_sq_ne_three (x : ZMod 4) : x ^ 2 ≠ 3 := by
  fin_cases x <;> decide

/-- Squares mod 8 are not `5`. -/
lemma zmod8_sq_ne_five (x : ZMod 8) : x ^ 2 ≠ 5 := by
  fin_cases x <;> decide

/-- If `r` is even and `B` is odd, the RHS is `3 mod 4`. -/
lemma rhs_mod4_r_even_B_odd
    (r B : ZMod 4)
    (hr : r = 0 ∨ r = 2)
    (hB : B = 1 ∨ B = 3) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 3 := by
  rcases hr with rfl | rfl <;>
  rcases hB with rfl | rfl <;>
  decide

/-- If `r` is odd and `B = 2*m` with `m` odd, the RHS is `5 mod 8`. -/
lemma rhs_mod8_r_odd_B_twice_odd
    (r B : ZMod 8)
    (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7)
    (hB : B = 2 ∨ B = 6) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 5 := by
  rcases hr with rfl | rfl | rfl | rfl <;>
  rcases hB with rfl | rfl <;>
  decide

/-- Sanity check: `r` odd and `4 ∣ B` is not contradicted mod 8. -/
example :
    ((1 : ZMod 8) ^ 4 + (1 : ZMod 8) ^ 2 * (4 : ZMod 8) ^ 2 -
      (4 : ZMod 8) ^ 4) = 1 := by
  decide

/-- Sanity check: `r` odd and `4 ∣ B` is not excluded by coprimality. -/
example : Int.gcd 1 4 = 1 := by
  norm_num

end DM1
```

## Honest `both_odd` skeleton

The following is the correct shape: all advertised residue computations are mechanical, but the `4 ∣ B` subcase must be supplied separately.

```lean
import Mathlib

namespace DM1

/-- Exact missing case for the proposed proof of `B` odd. -/
lemma no_solution_with_r_odd_and_four_dvd_B
    {r B s : ℤ}
    (hrpos : 0 < r) (hBpos : 0 < B)
    (hr_odd : r % 2 = 1)
    (hgcd : Int.gcd r B = 1)
    (h4B : (4 : ℤ) ∣ B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    False := by
  -- Not a mod-8 contradiction: the RHS is `1 mod 8` in this subcase.
  -- This needs an additional 2-adic/descent argument, or another global argument.
  sorry

lemma both_odd_skeleton
    {r B s : ℤ}
    (hrpos : 0 < r) (hBpos : 0 < B)
    (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  -- 1. Prove `r % 2 = 1`.
  --    If `r` is even, then either `B` is even, contradicting gcd=1,
  --    or `B` is odd, and the mod-4 residue lemma gives `s^2 = 3` in `ZMod 4`.
  have hr_odd : r % 2 = 1 := by
    sorry

  -- 2. Prove `B % 2 = 1`.
  --    If `B` is even, then either:
  --    * `B = 2*m` with `m` odd: use the mod-8 residue lemma, or
  --    * `4 ∣ B`: call the missing lemma above.
  have hB_odd : B % 2 = 1 := by
    by_cases h4B : (4 : ℤ) ∣ B
    · exact False.elim
        (no_solution_with_r_odd_and_four_dvd_B hrpos hBpos hr_odd hgcd h4B heq)
    · -- Here even `B` means `B = 2*m` with `m` odd; use `rhs_mod8_r_odd_B_twice_odd`.
      sorry

  exact ⟨hr_odd, hB_odd⟩

end DM1
```

Bottom line: the finite residue lemmas compile, but the full `both_odd` theorem does not follow from the stated proof unless you add the missing `4 ∣ B` subcase lemma.
