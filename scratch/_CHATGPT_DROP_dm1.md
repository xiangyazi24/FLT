# Q1373 (dm1/dm1): parity in the quartic-plus equation

I cannot honestly give the requested complete proof as stated from the proposed argument, because the proposed `B`-even proof has a real gap.

The `r`-even branch is correct:

```text
r even and gcd(r,B)=1  ⇒  B odd,
RHS ≡ 0 + 0 - 1 ≡ 3 mod 4,
```

which contradicts the fact that squares mod `4` are only `0,1`.

But the proposed `B`-even proof only handles the subcase `v₂(B)=1`.  If `B=2k` with `k` odd, then modulo `16` gives

```text
RHS ≡ 1 + 4 - 0 ≡ 5 mod 16,
```

which is impossible.  However, if `B=4m`, then modulo `16` gives

```text
RHS ≡ r^4 ≡ 1 mod 16,
```

which is compatible with being a square.  This is **not** a gcd issue: for example `gcd(1,4)=1`.

So the exact missing lemma is:

```lean
lemma B_divisible_by_four_impossible
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (h4 : (4 : ℤ) ∣ B) : False := by
  sorry
```

Without that lemma, `Odd B` does not follow from the advertised mod-16 argument.

## Compilable finite residue checks

These are the clean finite checks to use with `ZMod`.

```lean
import Mathlib

namespace DM1

lemma zmod4_square_ne_three (x : ZMod 4) : x ^ 2 ≠ 3 := by
  fin_cases x <;> decide

lemma zmod16_square_ne_five (x : ZMod 16) : x ^ 2 ≠ 5 := by
  fin_cases x <;> decide

/-- The `r`-even, `B`-odd RHS is `3 mod 4`. -/
lemma rhs_mod4_of_r_even_B_odd
    (r B : ZMod 4)
    (hr : r = 0 ∨ r = 2)
    (hB : B = 1 ∨ B = 3) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 3 := by
  rcases hr with rfl | rfl <;>
  rcases hB with rfl | rfl <;>
  decide

/-- The `B=2k`, `k` odd, `r` odd RHS is `5 mod 16`. -/
lemma rhs_mod16_of_r_odd_B_two_times_odd
    (r B : ZMod 16)
    (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 9 ∨ r = 11 ∨ r = 13 ∨ r = 15)
    (hB : B = 2 ∨ B = 6 ∨ B = 10 ∨ B = 14) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 5 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hB with rfl | rfl | rfl | rfl <;>
  decide

/-- Sanity check: `B=4m` is not contradicted by mod `16`. -/
example :
    ((1 : ZMod 16) ^ 4 + (1 : ZMod 16) ^ 2 * (4 : ZMod 16) ^ 2 -
      (4 : ZMod 16) ^ 4) = 1 := by
  decide

/-- Sanity check: `B=4m` is not excluded by coprimality. -/
example : Int.gcd 1 4 = 1 := by
  norm_num

end DM1
```

## Skeleton with the exact `sorry`

This is the honest Lean skeleton.  The first branch is the advertised mod-4 contradiction; the second branch needs the missing `B_divisible_by_four_impossible` lemma after the mod-16 subcase `B ≡ 2 mod 4` is removed.

```lean
import Mathlib

namespace DM1

lemma B_divisible_by_four_impossible
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (h4 : (4 : ℤ) ∣ B) : False := by
  -- This is not proved by the stated mod-16 argument.
  -- It needs an additional 2-adic/descent argument.
  sorry

lemma quartic_parity
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Odd r ∧ Odd B := by
  -- Recommended structure:
  -- 1. Prove `Odd r` by contradiction.
  --    If `Even r`, then `Odd B` from gcd, and the ZMod-4 check above gives
  --    `s^2 = 3` in `ZMod 4`, contradicting `zmod4_square_ne_three`.
  have hr_odd : Odd r := by
    sorry

  -- 2. Prove `Odd B` by contradiction.
  --    If `Even B`, then `Odd r` from gcd. Split on whether `4 ∣ B`.
  --    * If not `4 ∣ B`, then `B ≡ 2 mod 4`, so the ZMod-16 check gives
  --      `s^2 = 5`, contradicting `zmod16_square_ne_five`.
  --    * If `4 ∣ B`, call the missing lemma above.
  have hB_odd : Odd B := by
    sorry

  exact ⟨hr_odd, hB_odd⟩

end DM1
```

Bottom line: the mod-4 and mod-16 residue checks are easy and compile, but they do **not** prove `Odd B`.  The exact remaining proof obligation is the `4 ∣ B` subcase.
