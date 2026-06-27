# Q1502 (dm1/dm2): `Int.natAbs` comparison for positive integers

Yes: use

```lean
Int.natAbs_lt_natAbs_of_nonneg_of_lt
```

It has the exact shape you want after turning positivity into nonnegativity:

```lean
exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hlt
```

where

```lean
hαpos : 0 < α
hlt   : α < a * b
```

Minimal compilable examples:

```lean
import Mathlib

example {α a b : ℤ}
    (hαpos : 0 < α)
    (hlt : α < a * b) :
    α.natAbs < (a * b).natAbs := by
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hlt

example {α B : ℤ}
    (hαpos : 0 < α)
    (hlt : α < B) :
    α.natAbs < B.natAbs := by
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hlt
```

You do **not** need to cast through `Nat` manually.

For your specific inequality, first prove the integer strict inequality `α < a*b`, then finish with the one-liner above.  A robust skeleton is:

```lean
-- after you have proved this:
have hlt_int : α < a * b := by
  -- prove by monotonicity + rule out equality with `¬ BaseZ β α`
  -- `nlinarith` often closes once you have the equality case excluded.
  sorry

exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hlt_int
```

A useful pattern for deriving the strict inequality is to first prove non-strict bounds and then rule out equality:

```lean
have hβ_ge_one : 1 ≤ β := by omega
have ha_ge_one : 1 ≤ a := by omega
have hα_le_b : α ≤ b := by
  -- using `b = α * β` and `1 ≤ β`
  nlinarith
have hb_le_ab : b ≤ a * b := by
  -- using `1 ≤ a` and `0 < b`
  nlinarith
have hα_le_ab : α ≤ a * b := le_trans hα_le_b hb_le_ab
have hneq : α ≠ a * b := by
  -- equality forces β = 1 and a = 1; combine with `¬ BaseZ β α`
  sorry
have hlt_int : α < a * b := lt_of_le_of_ne hα_le_ab hneq
```

Then the natAbs target is immediate:

```lean
exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hlt_int
```