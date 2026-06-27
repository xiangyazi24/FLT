# Q1465 (dm2/dm1): closing `Rat.den_div_eq_of_coprime` with `b = d^3`

## Direct answer

`Rat.den_div_eq_of_coprime` takes the denominator parameter as an **integer**:

```lean
theorem Rat.den_div_eq_of_coprime {a b : ℤ}
    (hb0 : 0 < b)
    (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b
```

So if you apply it with `b = d^3`, the positivity hypothesis is exactly

```lean
0 < d ^ 3        -- with d : ℤ
```

and this is closed by

```lean
have hdenpos : 0 < d ^ 3 := pow_pos hdpos 3
```

where

```lean
have hdpos : 0 < d := by
  dsimp [d]
  exact_mod_cast u.den_pos
```

The coprimality expected by `Rat.den_div_eq_of_coprime` is a `Nat.Coprime` statement on `natAbs`.  If you have

```lean
hcopN_d3 : IsCoprime N (d ^ 3)
```

then the exact conversion is

```lean
have hcopNat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
  (Int.isCoprime_iff_nat_coprime.mp hcopN_d3)
```

Do this explicitly; do not ask `exact_mod_cast` to invent the `Nat.Coprime` proof.

## Exact closer when the goal is an `Int` equality

This is the cleanest situation.  If your goal is

```lean
(((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3
```

then the closing tactic is just:

```lean
exact Rat.den_div_eq_of_coprime
  (a := N) (b := d ^ 3) hdenpos hcopNat
```

If Lean’s displayed denominator is written slightly differently, use `simpa`:

```lean
simpa using
  (Rat.den_div_eq_of_coprime
    (a := N) (b := d ^ 3) hdenpos hcopNat)
```

## Exact closer after rewriting by your rational representation

Suppose you have

```lean
let d : ℤ := u.den
let N : ℤ := ...
hrepr : u ^ 3 + u ^ 2 - u = (N : ℚ) / (d ^ 3 : ℚ)
```

and your goal is

```lean
(((u ^ 3 + u ^ 2 - u).den : ℤ) = d ^ 3)
```

then use:

```lean
rw [hrepr]
exact Rat.den_div_eq_of_coprime
  (a := N) (b := d ^ 3) hdenpos hcopNat
```

If the right side is still displayed as `(u.den : ℤ)^3`, use `change` after the rewrite:

```lean
rw [hrepr]
change (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3
exact Rat.den_div_eq_of_coprime
  (a := N) (b := d ^ 3) hdenpos hcopNat
```

## Exact closer when the final goal is a `Nat` denominator equality

Often the final goal is the natural-number equality

```lean
((N : ℚ) / (d ^ 3 : ℚ)).den = u.den ^ 3
```

while `Rat.den_div_eq_of_coprime` gives the integer-cast equality.  In that case, first create the integer equality, unfold `d`, and then use `exact_mod_cast`:

```lean
have hden_int :
    (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3 :=
  Rat.den_div_eq_of_coprime
    (a := N) (b := d ^ 3) hdenpos hcopNat

dsimp [d] at hden_int
exact_mod_cast hden_int
```

This is the pattern I would use.  `exact_mod_cast` handles the cast of

```lean
(u.den ^ 3 : ℕ)  ↦  ((u.den : ℤ) ^ 3)
```

on the target side.

## Complete local snippet

```lean
import Mathlib

namespace Q1465

example (u : ℚ) (N : ℤ)
    (hcopN : IsCoprime N ((u.den : ℤ) ^ 3)) :
    (((N : ℚ) / (((u.den : ℤ) ^ 3 : ℤ) : ℚ)).den : ℤ) =
      ((u.den : ℤ) ^ 3 : ℤ) := by
  let d : ℤ := u.den

  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast u.den_pos

  have hdenpos : 0 < d ^ 3 :=
    pow_pos hdpos 3

  have hcopN_d3 : IsCoprime N (d ^ 3) := by
    dsimp [d]
    simpa using hcopN

  have hcopNat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    (Int.isCoprime_iff_nat_coprime.mp hcopN_d3)

  change (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3
  exact Rat.den_div_eq_of_coprime
    (a := N) (b := d ^ 3) hdenpos hcopNat

example (u : ℚ) (N : ℤ)
    (hcopN : IsCoprime N ((u.den : ℤ) ^ 3)) :
    ((N : ℚ) / (((u.den : ℤ) ^ 3 : ℤ) : ℚ)).den = u.den ^ 3 := by
  let d : ℤ := u.den

  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast u.den_pos

  have hdenpos : 0 < d ^ 3 :=
    pow_pos hdpos 3

  have hcopN_d3 : IsCoprime N (d ^ 3) := by
    dsimp [d]
    simpa using hcopN

  have hcopNat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    (Int.isCoprime_iff_nat_coprime.mp hcopN_d3)

  have hden_int :
      (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3 :=
    Rat.den_div_eq_of_coprime
      (a := N) (b := d ^ 3) hdenpos hcopNat

  dsimp [d] at hden_int
  exact_mod_cast hden_int

end Q1465
```

## In the denominator computation from `u = num/den`

The final block usually looks like this:

```lean
  rw [hrepr]
  change (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3
  exact Rat.den_div_eq_of_coprime
    (a := N) (b := d ^ 3) hdenpos hcopNat
```

or, for a natural-number target:

```lean
  rw [hrepr]
  have hden_int :
      (((N : ℚ) / (d ^ 3 : ℚ)).den : ℤ) = d ^ 3 :=
    Rat.den_div_eq_of_coprime
      (a := N) (b := d ^ 3) hdenpos hcopNat
  dsimp [d] at hden_int
  exact_mod_cast hden_int
```

## Bottom line

Yes: `hb0` is `0 < b` for `b : ℤ`.  For `b = d^3`, use `pow_pos hdpos 3`.  Convert

```lean
IsCoprime N (d^3)
```

to

```lean
Nat.Coprime N.natAbs (d^3).natAbs
```

using

```lean
Int.isCoprime_iff_nat_coprime.mp
```

Then close the integer denominator goal by direct `exact`, and close the natural denominator goal by `exact_mod_cast hden_int` after `dsimp [d] at hden_int`.
