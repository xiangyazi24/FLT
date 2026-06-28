# Q1915 (dm3): dm4 — quartic `d` versus Kubert torsion order

## Executive answer

No: the formula `n = 2 * (d + 3)` is **not** the right interpretation for the quartic family

```text
t^2 = s^4 + d^2 * s^2 - d^4.
```

For this exact quartic shape, **every nonzero value of `d` gives the same rational obstruction curve**, namely the listed Kubert obstruction curve for `N = 10`:

```text
E10 : w^2 = u^3 + u^2 - u.
```

The change of variables is

```text
u = (s / d)^2,
w = s * t / d^3.
```

Indeed, dividing the quartic by `d^4` gives

```text
(t / d^2)^2 = (s / d)^4 + (s / d)^2 - 1,
```

and multiplying by `(s / d)^2` gives

```text
(s * t / d^3)^2
  = (s / d)^2 * ((s / d)^4 + (s / d)^2 - 1)
  = u^3 + u^2 - u.
```

So the mapping is not

```text
d = 2 ↦ n = 10,
d = 3 ↦ n = 12,
d = 4 ↦ n = 14,
d = 5 ↦ n = 16.
```

Instead, for the exact equation `s^4 + d^2*s^2 - d^4 = t^2`, the correct table is:

| `d` | obstruction curve reached by the square-`u` substitution | torsion order label |
|---:|---|---:|
| 2 | `w^2 = u^3 + u^2 - u` | `N = 10` |
| 3 | `w^2 = u^3 + u^2 - u` | `N = 10` |
| 4 | `w^2 = u^3 + u^2 - u` | `N = 10` |
| 5 | `w^2 = u^3 + u^2 - u` | `N = 10` |
| 6 | `w^2 = u^3 + u^2 - u` | `N = 10` |
| 7 | `w^2 = u^3 + u^2 - u` | `N = 10` |

The role of `d` here is just an integral scaling / denominator-clearing parameter. It is not the torsion-order parameter.

## What quartics match the other listed obstruction curves?

For a curve of the form

```text
E(A,B) : w^2 = u^3 + A*u^2 + B*u,
```

using the same square substitution

```text
u = (s / D)^2,
w = s * t / D^3
```

corresponds to the quartic

```text
t^2 = s^4 + A*D^2*s^2 + B*D^4.
```

Applying that to the four obstruction curves in the prompt gives:

| torsion order | obstruction curve | corresponding scaled quartic shape |
|---:|---|---|
| `N = 10` | `w^2 = u^3 + u^2 - u` | `t^2 = s^4 + D^2*s^2 - D^4` |
| `N = 12` | `w^2 = u^3 - u^2 - 4*u + 4` | not directly of `u*(quadratic)` form because of the constant `+4`; the naive `u=(s/D)^2` trick does not give the displayed quartic family |
| `N = 14` | `w^2 = u^3 + u^2 - 2*u` | `t^2 = s^4 + D^2*s^2 - 2*D^4` |
| `N = 16` | `w^2 = u^3 - u^2 - u` | `t^2 = s^4 - D^2*s^2 - D^4` |

Thus the displayed family with the **positive** middle term and the **coefficient `-1`** constant term is specifically the `N = 10` family.

## Sanity check by `j`-invariants

A quick way to see that the same quartic family cannot be separately encoding `N = 10,12,14,16` is that all curves

```text
t^2 = s^4 + d^2*s^2 - d^4
```

are rationally equivalent after scaling `s = d*x`, `t = d^2*y`; they all reduce to

```text
y^2 = x^4 + x^2 - 1.
```

So, over `ℚ`, the value of `d` cannot change the isomorphism class of the associated genus-one curve.

For curves `w^2 = u^3 + A*u^2 + B*u`, the invariant

```text
j = 256 * (A^2 - 3*B)^3 / (B^2 * (A^2 - 4*B))
```

shows that the listed obstruction curves are not all the same rational curve. For example:

```text
N = 10: A =  1, B = -1, j = 16384/5
N = 14: A =  1, B = -2, j = 21952/9
N = 16: A = -1, B = -1, j = 16384/5
```

`N = 10` and `N = 16` have the same `j`, but they are quadratic twists of each other; the sign of the middle term in the quartic distinguishes the square-substitution quartics above.

## Warning about the stated `QuarticD2` through `QuarticD7`

If `QuarticD2` through `QuarticD7` literally assert that there are no integer solutions to

```text
t^2 = s^4 + d^2*s^2 - d^4
```

with no extra hypotheses, those statements are false: for every positive `d`,

```text
s = d,
t = ± d^2
```

is an immediate solution, since

```text
d^4 + d^4 - d^4 = d^4.
```

This is the point `u = 1`, `w = ±1` on `E10`. If the intended lemmas exclude cuspidal/trivial points, primitive cases, or require additional side conditions, those exclusions need to be present in the theorem statements.

## Lean-shaped algebra check

The basic algebraic reduction to the `N = 10` obstruction curve can be recorded as follows.

```lean
import Mathlib

example {d s t : ℚ} (hd : d ≠ 0)
    (h : s ^ 4 + d ^ 2 * s ^ 2 - d ^ 4 = t ^ 2) :
    (s * t / d ^ 3) ^ 2 =
      (s ^ 2 / d ^ 2) ^ 3 + (s ^ 2 / d ^ 2) ^ 2 - (s ^ 2 / d ^ 2) := by
  field_simp [hd]
  field_simp [hd] at h
  ring_nf at h ⊢
  nlinarith
```

The conceptual takeaway for the formalization is: do not use `d` to choose among `N = 10,12,14,16` for this quartic. Use the actual cubic obstruction curve coefficients. The equation `s^4 + d^2*s^2 - d^4 = t^2` only matches the `N = 10` obstruction curve under the displayed square substitution.
