# Q1971 (dm2): local obstruction primes for N=14 and N=16

## Executive answer

Yes, but the native-decide checks should be applied to the **2-covering / Selmer homogeneous spaces**, not directly to the elliptic curve equation.  A finite-field search on

```text
w^2 = u^3 + u^2 - 2u
w^2 = u^3 - u^2 - u
```

will of course find the torsion reductions.  The useful checks are instead: for each non-torsion Selmer candidate, show the associated quartic covering has no primitive solution modulo a suitable prime power.

The useful primes are:

```text
N=14: p = 2 and p = 3
N=16: p = 5 and p = 2
```

More precisely:

```text
N=14, E  side d =  3: obstruction modulo 4.
N=14, E  side d = -3: obstruction modulo 27, if your sign conventions include it.
N=14, E' side d =  2: obstruction modulo 8.
N=14, E' side d = -2: obstruction modulo 8.

N=16, E  side d =  5: obstruction modulo 125.
N=16, E  side d = -5: obstruction modulo 125, if your sign conventions include it.
N=16, E' side d = -1: obstruction modulo 16.
```

For N=16, this is essentially the same prime-power pattern as the N=10 proof: the `5`-cover is killed at `5^3 = 125`, and the dual `-1` cover is killed at `2^4 = 16`.

For N=14, the small-prime pattern is even lighter: one side is killed 2-adically (`mod 4` or `mod 8`), and the possible negative `3`-class is killed 3-adically (`mod 27`).

## Conventions for the 2-isogeny covering equations

For a curve

```text
E : y^2 = x^3 + a*x^2 + b*x
```

with the rational 2-torsion point `(0,0)`, I am using the standard covering equation

```text
d * Y^2 = d^2 * X^4 + d*a*X^2*Z^2 + b*Z^4.
```

The 2-isogenous curve is

```text
E' : y^2 = x^3 - 2*a*x^2 + (a^2 - 4*b)*x.
```

Different books flip signs or replace `d` by an equivalent squareclass.  That is why I include both signs for the classes where ambiguity is likely.  The native-decide checks below are cheap enough that keeping the redundant sign checks is safer than encoding a convention mismatch.

## N=14 details

For

```text
E14 : y^2 = x^3 + x^2 - 2*x
```

we have

```text
a = 1,
b = -2,
E14' : y^2 = x^3 - 2*x^2 + 9*x.
```

The nontrivial `E14`-side class is represented by `d = 3` up to sign.  The covering is

```text
3*Y^2 = 9*X^4 + 3*X^2*Z^2 - 2*Z^4.
```

This has no primitive solution modulo `4`, where primitive means not both `X,Z` are even.

If the `d = -3` class appears under your sign conventions, use the congruence

```text
-3*Y^2 = 9*X^4 - 3*X^2*Z^2 - 2*Z^4,
```

which has no primitive solution modulo `27`, where primitive means not both `X,Z` are divisible by `3`.

On the dual side

```text
E14' : y^2 = x^3 - 2*x^2 + 9*x,
```

the relevant classes are `d = ±2`.  The two checks are

```text
 2*Y^2 = 4*X^4 - 4*X^2*Z^2 + 9*Z^4     mod 8,
-2*Y^2 = 4*X^4 + 4*X^2*Z^2 + 9*Z^4     mod 8.
```

Both have no primitive solution modulo `8`.

So for N=14, the practical finite checks are:

```text
mod 4   for the E-side d=3 cover;
mod 27  for the optional E-side d=-3 cover;
mod 8   for both dual d=2 and d=-2 covers.
```

## N=16 details

For

```text
E16 : y^2 = x^3 - x^2 - x
```

we have

```text
a = -1,
b = -1,
E16' : y^2 = x^3 + 2*x^2 + 5*x.
```

The `E16`-side nontrivial class is represented by `d = 5` up to sign.  The covering is

```text
5*Y^2 = 25*X^4 - 5*X^2*Z^2 - Z^4.
```

It has no primitive solution modulo `125`, where primitive means not both `X,Z` are divisible by `5`.

The sign variant

```text
-5*Y^2 = 25*X^4 + 5*X^2*Z^2 - Z^4
```

is also obstructed modulo `125`.

On the dual side

```text
E16' : y^2 = x^3 + 2*x^2 + 5*x,
```

the relevant class is `d = -1`.  The covering can be written as

```text
Y^2 = -X^4 + 2*X^2*Z^2 - 5*Z^4.
```

This has no primitive solution modulo `16`, where primitive means not both `X,Z` are even.

If a sign convention changes the middle term, the sibling equation

```text
Y^2 = -X^4 - 2*X^2*Z^2 - 5*Z^4
```

is also obstructed modulo `16`; this is exactly the same robust pattern already used in the N=10 local-obstruction file.

## Lean code: native_decide checks

This is written in the same style as the existing `DescentObstruction.lean` file.

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace FLT
namespace MazurLocalObstructionsN14N16

/-! ## Primitive residue predicates -/

def NonzeroMod2_4 (a : ZMod 4) : Bool :=
  decide (a.val % 2 ≠ 0)

def PrimitiveMod2_4 (x z : ZMod 4) : Bool :=
  NonzeroMod2_4 x || NonzeroMod2_4 z

def NonzeroMod2_8 (a : ZMod 8) : Bool :=
  decide (a.val % 2 ≠ 0)

def PrimitiveMod2_8 (x z : ZMod 8) : Bool :=
  NonzeroMod2_8 x || NonzeroMod2_8 z

def NonzeroMod2_16 (a : ZMod 16) : Bool :=
  decide (a.val % 2 ≠ 0)

def PrimitiveMod2_16 (x z : ZMod 16) : Bool :=
  NonzeroMod2_16 x || NonzeroMod2_16 z

def NonzeroMod3_27 (a : ZMod 27) : Bool :=
  decide (a.val % 3 ≠ 0)

def PrimitiveMod3_27 (x z : ZMod 27) : Bool :=
  NonzeroMod3_27 x || NonzeroMod3_27 z

def NonzeroMod5_125 (a : ZMod 125) : Bool :=
  decide (a.val % 5 ≠ 0)

def PrimitiveMod5_125 (x z : ZMod 125) : Bool :=
  NonzeroMod5_125 x || NonzeroMod5_125 z

/-! ## N = 14, E-side classes -/

/--
For `E14 : y² = x³ + x² - 2x`, the `d = 3` covering

`3Y² = 9X⁴ + 3X²Z² - 2Z⁴`

has no primitive solution modulo `4`.
-/
set_option maxHeartbeats 0 in
theorem N14_E_d3_no_primitive_mod4 :
    ¬ ∃ x y z : ZMod 4,
      PrimitiveMod2_4 x z = true ∧
        (3 : ZMod 4) * y ^ 2 =
          (9 : ZMod 4) * x ^ 4 +
          (3 : ZMod 4) * x ^ 2 * z ^ 2 -
          (2 : ZMod 4) * z ^ 4 := by
  native_decide

/--
Optional sign variant for the `E14`-side `d = -3` class.  This one is killed
modulo `27`.
-/
set_option maxHeartbeats 0 in
theorem N14_E_dm3_no_primitive_mod27 :
    ¬ ∃ x y z : ZMod 27,
      PrimitiveMod3_27 x z = true ∧
        (-3 : ZMod 27) * y ^ 2 =
          (9 : ZMod 27) * x ^ 4 -
          (3 : ZMod 27) * x ^ 2 * z ^ 2 -
          (2 : ZMod 27) * z ^ 4 := by
  native_decide

/-! ## N = 14, dual-side classes -/

/--
For `E14' : y² = x³ - 2x² + 9x`, the `d = 2` covering

`2Y² = 4X⁴ - 4X²Z² + 9Z⁴`

has no primitive solution modulo `8`.
-/
set_option maxHeartbeats 0 in
theorem N14_Ep_d2_no_primitive_mod8 :
    ¬ ∃ x y z : ZMod 8,
      PrimitiveMod2_8 x z = true ∧
        (2 : ZMod 8) * y ^ 2 =
          (4 : ZMod 8) * x ^ 4 -
          (4 : ZMod 8) * x ^ 2 * z ^ 2 +
          (9 : ZMod 8) * z ^ 4 := by
  native_decide

/-- Same dual side, opposite sign representative `d = -2`. -/
set_option maxHeartbeats 0 in
theorem N14_Ep_dm2_no_primitive_mod8 :
    ¬ ∃ x y z : ZMod 8,
      PrimitiveMod2_8 x z = true ∧
        (-2 : ZMod 8) * y ^ 2 =
          (4 : ZMod 8) * x ^ 4 +
          (4 : ZMod 8) * x ^ 2 * z ^ 2 +
          (9 : ZMod 8) * z ^ 4 := by
  native_decide

/-! ## N = 16, E-side classes -/

/--
For `E16 : y² = x³ - x² - x`, the `d = 5` covering

`5Y² = 25X⁴ - 5X²Z² - Z⁴`

has no primitive solution modulo `125`.
-/
set_option maxHeartbeats 0 in
theorem N16_E_d5_no_primitive_mod125 :
    ¬ ∃ x y z : ZMod 125,
      PrimitiveMod5_125 x z = true ∧
        (5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 -
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4 := by
  native_decide

/-- Optional sign variant for the `E16`-side `d = -5` representative. -/
set_option maxHeartbeats 0 in
theorem N16_E_dm5_no_primitive_mod125 :
    ¬ ∃ x y z : ZMod 125,
      PrimitiveMod5_125 x z = true ∧
        (-5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 +
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4 := by
  native_decide

/-! ## N = 16, dual-side classes -/

/--
For `E16' : y² = x³ + 2x² + 5x`, the `d = -1` covering is

`Y² = -X⁴ + 2X²Z² - 5Z⁴`,

and it has no primitive solution modulo `16`.
-/
def N16_Ep_dm1_rhs_plus (x z : ZMod 16) : ZMod 16 :=
  - x ^ 4 +
    (2 : ZMod 16) * x ^ 2 * z ^ 2 -
    (5 : ZMod 16) * z ^ 4

set_option maxHeartbeats 0 in
theorem N16_Ep_dm1_no_primitive_mod16_plus :
    ¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = N16_Ep_dm1_rhs_plus x z := by
  native_decide

/-- Robust sign-convention sibling, also obstructed modulo `16`. -/
def N16_Ep_dm1_rhs_minus (x z : ZMod 16) : ZMod 16 :=
  - x ^ 4 -
    (2 : ZMod 16) * x ^ 2 * z ^ 2 -
    (5 : ZMod 16) * z ^ 4

set_option maxHeartbeats 0 in
theorem N16_Ep_dm1_no_primitive_mod16_minus :
    ¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = N16_Ep_dm1_rhs_minus x z := by
  native_decide

/-- Package of the recommended checks for the likely sign conventions. -/
theorem recommended_obstructions_verified :
    (¬ ∃ x y z : ZMod 4,
      PrimitiveMod2_4 x z = true ∧
        (3 : ZMod 4) * y ^ 2 =
          (9 : ZMod 4) * x ^ 4 +
          (3 : ZMod 4) * x ^ 2 * z ^ 2 -
          (2 : ZMod 4) * z ^ 4)
    ∧
    (¬ ∃ x y z : ZMod 8,
      PrimitiveMod2_8 x z = true ∧
        (2 : ZMod 8) * y ^ 2 =
          (4 : ZMod 8) * x ^ 4 -
          (4 : ZMod 8) * x ^ 2 * z ^ 2 +
          (9 : ZMod 8) * z ^ 4)
    ∧
    (¬ ∃ x y z : ZMod 125,
      PrimitiveMod5_125 x z = true ∧
        (5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 -
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4)
    ∧
    (¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = N16_Ep_dm1_rhs_plus x z) := by
  exact ⟨N14_E_d3_no_primitive_mod4,
    N14_Ep_d2_no_primitive_mod8,
    N16_E_d5_no_primitive_mod125,
    N16_Ep_dm1_no_primitive_mod16_plus⟩

end MazurLocalObstructionsN14N16
end FLT
```

## How I would use these files

For N=14, create a local-obstruction file parallel to the existing N=10 one, with four native-decide lemmas:

```text
N14_E_d3_no_primitive_mod4
N14_E_dm3_no_primitive_mod27       -- optional / convention-dependent
N14_Ep_d2_no_primitive_mod8
N14_Ep_dm2_no_primitive_mod8       -- optional / convention-dependent
```

Then the global bridge should say that these local obstructions collapse the relevant Selmer groups to the torsion-generated classes.  The finite curve-point conclusion is then:

```text
E14(Q) = {O, (-2,0), (0,0), (1,0)}.
```

For N=16, reuse the N=10 local-obstruction architecture almost verbatim, changing the middle sign on the `d = 5` equation and using the plus-middle dual equation:

```text
N16_E_d5_no_primitive_mod125
N16_Ep_dm1_no_primitive_mod16_plus
```

Then the global bridge should say that the 2-isogeny Selmer groups have the torsion sizes only, giving

```text
E16(Q) = {O, (0,0)}
```

for the exact curve `y^2 = x^3 - x^2 - x`.  If your downstream bridge uses the harmless over-approximation `{u=-1,0,1}`, that is fine, but note that `u = ±1` do not actually give affine rational points on this curve because the right-hand side is negative at `u = -1` and `u = 1`.

## Bottom line

Use these prime powers:

```text
N=14:  4, 8, 27   i.e. primes 2 and 3.
N=16:  125, 16    i.e. primes 5 and 2.
```

They are exactly the kind of finite checks that `native_decide` handles well, and they match the existing N=10 proof strategy: native-decide proves the local failures of the non-torsion covering spaces; a separate descent/Selmer bridge converts those local failures into “rank zero and only the listed torsion points.”
