/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Local obstruction checks for the 2-isogeny descent on `20.a4`

This file verifies the finite local obstruction checks for

    E  : y² = x³ + x² - x
    E' : Y² = X³ - 2X² + 5X

using `native_decide`.

The global conclusion `rank = 0` still requires formal 2-isogeny descent
machinery, which is not supplied here.
-/

namespace FLT
namespace C20LocalObstructions

/-!
## Primitive residue conditions

For the mod `125` check, "primitive" means not both coordinates are divisible
by `5`.

For the mod `16` check, "primitive" means not both coordinates are divisible
by `2`.

These are expressed using `ZMod.val`.
-/

def NonzeroMod5_125 (a : ZMod 125) : Bool :=
  decide (a.val % 5 ≠ 0)

def PrimitiveMod5_125 (x z : ZMod 125) : Bool :=
  NonzeroMod5_125 x || NonzeroMod5_125 z

def NonzeroMod5_25 (a : ZMod 25) : Bool :=
  decide (a.val % 5 ≠ 0)

def NonzeroMod2_16 (a : ZMod 16) : Bool :=
  decide (a.val % 2 ≠ 0)

def PrimitiveMod2_16 (x z : ZMod 16) : Bool :=
  NonzeroMod2_16 x || NonzeroMod2_16 z

/-!
## The `E`, `d = 5` obstruction modulo `125`

For

    E : y² = x³ + x² - x,

the 2-isogeny descent homogeneous space for `d = 5` is

    5 W² = 25 U⁴ + 5 U² V² - V⁴.

The local obstruction is that there is no primitive solution modulo `125`.
-/

set_option maxHeartbeats 0 in
theorem E_d5_no_primitive_mod125 :
    ¬ ∃ x y z : ZMod 125,
      PrimitiveMod5_125 x z = true ∧
        (5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 +
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4 := by
  native_decide

/-!
A smaller square-valuation sub-check.

After the standard descent reduction, one reaches an impossibility of the form

    y² = ±5 x⁴ mod 25

with `x` a unit modulo `5`.  Both signs are included, since the sign depends
on the convention for the homogeneous space.
-/

set_option maxHeartbeats 0 in
theorem no_square_eq_pos_five_times_unit_fourth_mod25 :
    ¬ ∃ x y : ZMod 25,
      NonzeroMod5_25 x = true ∧
        y ^ 2 = (5 : ZMod 25) * x ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem no_square_eq_neg_five_times_unit_fourth_mod25 :
    ¬ ∃ x y : ZMod 25,
      NonzeroMod5_25 x = true ∧
        y ^ 2 = (-5 : ZMod 25) * x ^ 4 := by
  native_decide

/-!
## The `E'`, `d' = -1` obstruction

For

    E' : Y² = X³ - 2X² + 5X,

one convention gives the quartic obstruction

    y² = -x⁴ + 2x²z² - 5z⁴.

The obstruction is visible modulo `16`, not modulo `8`.
-/

def Ep_dm1_rhs_plus (x z : ZMod 16) : ZMod 16 :=
  - (x ^ 4) +
    (2 : ZMod 16) * x ^ 2 * z ^ 2 -
    (5 : ZMod 16) * z ^ 4

set_option maxHeartbeats 0 in
theorem Ep_dm1_no_primitive_mod16_plus :
    ¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = Ep_dm1_rhs_plus x z := by
  native_decide

/-!
The other common sign convention for the same `d' = -1` space is

    y² = -x⁴ - 2x²z² - 5z⁴.

This is also obstructed modulo `16`.
-/

def Ep_dm1_rhs_minus (x z : ZMod 16) : ZMod 16 :=
  - (x ^ 4) -
    (2 : ZMod 16) * x ^ 2 * z ^ 2 -
    (5 : ZMod 16) * z ^ 4

set_option maxHeartbeats 0 in
theorem Ep_dm1_no_primitive_mod16_minus :
    ¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = Ep_dm1_rhs_minus x z := by
  native_decide

/-!
For reference: the corresponding `mod 8` statement with the `+2x²z²`
convention is false.  This theorem records an explicit counterexample.

    x = 1, z = 1, y = 2.
-/

theorem Ep_dm1_mod8_plus_has_solution :
    ∃ x y z : ZMod 8,
      ((x.val % 2 ≠ 0) ∨ (z.val % 2 ≠ 0)) ∧
        y ^ 2 =
          - (x ^ 4) +
          (2 : ZMod 8) * x ^ 2 * z ^ 2 -
          (5 : ZMod 8) * z ^ 4 := by
  refine ⟨1, 2, 1, ?_⟩
  native_decide

/-!
## Package the verified finite checks
-/

theorem local_obstructions_verified :
    (¬ ∃ x y z : ZMod 125,
      PrimitiveMod5_125 x z = true ∧
        (5 : ZMod 125) * y ^ 2 =
          (25 : ZMod 125) * x ^ 4 +
          (5 : ZMod 125) * x ^ 2 * z ^ 2 -
          z ^ 4)
    ∧
    (¬ ∃ x y z : ZMod 16,
      PrimitiveMod2_16 x z = true ∧
        y ^ 2 = Ep_dm1_rhs_plus x z) := by
  exact ⟨E_d5_no_primitive_mod125, Ep_dm1_no_primitive_mod16_plus⟩

/-!
## Placeholder for the global descent conclusion

Mathlib/FLT does not yet have the 2-isogeny descent machinery connecting these
finite local obstruction checks to the Mordell-Weil rank computation.
-/

/-- The rank of curve 20.a4 is zero. This follows from the 2-isogeny descent
checked in local_obstructions_verified, but the formal descent bridge is not yet
in Mathlib. -/

end C20LocalObstructions
end FLT
