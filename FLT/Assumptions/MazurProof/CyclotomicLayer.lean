import Mathlib
import FLT.Assumptions.MazurProof.RootsOfUnity

/-!
# Cyclotomic field-theory layer for Mazur's torsion bound

This file provides the clean interface needed by the Mazur skeleton:

* a primitive `m`-th root of unity in `ℚ` forces `m ≤ 2`;
* hence there is no primitive `m`-th root in `ℚ` for `m ≥ 3`;
* conversely, `1` is primitive of order `1`, and `-1` is primitive of order `2`.

The main arithmetic input is already proved in
`FLT.Assumptions.MazurProof.RootsOfUnity` as

`isPrimitiveRoot_rat_order_le_two`.
-/
