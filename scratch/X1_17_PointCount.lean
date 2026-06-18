import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# scratch/X1_17_PointCount.lean

Affine point counts for Sutherland's affine plane model of `X_1(17)`.

Sutherland / Derickx–van Hoeij affine model:

  F17(x,y) =
    -x^4*y + x^3*y^3 + x^3*y
    - x^2*y^4 - x^2*y + x^2
    + x*y^4 - x*y^3 + x*y^2 - x*y
    - y^3 + 2*y^2 - y.

The smooth projective normalization is the modular curve `X_1(17)`.
This file only verifies affine `F_p` solution counts for the displayed
plane model.  Points at infinity and singular/normalization corrections are
a separate geometric layer.
-/

namespace Scratch.X1_17_PointCount

/-- Sutherland's affine polynomial for `X_1(17)`. -/
def F17 {R : Type*} [CommRing R] (x y : R) : R :=
  - x ^ 4 * y
    + x ^ 3 * y ^ 3 + x ^ 3 * y
    - x ^ 2 * y ^ 4 - x ^ 2 * y + x ^ 2
    + x * y ^ 4 - x * y ^ 3 + x * y ^ 2 - x * y
    - y ^ 3 + 2 * y ^ 2 - y

/-- Affine `F_3`-points of the Sutherland plane model. -/
def X1_17_affine_F3_points : Finset (ZMod 3 × ZMod 3) :=
  Finset.univ.filter fun p : ZMod 3 × ZMod 3 =>
    F17 p.1 p.2 = 0

/-- Affine `F_5`-points of the Sutherland plane model. -/
def X1_17_affine_F5_points : Finset (ZMod 5 × ZMod 5) :=
  Finset.univ.filter fun p : ZMod 5 × ZMod 5 =>
    F17 p.1 p.2 = 0

/-- Affine `F_7`-points of the Sutherland plane model. -/
def X1_17_affine_F7_points : Finset (ZMod 7 × ZMod 7) :=
  Finset.univ.filter fun p : ZMod 7 × ZMod 7 =>
    F17 p.1 p.2 = 0

/--
There are exactly `3` affine `F_3`-solutions on the Sutherland plane model.

The solutions are `(0,0)`, `(0,1)`, `(1,1)` over `ZMod 3`.
-/
theorem X1_17_affine_F3_point_count :
    X1_17_affine_F3_points.card = 3 := by
  native_decide

/--
There are exactly `3` affine `F_5`-solutions on the Sutherland plane model.

The solutions are `(0,0)`, `(0,1)`, `(1,1)` over `ZMod 5`.
-/
theorem X1_17_affine_F5_point_count :
    X1_17_affine_F5_points.card = 3 := by
  native_decide

/--
There are exactly `3` affine `F_7`-solutions on the Sutherland plane model.

The solutions are `(0,0)`, `(0,1)`, `(1,1)` over `ZMod 7`.
-/
theorem X1_17_affine_F7_point_count :
    X1_17_affine_F7_points.card = 3 := by
  native_decide

/--
Inline version of the `F_3` count, useful if another file does not want to
unfold `X1_17_affine_F3_points`.
-/
theorem X1_17_affine_F3_point_count_inline :
    (Finset.univ.filter
      (fun p : ZMod 3 × ZMod 3 =>
        - p.1 ^ 4 * p.2
          + p.1 ^ 3 * p.2 ^ 3 + p.1 ^ 3 * p.2
          - p.1 ^ 2 * p.2 ^ 4 - p.1 ^ 2 * p.2 + p.1 ^ 2
          + p.1 * p.2 ^ 4 - p.1 * p.2 ^ 3 + p.1 * p.2 ^ 2 - p.1 * p.2
          - p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 = 0)).card = 3 := by
  native_decide

/--
Inline version of the `F_5` count.
-/
theorem X1_17_affine_F5_point_count_inline :
    (Finset.univ.filter
      (fun p : ZMod 5 × ZMod 5 =>
        - p.1 ^ 4 * p.2
          + p.1 ^ 3 * p.2 ^ 3 + p.1 ^ 3 * p.2
          - p.1 ^ 2 * p.2 ^ 4 - p.1 ^ 2 * p.2 + p.1 ^ 2
          + p.1 * p.2 ^ 4 - p.1 * p.2 ^ 3 + p.1 * p.2 ^ 2 - p.1 * p.2
          - p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 = 0)).card = 3 := by
  native_decide

/--
Inline version of the `F_7` count.
-/
theorem X1_17_affine_F7_point_count_inline :
    (Finset.univ.filter
      (fun p : ZMod 7 × ZMod 7 =>
        - p.1 ^ 4 * p.2
          + p.1 ^ 3 * p.2 ^ 3 + p.1 ^ 3 * p.2
          - p.1 ^ 2 * p.2 ^ 4 - p.1 ^ 2 * p.2 + p.1 ^ 2
          + p.1 * p.2 ^ 4 - p.1 * p.2 ^ 3 + p.1 * p.2 ^ 2 - p.1 * p.2
          - p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 = 0)).card = 3 := by
  native_decide

end Scratch.X1_17_PointCount
