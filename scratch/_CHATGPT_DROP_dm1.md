# Q1206 (dm1): revised `OrderReduction.lean` with one Mazur-list axiom

## Conclusion

The proposed 7-smooth closure cannot be proved from the current noncyclic exclusions alone. A point of exact order `n` only gives a cyclic subgroup `Z/n`. The exclusions for full odd square torsion, large 2-rank, and specific `Z/2 × Z/d` groups do not rule out the cyclic branch.

So the right A-line architecture is to use one cyclic-order axiom:

```lean
rational_point_order_in_mazur_list :
  HasRationalPointOfOrder E n → MazurOrder n
```

where `MazurOrder n` means `n ∈ {1,2,3,4,5,6,7,8,9,10,12}`. Then every order `n ≥ 17` is excluded immediately.

## Complete revised file

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace FLT
namespace OrderReduction

/--
`HasRationalPointOfOrder E n` means that the rational point group of `E`
contains a point of exact additive order `n`.

If the project already has this definition, delete this definition and use the
project definition instead.
-/
def HasRationalPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/-- The cyclic torsion orders allowed by Mazur's theorem over `ℚ`. -/
def MazurOrder (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
  n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12

/--
Single A-line axiom: a rational point of exact order `n` has order in Mazur's
cyclic list.

This replaces the attempted 7-smooth group-theory closure.  It is exactly the
missing cyclic-order theorem; it is weaker and cleaner than importing a full
classification of the whole rational torsion group.
-/
axiom rational_point_order_in_mazur_list
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ} :
    HasRationalPointOfOrder E n → MazurOrder n

/-- No number at least `17` lies in Mazur's cyclic list. -/
theorem not_mazurOrder_of_ge_17 {n : ℕ} (hn : 17 ≤ n) :
    ¬ MazurOrder n := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega

/--
Main reduction theorem: no rational point can have exact order `n ≥ 17`.
-/
theorem no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n := by
  intro h
  exact not_mazurOrder_of_ge_17 hn
    (rational_point_order_in_mazur_list (E := E) (n := n) h)

/-- Optional predicate for the 7-smooth branch. -/
def SevenSmooth (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7

/--
The 7-smooth hypothesis is no longer used: the Mazur cyclic-order axiom rules
out every exact order `n ≥ 17`, hence also every 7-smooth such `n`.
-/
theorem no_rational_point_of_order_sevenSmooth_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (_h7 : SevenSmooth n) (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n :=
  no_rational_point_of_order_ge_17 (E := E) (n := n) hn

end OrderReduction
end FLT
```

## Integration note

If `OrderReduction.lean` already has project-local definitions for `HasRationalPointOfOrder`, `SevenSmooth`, or the namespace, keep those and replace only the cyclic-order axiom plus the final two theorems. The important design change is that the 7-smooth branch should not try to derive a contradiction from noncyclic torsion exclusions; it should call `rational_point_order_in_mazur_list` and close by `omega`.