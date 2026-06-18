import FLT.EllipticCurve.Torsion
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic

/-!
# Refactored Mazur torsion bound skeleton

This file proves

    #(E(ℚ)_tors) ≤ 16

from the following clean axiom split:

1. torsion decomposition;
2. first invariant factor bound `m ≤ 2`;
3. cyclic order classification `N ≤ 10 ∨ N = 12`;
4. no `ZMod 2 × ZMod 10`;
5. no `ZMod 2 × ZMod 12`.

The point of the refactor is that `Z/2 × Z/14` and `Z/2 × Z/16`
are excluded by the cyclic-order axiom, because they contain points of
order `14` and `16`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace FLT
namespace TorsionBound

/-- Rational points of a Weierstrass elliptic curve. -/
abbrev RatPoints (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℚ).Point

/-- The rational torsion subgroup as a type. -/
abbrev RatTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  AddCommGroup.torsion (RatPoints E)

/-- The rational torsion subgroup as a set. -/
abbrev RatTorsionSet (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Set (RatPoints E) :=
  (AddCommGroup.torsion (RatPoints E) : Set (RatPoints E))

/-- `E(ℚ)` has a point of exact additive order `N`. -/
def HasPointOfOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) : Prop :=
  ∃ P : RatPoints E, addOrderOf P = N

/--
Torsion decomposition.

This is the data-bearing version of:

    E(ℚ)_tors ≅ ZMod m × ZMod n,  m ∣ n.

The final equality records the cardinality consequence, so the main theorem
does not have to fight `Set.ncard`/subgroup cardinality API.
-/
axiom torsion_decomp
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m n : ℕ,
      1 ≤ m ∧
      1 ≤ n ∧
      m ∣ n ∧
      Nonempty (RatTorsion E ≃+ (ZMod m × ZMod n)) ∧
      (RatTorsionSet E).ncard = m * n

/--
First invariant factor bound.

This is the output of the Weil-pairing/roots-of-unity argument.
-/
axiom torsion_first_factor_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m n : ℕ}
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hdiv : m ∣ n)
    (hdecomp : Nonempty (RatTorsion E ≃+ (ZMod m × ZMod n))) :
    m ≤ 2

/--
Pure group-theory bridge.

From a decomposition with second invariant factor `n`, obtain a rational point
of exact order `n`.

Eventually this should be proved by taking the preimage of
`(0, 1) : ZMod m × ZMod n`.
-/
axiom point_of_order_second_factor
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m n : ℕ}
    (hn : 1 ≤ n)
    (hdecomp : Nonempty (RatTorsion E ≃+ (ZMod m × ZMod n))) :
    HasPointOfOrder E n

/--
Cyclic Mazur/Kubert classification in the exact form needed here.

A rational point of finite order `N ≥ 1` has

    N ∈ {1,2,3,4,5,6,7,8,9,10,12}.

For the cardinality proof, this is used only through the derived consequence
`N ≤ 12`.
-/
axiom cyclic_order_allowed
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ}
    (hN : 1 ≤ N)
    (hP : HasPointOfOrder E N) :
    N ≤ 10 ∨ N = 12

/-- No rational elliptic curve has torsion subgroup `ZMod 2 × ZMod 10`. -/
axiom no_Z2_cross_Z10
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ Nonempty (RatTorsion E ≃+ (ZMod 2 × ZMod 10))

/-- No rational elliptic curve has torsion subgroup `ZMod 2 × ZMod 12`. -/
axiom no_Z2_cross_Z12
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ Nonempty (RatTorsion E ≃+ (ZMod 2 × ZMod 12))

/-- Convenient derived form of the cyclic classification. -/
theorem cyclic_order_le_twelve
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ}
    (hN : 1 ≤ N)
    (hP : HasPointOfOrder E N) :
    N ≤ 12 := by
  rcases cyclic_order_allowed E hN hP with hle10 | h12
  · omega
  · omega

/--
In the noncyclic case `T ≅ ZMod 2 × ZMod n`, the second invariant factor
satisfies `n ≤ 8`.

Proof:
* the group contains a point of order `n`;
* cyclic classification gives `n ≤ 12`;
* `2 ∣ n`;
* the explicit noncyclic exclusions rule out `n = 10` and `n = 12`;
* hence `n ≤ 8`.
-/
theorem noncyclic_second_factor_le_eight
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ}
    (hn : 1 ≤ n)
    (heven : 2 ∣ n)
    (hdecomp : Nonempty (RatTorsion E ≃+ (ZMod 2 × ZMod n))) :
    n ≤ 8 := by
  have hpoint : HasPointOfOrder E n :=
    point_of_order_second_factor E hn hdecomp

  have hcyc : n ≤ 10 ∨ n = 12 :=
    cyclic_order_allowed E hn hpoint

  have hn_ne_10 : n ≠ 10 := by
    intro hn10
    subst n
    exact no_Z2_cross_Z10 E hdecomp

  have hn_ne_12 : n ≠ 12 := by
    intro hn12
    subst n
    exact no_Z2_cross_Z12 E hdecomp

  rcases heven with ⟨k, hk⟩
  subst n

  rcases hcyc with hle10 | h12
  · have hnot10 : 2 * k ≠ 10 := hn_ne_10
    omega
  · exact (hn_ne_12 h12).elim

/--
Mazur's torsion cardinality bound over `ℚ`.

This has the same target shape as the current FLT assumption:

    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16.
-/
theorem mazur_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  change (RatTorsionSet E).ncard ≤ 16

  rcases torsion_decomp E with
    ⟨m, n, hm, hn, hdiv, hdecomp, hcard⟩

  have hmle : m ≤ 2 :=
    torsion_first_factor_le_two E hm hn hdiv hdecomp

  have hm_cases : m = 1 ∨ m = 2 := by
    omega

  rcases hm_cases with hmonic | hnoncyclic

  · -- Cyclic case: `T ≅ ZMod 1 × ZMod n`, so `T` has a point of order `n`.
    subst m

    have hpoint : HasPointOfOrder E n :=
      point_of_order_second_factor E hn hdecomp

    have hnle12 : n ≤ 12 :=
      cyclic_order_le_twelve E hn hpoint

    rw [hcard]
    omega

  · -- Noncyclic case: `T ≅ ZMod 2 × ZMod n`.
    subst m

    have hnle8 : n ≤ 8 :=
      noncyclic_second_factor_le_eight E hn hdiv hdecomp

    rw [hcard]
    omega

end TorsionBound
end FLT
```
```lean
cyclic_order_allowed :
  N ≤ 10 ∨ N = 12
```
```lean
N ≤ 12
