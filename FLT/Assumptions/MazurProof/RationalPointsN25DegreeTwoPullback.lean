import FLT.Assumptions.MazurProof.RationalPointsN25ReductionCardinality

/-!
# The degree-two pullback endgame for the level-25 quotient

For a degree-two map of curves, pullback and norm on Jacobians satisfy
`norm ∘ pullback = [2]`.  Pullback is therefore injective as soon as the
source Jacobian has no rational two-torsion.  The two-prime reduction argument
provides exactly that fact because it forces the finite rational group order
to divide the odd prime `71`.

This file proves only the resulting finite-group argument.  It introduces no
curve or Jacobian object: a geometric layer must construct the actual
pullback and norm maps and prove their degree-two composition identity.
-/

namespace MazurProof.RationalPointsN25DegreeTwoPullback

open MazurProof.RationalPointsN25ReductionCardinality

/-- If the order of a finite additive group divides `71`, multiplication by
two is injective on that group.

Indeed, the group order is coprime to two.  Mathlib's finite-group power-map
theorem then makes scalar multiplication by two bijective, hence injective.
This is the precise no-two-torsion consequence needed by the degree-two
Jacobian pullback argument. -/
theorem two_nsmul_injective_of_natCard_dvd_seventy_one
    {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G ∣ 71) :
    Function.Injective (fun x : G ↦ (2 : ℕ) • x) := by
  have hcop : (Nat.card G).Coprime 2 :=
    (by norm_num : Nat.Coprime 71 2).coprime_dvd_left hcard
  exact hcop.nsmul_right_bijective.injective

/-- A homomorphism admitting a left composite equal to multiplication by two
is injective when its finite source order divides `71`.

For the intended degree-two cover, `pull` is Jacobian pullback and `norm` is
the norm map.  Applying `norm` to an equality of pullbacks gives equality
after doubling, which can be cancelled by the preceding odd-order theorem.
-/
theorem pull_injective_of_norm_comp_eq_two_of_natCard_dvd_seventy_one
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G]
    (pull : G →+ H) (norm : H →+ G)
    (hnorm : ∀ x : G, norm (pull x) = (2 : ℕ) • x)
    (hcard : Nat.card G ∣ 71) :
    Function.Injective pull := by
  intro x y hxy
  apply two_nsmul_injective_of_natCard_dvd_seventy_one hcard
  calc
    (2 : ℕ) • x = norm (pull x) := (hnorm x).symm
    _ = norm (pull y) := by rw [hxy]
    _ = (2 : ℕ) • y := hnorm y

/-- Two good-reduction maps followed by the degree-two norm-pullback identity
force the pullback homomorphism to be injective.

The reduction hypotheses first imply that the source order divides `71`;
only then is oddness used to cancel multiplication by two.  This ordering is
important: it avoids the circular argument that tries to deduce oddness from
an injectivity statement that itself requires absence of two-torsion. -/
theorem pull_injective_of_two_reductions_and_norm_comp_eq_two
    {G H H2 H3 : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [AddCommGroup H2] [AddCommGroup H3]
    [Finite G] [Finite H2] [Finite H3]
    (pull : G →+ H) (norm : H →+ G)
    (red2 : G →+ H2) (red3 : G →+ H3) {a b : ℕ}
    (hnorm : ∀ x : G, norm (pull x) = (2 : ℕ) • x)
    (hker2 : Nat.card red2.ker = 2 ^ a)
    (hker3 : Nat.card red3.ker = 3 ^ b)
    (htarget2 : Nat.card H2 = 71)
    (htarget3 : Nat.card H3 = 71) :
    Function.Injective pull := by
  apply pull_injective_of_norm_comp_eq_two_of_natCard_dvd_seventy_one
      pull norm hnorm
  exact natCard_dvd_seventy_one_of_two_reductions
    red2 red3 hker2 hker3 htarget2 htarget3

end MazurProof.RationalPointsN25DegreeTwoPullback
