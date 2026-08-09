import FLT.Assumptions.MazurProof.RationalPointsN25TwoPrimeReduction

/-!
# Cardinality bookkeeping for the level-25 reduction maps

The geometric good-reduction argument will provide homomorphisms from the
rational Jacobian into its special fibres.  At the residue characteristic
`p`, only the `p`-primary part of the kernel can survive.  This file isolates
the finite-group bookkeeping that turns those two geometric statements into
the exact divisibility hypotheses used by the two-prime endgame.

No curve, Jacobian, or specialization map is postulated here.  The theorems
apply to arbitrary finite additive groups, so a future geometric layer must
supply the homomorphisms and prove the stated kernel cardinalities.
-/

namespace MazurProof.RationalPointsN25ReductionCardinality

open MazurProof.RationalPointsN25TwoPrimeReduction

/-- The order of a finite additive group is the product of the orders of the
kernel and range of any homomorphism from it.

This is the cardinal form of the first isomorphism theorem.  It is recorded
explicitly because it is the only group-theoretic input needed to pass from a
good-reduction map to a bound on the rational Jacobian order. -/
theorem natCard_eq_kernel_mul_range
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (f : G →+ H) :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  calc
    Nat.card G = Nat.card (G ⧸ f.ker) * Nat.card f.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    _ = Nat.card f.range * Nat.card f.ker := by
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
    _ = Nat.card f.ker * Nat.card f.range := Nat.mul_comm _ _

/-- A finite homomorphism source has order dividing the product of its kernel
order and the order of the ambient target.

The range is a subgroup of the target, so Lagrange's theorem supplies the
remaining divisibility after the kernel-range product formula. -/
theorem natCard_dvd_kernel_mul_codomain
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (f : G →+ H) :
    Nat.card G ∣ Nat.card f.ker * Nat.card H := by
  rw [natCard_eq_kernel_mul_range f]
  exact Nat.mul_dvd_mul_left _ (AddSubgroup.card_addSubgroup_dvd_card f.range)

/-- If the kernel of a finite reduction map has order `p^a` and its target
has order `m`, then the source order divides `p^a * m`.

For a Jacobian with good reduction, the geometric specialization theorem is
expected to prove precisely the kernel hypothesis.  The present result then
removes all further finite-group bookkeeping from that bridge. -/
theorem natCard_dvd_prime_power_mul_of_reduction
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (f : G →+ H) {p a m : ℕ}
    (hker : Nat.card f.ker = p ^ a)
    (htarget : Nat.card H = m) :
    Nat.card G ∣ p ^ a * m := by
  simpa only [hker, htarget] using natCard_dvd_kernel_mul_codomain f

/-- Two reduction maps with 2-primary and 3-primary kernels and targets of
order `71` force the original finite group order to divide `71`.

This is the complete algebraic endgame intended for the level-25 Jacobian.
What remains outside this theorem is geometric: construct the two good-
reduction maps and identify both special-fibre orders with `71`. -/
theorem natCard_dvd_seventy_one_of_two_reductions
    {G H2 H3 : Type*}
    [AddCommGroup G] [AddCommGroup H2] [AddCommGroup H3]
    [Finite G] [Finite H2] [Finite H3]
    (red2 : G →+ H2) (red3 : G →+ H3) {a b : ℕ}
    (hker2 : Nat.card red2.ker = 2 ^ a)
    (hker3 : Nat.card red3.ker = 3 ^ b)
    (htarget2 : Nat.card H2 = 71)
    (htarget3 : Nat.card H3 = 71) :
    Nat.card G ∣ 71 := by
  apply finite_card_dvd_seventy_one_of_two_prime_bounds
  · exact natCard_dvd_prime_power_mul_of_reduction red2 hker2 htarget2
  · exact natCard_dvd_prime_power_mul_of_reduction red3 hker3 htarget3

end MazurProof.RationalPointsN25ReductionCardinality
