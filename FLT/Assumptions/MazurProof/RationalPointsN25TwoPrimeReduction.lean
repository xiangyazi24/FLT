import Mathlib

/-!
# The two-prime torsion endgame for the level-25 Jacobian

Good reduction at a prime `p` controls the prime-to-`p` part of rational
torsion.  Consequently a reduction at two can leave an unknown power of two
in the rational group order, while a reduction at three can leave an unknown
power of three.  If both special-fibre orders divide the same integer `m`, the
rational group order divides both `2^a*m` and `3^b*m` for some exponents.

This file proves the exact elementary arithmetic that combines those two
bounds.  It does not postulate a Jacobian or a reduction map: the future
geometric specialization layer must supply the two divisibility hypotheses.
-/

namespace MazurProof.RationalPointsN25TwoPrimeReduction

/-- If an integer divides both a power-of-two multiple and a power-of-three
multiple of the same integer `m`, then it already divides `m`.

The proof takes the gcd of the two bounds.  Powers of two and three are
coprime, so that gcd is exactly `m`.  This is the reusable arithmetic core of
the two-good-reduction argument. -/
theorem dvd_common_factor_of_two_and_three_primary_bounds
    {n m a b : ℕ} (h2 : n ∣ 2 ^ a * m) (h3 : n ∣ 3 ^ b * m) : n ∣ m := by
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) :=
    Nat.coprime_pow_primes a b Nat.prime_two Nat.prime_three (by norm_num)
  have hgcd : n ∣ Nat.gcd (2 ^ a * m) (3 ^ b * m) := Nat.dvd_gcd h2 h3
  simpa [Nat.gcd_mul_right, hcop] using hgcd

/-- Two local bounds with common factor `71` force the cardinality of any
finite type to divide `71`.  For the N=25 route, the type is intended to be
`Jac(C)(Q)` after rank zero has made it finite; good-reduction specialization
at two and three must provide the two hypotheses. -/
theorem finite_card_dvd_seventy_one_of_two_prime_bounds
    {G : Type*} [Finite G] {a b : ℕ}
    (h2 : Nat.card G ∣ 2 ^ a * 71)
    (h3 : Nat.card G ∣ 3 ^ b * 71) :
    Nat.card G ∣ 71 := by
  exact dvd_common_factor_of_two_and_three_primary_bounds h2 h3

end MazurProof.RationalPointsN25TwoPrimeReduction
