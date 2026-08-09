import FLT.Assumptions.MazurProof.RationalPointsN25QuotientZeta

/-!
# Exact level-25 Euler-factor certificate at three

The level-25 newform candidate has coefficient field
`Q(zeta_10)`, with `zeta_10` satisfying
`z^4 - z^3 + z^2 - z + 1 = 0`.  Its proposed local factor at three is
`1 + z^3 T + 3 z^6 T^2`.  The four embeddings of the coefficient field send
`z` to the powers `z`, `z^3`, `z^7`, and `z^9`.

This file verifies, over an arbitrary commutative ring, that the product of
those four conjugate quadratic factors is the displayed rational degree-eight
polynomial and that its value at one is `71`.  The large identity is an exact
ideal-membership certificate checked by `linear_combination` and `ring`.

The file deliberately does not identify the stored canonical curve with the
newform factor, prove good reduction at three, or assert that this polynomial
is a Frobenius polynomial.  Those are separate modular-geometry seams.  Thus
the certificate is reusable finite algebra without smuggling the missing
global theorem into a definition.
-/

namespace MazurProof.RationalPointsN25NewformEulerCertificate

noncomputable section

open Polynomial

/-- The first local quadratic factor reduces to a cubic representative modulo
the tenth cyclotomic relation.  This keeps the final norm certificate small. -/
theorem first_conjugate_reduce {R : Type*} [CommRing R] (z t : R)
    (hphi : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    1 + z ^ 3 * t + 3 * z ^ 6 * t ^ 2 =
      z ^ 3 * t - 3 * z * t ^ 2 + 1 := by
  linear_combination (3 * z ^ 2 * t ^ 2 + 3 * z * t ^ 2) * hphi

/-- The conjugate obtained from `z ↦ z^3` reduces to degree three in `z`
modulo the tenth cyclotomic relation. -/
theorem second_conjugate_reduce {R : Type*} [CommRing R] (z t : R)
    (hphi : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    1 + z ^ 9 * t + 3 * z ^ 8 * t ^ 2 =
      -3 * z ^ 3 * t ^ 2 - z ^ 3 * t + z ^ 2 * t - z * t + t + 1 := by
  linear_combination
    (z ^ 5 * t + 3 * z ^ 4 * t ^ 2 + z ^ 4 * t +
      3 * z ^ 3 * t ^ 2 - t) * hphi

/-- The conjugate obtained from `z ↦ z^9` reduces to degree three in `z`
modulo the tenth cyclotomic relation.  The `z ↦ z^7` factor is already in
reduced form and needs no companion lemma. -/
theorem fourth_conjugate_reduce {R : Type*} [CommRing R] (z t : R)
    (hphi : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    1 + z ^ 7 * t + 3 * z ^ 4 * t ^ 2 =
      3 * z ^ 3 * t ^ 2 - 3 * z ^ 2 * t ^ 2 - z ^ 2 * t +
        3 * z * t ^ 2 - 3 * t ^ 2 + 1 := by
  linear_combination (z ^ 3 * t + z ^ 2 * t + 3 * t ^ 2) * hphi

/-- Exact norm identity after reducing the four conjugate quadratic factors.
The multiplier supplied to `linear_combination` is the quotient of the
difference by the tenth cyclotomic polynomial, so Lean independently checks
the complete polynomial certificate. -/
theorem reduced_conjugate_product {R : Type*} [CommRing R] (z t : R)
    (hphi : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    (z ^ 3 * t - 3 * z * t ^ 2 + 1) *
      (-3 * z ^ 3 * t ^ 2 - z ^ 3 * t + z ^ 2 * t - z * t + t + 1) *
      (1 + z * t + 3 * z ^ 2 * t ^ 2) *
      (3 * z ^ 3 * t ^ 2 - 3 * z ^ 2 * t ^ 2 - z ^ 2 * t +
        3 * z * t ^ 2 - 3 * t ^ 2 + 1) =
        1 + t - 2 * t ^ 2 - 5 * t ^ 3 + t ^ 4 - 15 * t ^ 5 -
          18 * t ^ 6 + 27 * t ^ 7 + 81 * t ^ 8 := by
  linear_combination
    (-27*z^7*t^7 - 9*z^7*t^6 + 81*z^5*t^8 + 9*z^6*t^6 +
      27*z^5*t^7 - 27*z^4*t^7 - 3*z^5*t^5 - 18*z^4*t^6 +
      27*z^3*t^7 - 2*z^5*t^4 - 9*z^4*t^5 + 18*z^3*t^6 -
      81*z*t^8 + 3*z^4*t^4 + 9*z^3*t^5 + 9*z^2*t^6 -
      27*z*t^7 - 81*t^8 + z^4*t^3 - 3*z^3*t^4 - 9*z^2*t^5 +
      18*z*t^6 - 27*t^7 - z^3*t^3 - 9*z^2*t^4 + 24*z*t^5 +
      18*t^6 - 3*z^2*t^3 + 5*z*t^4 + 15*t^5 - z^2*t^2 +
      2*z*t^3 - t^4 + 2*t^3 - t^2) * hphi

/-- The product of the four unreduced Galois-conjugate local factors is the
rational degree-eight polynomial.  This is the finite algebraic certificate
needed once the newform-to-Jacobian bridge supplies the local factor. -/
theorem conjugate_euler_product {R : Type*} [CommRing R] (z t : R)
    (hphi : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0) :
    (1 + z ^ 3 * t + 3 * z ^ 6 * t ^ 2) *
      (1 + z ^ 9 * t + 3 * z ^ 8 * t ^ 2) *
      (1 + z * t + 3 * z ^ 2 * t ^ 2) *
      (1 + z ^ 7 * t + 3 * z ^ 4 * t ^ 2) =
        1 + t - 2 * t ^ 2 - 5 * t ^ 3 + t ^ 4 - 15 * t ^ 5 -
          18 * t ^ 6 + 27 * t ^ 7 + 81 * t ^ 8 := by
  rw [first_conjugate_reduce z t hphi, second_conjugate_reduce z t hphi,
    fourth_conjugate_reduce z t hphi]
  exact reduced_conjugate_product z t hphi

/-- The rational degree-eight polynomial supplied by the exact conjugate
product at three.  Its Frobenius interpretation remains a separate theorem. -/
def P₂₅AtThree : ℤ[X] :=
  1 + X - C 2 * X ^ 2 - C 5 * X ^ 3 + X ^ 4 - C 15 * X ^ 5 -
    C 18 * X ^ 6 + C 27 * X ^ 7 + C 81 * X ^ 8

/-- The exact level-25 polynomial at three evaluates to seventy-one at one.
Combined with a good-reduction specialization theorem, this is the second
local cardinality needed to eliminate rational two-primary torsion. -/
theorem P₂₅AtThree_eval_one : P₂₅AtThree.eval 1 = 71 := by
  norm_num [P₂₅AtThree]

end


end MazurProof.RationalPointsN25NewformEulerCertificate
