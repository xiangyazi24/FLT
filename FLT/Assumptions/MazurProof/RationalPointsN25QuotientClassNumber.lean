import FLT.Assumptions.MazurProof.CurveZetaClassNumber
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientZetaThree

/-!
# The N25 divisor-zeta to Picard-cardinality bridge

This file specializes the general divisor-count class-number theorem to the
characteristic-three level-25 quotient.  It does not assume that the Picard
cardinality is 71.  The lower-level theorem accepts equality of reciprocal
numerators; the semantic theorem derives that equality from two geometric
inputs:

1. effective divisors of every degree map to the finite degree-zero Picard
   class set, with the Riemann--Roch complete-linear-system fibre sizes;
2. the effective-divisor series equals the independently certified N25
   point-count zeta series.

The first input is the future Picard/Riemann--Roch construction.  The second
is the future Euler-product identification between closed points and effective
divisors.  Once they are supplied, the numerical conclusion follows from the
proved general class-number formula, not from a Jacobian-cardinality axiom.
-/

namespace MazurProof.RationalPointsN25QuotientClassNumber

open CurveZetaClassNumber
open RationalPointsN25QuotientZeta
open RationalPointsN25QuotientZetaThree

/-! ## The certified point-count zeta series

The reciprocal numerator obtained from the four characteristic-three point
counts determines a formal rational series by dividing by
`(1-T)(1-3T)`.  Keeping this series separate from the effective-divisor zeta
series makes the remaining Euler-product theorem visible: geometry must prove
that the two independently defined series agree.
-/

/-- The point-count zeta series determined by the certified genus-four
reciprocal numerator at three.  The inverse denominator is the formal inverse
with constant coefficient one, so this definition involves no division of
integer coefficients. -/
noncomputable def certifiedPointZetaSeries25Three : PowerSeries ℤ :=
  zetaDenominatorInverse 3 *
    (genusFourReciprocalNumerator 3 1 (-2) (-5) 1 : PowerSeries ℤ)

/-- Multiplying the certified point-count series by the zeta denominator
recovers its reciprocal numerator.  This is the formal-series counterpart of
the rational-function identity `Z(T)=P(T)/((1-T)(1-3T))`. -/
theorem zetaDenominator_mul_certifiedPointZetaSeries25Three :
    zetaDenominator 3 * certifiedPointZetaSeries25Three =
      (genusFourReciprocalNumerator 3 1 (-2) (-5) 1 : PowerSeries ℤ) := by
  rw [certifiedPointZetaSeries25Three, ← mul_assoc,
    zetaDenominator_mul_inverse, one_mul]

/-! ## From the Euler product to the class number -/

/-- The exact semantic consumer for the characteristic-three N25 fibre.

`Pic` is intended to be `Pic^0` of the smooth projective fibre,
`Effective n` its effective divisors of degree `n`, and `classOf` the divisor
class translated to degree zero using a rational cusp. -/
theorem picardZero_card_eq_seventy_one_of_divisor_zeta
    {Pic : Type*} [Fintype Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (hRRfiber : ∀ n, 7 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard 3 (n + 1 - 4))
    (hZeta :
      truncatedNumerator 3 (fun d => Fintype.card (Effective d)) 4 =
        genusFourReciprocalNumerator 3 1 (-2) (-5) 1) :
    Fintype.card Pic = 71 := by
  have hclass := rr_fiber_numerator_eval_one Effective classOf 3 4
    (by norm_num) (by norm_num) (by simpa using hRRfiber)
  norm_num at hclass
  rw [hZeta] at hclass
  have heval :
      (genusFourReciprocalNumerator 3 1 (-2) (-5) 1).eval 1 = 71 := by
    simpa [RationalPointsN25QuotientZetaThree.q] using
      genusFourReciprocalNumerator_eval_one
  rw [heval] at hclass
  exact_mod_cast hclass.symm

/-- The semantic characteristic-three consumer: if the effective-divisor
generating series equals the independently certified point-count zeta series,
then Riemann--Roch forces the degree-zero Picard group to have cardinality 71.

The hypothesis `hEuler` is exactly the geometric Euler-product boundary.  The
proof first recovers equality of the two polynomial numerators coefficient by
coefficient, then invokes the already proved divisor class-number formula. -/
theorem picardZero_card_eq_seventy_one_of_euler_product
    {Pic : Type*} [Fintype Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (hRRfiber : ∀ n, 7 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard 3 (n + 1 - 4))
    (hEuler :
      divisorZetaSeries (fun d => Fintype.card (Effective d)) =
        certifiedPointZetaSeries25Three) :
    Fintype.card Pic = 71 := by
  have hrat := rr_fiber_zeta_rationality Effective classOf 3 4
    (by norm_num) (by simpa using hRRfiber)
  rw [hEuler] at hrat
  change zetaDenominator (3 : ℤ) * certifiedPointZetaSeries25Three =
    (truncatedNumerator (3 : ℤ)
      (fun d => Fintype.card (Effective d)) 4 : PowerSeries ℤ) at hrat
  rw [zetaDenominator_mul_certifiedPointZetaSeries25Three] at hrat
  have hNumerator :
      truncatedNumerator 3 (fun d => Fintype.card (Effective d)) 4 =
        genusFourReciprocalNumerator 3 1 (-2) (-5) 1 := by
    ext n
    have hcoeff := congrArg (PowerSeries.coeff n) hrat
    simpa only [Polynomial.coeff_coe] using hcoeff.symm
  exact picardZero_card_eq_seventy_one_of_divisor_zeta Effective classOf
    hRRfiber hNumerator

end MazurProof.RationalPointsN25QuotientClassNumber
