import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF3
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic.ComputeDegree

/-!
# Hilbert polynomial of the level-25 quadric-cubic model

A regular sequence of degrees two and three in projective three-space has
Hilbert series

`(1 - T²)(1 - T³) / (1 - T)⁴`.

This file certifies the arithmetic part of that calculation.  The numerator
has degree five, its Hilbert polynomial is `6T - 3`, and the constant term
therefore gives the genus candidate `1 - (-3) = 4`.

This is deliberately not a scheme-level genus theorem.  Such a theorem still
has to connect the explicit quadric and cubic to a regular codimension-two
closed subscheme and identify its scheme-theoretic Hilbert polynomial with
the series used here.  Mathlib currently has no general projective-curve
genus interface supplying that final bridge.
-/

namespace MazurProof.RationalPointsN25QuotientHilbert

noncomputable section

open Polynomial

/-! ## Complete-intersection numerator -/

/-- The numerator contributed by equations of degrees two and three in a
four-variable homogeneous coordinate ring. -/
def completeIntersectionHilbertNumerator25 : ℚ[X] :=
  (1 - X ^ 2) * (1 - X ^ 3)

/-- The numerator expands into the four shifts used by the Koszul resolution:
the ambient term, the two equation terms, and their overlap. -/
theorem completeIntersectionHilbertNumerator25_expanded :
    completeIntersectionHilbertNumerator25 =
      1 - X ^ 2 - X ^ 3 + X ^ 5 := by
  simp only [completeIntersectionHilbertNumerator25]
  ring

/-- The top shift in the complete-intersection numerator is five. -/
theorem completeIntersectionHilbertNumerator25_natDegree :
    completeIntersectionHilbertNumerator25.natDegree = 5 := by
  simp only [completeIntersectionHilbertNumerator25]
  compute_degree <;> norm_num

/-! ## Hilbert polynomial and genus arithmetic -/

/-- The Hilbert polynomial encoded by the standard `(2,3)` complete-
intersection series in four variables is `6T-3`.

The proof uses linearity to split the four Koszul shifts.  Each shift is then
the explicit third ascending Pochhammer polynomial from Mathlib's Hilbert
polynomial formula; no coefficient table or finite search is involved. -/
theorem completeIntersectionHilbertPolynomial25 :
    hilbertPoly completeIntersectionHilbertNumerator25 4 = 6 * X - 3 := by
  change (hilbertPoly_linearMap ℚ 4) completeIntersectionHilbertNumerator25 =
    6 * X - 3
  rw [completeIntersectionHilbertNumerator25_expanded]
  rw [map_add, map_sub, map_sub]
  change hilbertPoly (1 : ℚ[X]) 4 - hilbertPoly (X ^ 2) 4 -
      hilbertPoly (X ^ 3) 4 + hilbertPoly (X ^ 5) 4 = _
  rw [show (1 : ℚ[X]) = X ^ 0 by simp]
  simp only [hilbertPoly_X_pow_succ]

  -- Expand the four third Pochhammer polynomials structurally.
  norm_num [preHilbertPoly, ascPochhammer, Polynomial.smul_eq_C_mul,
    Nat.factorial]
  simp only [Polynomial.C_ofNat]

  -- Record the two rational scalar simplifications left after normalization.
  have h18 : C (1 / 6 : ℚ) * (18 : ℚ[X]) = 3 := by
    change C (1 / 6 : ℚ) * C (18 : ℚ) = C (3 : ℚ)
    rw [← Polynomial.C_mul]
    norm_num
  have h36 : C (1 / 6 : ℚ) * (36 : ℚ[X]) = 6 := by
    change C (1 / 6 : ℚ) * C (36 : ℚ) = C (6 : ℚ)
    rw [← Polynomial.C_mul]
    norm_num

  -- Cancellation of the cubic and quadratic terms leaves degree one.
  ring_nf
  rw [h18]
  calc
    -3 + C (1 / 6 : ℚ) * X * 36 =
        -3 + X * (C (1 / 6 : ℚ) * 36) := by ring
    _ = -3 + X * 6 := by rw [h36]

/-- Coefficients of the corresponding Hilbert series eventually equal
`6n-3`.  The degree-five bound is the exact range supplied by Mathlib's
general coefficient-to-Hilbert-polynomial theorem. -/
theorem completeIntersectionHilbertSeries25_eventually
    (n : ℕ) (hn : completeIntersectionHilbertNumerator25.natDegree < n) :
    (completeIntersectionHilbertNumerator25 *
        PowerSeries.invOneSubPow ℚ 4 : PowerSeries ℚ).coeff n =
      6 * (n : ℚ) - 3 := by
  rw [coeff_mul_invOneSubPow_eq_hilbertPoly_eval 4 hn,
    completeIntersectionHilbertPolynomial25]
  simp

/-- The constant term of `6T-3` gives arithmetic genus four under the standard
curve convention `P(n)=deg(C)n+1-g`.  This theorem certifies only that final
arithmetic extraction, not the missing scheme-theoretic identification. -/
theorem completeIntersectionArithmeticGenus25 :
    1 - (hilbertPoly completeIntersectionHilbertNumerator25 4).coeff 0 =
      (4 : ℚ) := by
  rw [completeIntersectionHilbertPolynomial25]
  norm_num

end

end MazurProof.RationalPointsN25QuotientHilbert
