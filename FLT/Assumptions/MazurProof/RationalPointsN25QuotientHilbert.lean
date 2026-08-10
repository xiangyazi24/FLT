import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF3
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoGradedAlgebra
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic.ComputeDegree

/-!
# Hilbert polynomial of the level-25 quadric-cubic model

The binary canonical equations now have a proved, explicit Koszul resolution
in every homogeneous degree.  The corresponding shifts give the Hilbert
series

`(1 - T²)(1 - T³) / (1 - T)⁴`.

This file first proves that the actual literal quotient pieces are
finite-dimensional and that their finranks satisfy the alternating identity
forced by the degreewise Koszul resolution.  It then certifies the arithmetic
of those shifts.  The numerator has degree five, its Hilbert polynomial is
`6T - 3`, and the constant term therefore gives the genus candidate
`1 - (-3) = 4`.

The presented cokernel pieces have now been identified with the literal
degreewise images in `S/(Q,C)` and packaged as its internal graded-algebra
structure.  This is nevertheless deliberately not a scheme-level genus
theorem: the graded resolution still has to be sheafified on `Proj` and
compared with the scheme-theoretic Hilbert polynomial.  Mathlib currently has
no general projective-curve genus interface supplying that final bridge.
-/

namespace MazurProof.RationalPointsN25QuotientHilbert

noncomputable section

open Polynomial
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading

/-! ## Finite-dimensionality and the actual graded Hilbert function -/

/-- Every shifted homogeneous polynomial piece is finite-dimensional.  A
degree condition leaves only finitely many exponent vectors, and the
homogeneous submodule is the finitely supported module on that finite set. -/
noncomputable instance shiftedPiece_finite (debt n : ℕ) :
    Module.Finite k (shiftedPiece debt n) := by
  by_cases hdegree : debt ≤ n
  · rw [shiftedPiece, if_pos hdegree,
      MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    let A := {d : Fin 4 →₀ ℕ | d.degree = n - debt}
    have hA : A.Finite :=
      (Finsupp.finite_of_degree_le (n - debt)).subset (by
        intro d hd
        exact le_of_eq hd)
    letI : Finite A := hA
    exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp A).symm
  · rw [shiftedPiece, if_neg hdegree]
    infer_instance

/-- A degree-`n` piece of `S(-debt)` has the stars-and-bars dimension for
monomials of degree `n-debt` in four variables, and vanishes below the shift. -/
theorem shiftedPiece_finrank (debt n : ℕ) :
    Module.finrank k (shiftedPiece debt n) =
      if debt ≤ n then (n - debt + 3).choose 3 else 0 := by
  by_cases hdegree : debt ≤ n
  · rw [shiftedPiece, if_pos hdegree,
      MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    let A := {d : Fin 4 →₀ ℕ | d.degree = n - debt}
    have hA : A.Finite :=
      (Finsupp.finite_of_degree_le (n - debt)).subset (by
        intro d hd
        exact le_of_eq hd)
    letI : Finite A := hA
    letI : Fintype A := Fintype.ofFinite A
    change Module.finrank k (Finsupp.supported k k A) = _
    rw [(Finsupp.supportedEquivFinsupp A).finrank_eq,
      Module.finrank_finsupp_self, if_pos hdegree]
    have hAeq :
        A = (Finset.finsuppAntidiag (Finset.univ : Finset (Fin 4))
          (n - debt) : Set (Fin 4 →₀ ℕ)) := by
      ext d
      simp only [A, Set.mem_setOf_eq, Finset.mem_coe,
        Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
      change (∑ i ∈ d.support, d i) = n - debt ↔
        (∑ i : Fin 4, d i) = n - debt
      have hsum : (∑ i ∈ d.support, d i) = ∑ i : Fin 4, d i := by
        apply Finset.sum_subset (Finset.subset_univ d.support)
        intro i _ hi
        exact Finsupp.notMem_support_iff.mp hi
      rw [hsum]
    have hFintypeCard : Fintype.card A =
        (Finset.finsuppAntidiag (Finset.univ : Finset (Fin 4))
          (n - debt)).card := by
      calc
        Fintype.card A = Fintype.card
            (Finset.finsuppAntidiag (Finset.univ : Finset (Fin 4))
              (n - debt)) :=
          Fintype.card_congr (Equiv.setCongr hAeq)
        _ = _ := Fintype.card_coe _
    rw [hFintypeCard]
    have hcard := Finset.card_finsuppAntidiag_nat_eq_choose
      (s := (Finset.univ : Finset (Fin 4))) (n - debt)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    rw [hcard]
    rw [show 4 + (n - debt) - 1 = n - debt + 3 by omega]
    exact Nat.choose_symm
      (n := n - debt + 3) (k := 3) (by omega)
  · rw [shiftedPiece, if_neg hdegree, if_neg hdegree]
    simp

/-- The literal degree piece in the actual quotient ring is
finite-dimensional, by the proved equivalence with the Koszul cokernel. -/
noncomputable instance literalConePiece_finite (n : ℕ) :
    Module.Finite k (literalConePiece n) :=
  Module.Finite.equiv (canonicalConePieceLinearEquiv n)

/-- Degreewise Koszul exactness gives the alternating finrank identity for
the actual literal quotient piece.  This is the coefficient-level Hilbert
function statement before evaluating the dimensions of the four shifted
ambient pieces. -/
theorem literalConePiece_finrank (n : ℕ) :
    Module.finrank k (literalConePiece n) +
        Module.finrank k (shiftedPiece 2 n) +
        Module.finrank k (shiftedPiece 3 n) =
      Module.finrank k (shiftedPiece 0 n) +
        Module.finrank k (shiftedPiece 5 n) := by
  have hEquiv :
      Module.finrank k (canonicalConePiece n) =
        Module.finrank k (literalConePiece n) :=
    (canonicalConePieceLinearEquiv n).finrank_eq
  have hQuotient :
      Module.finrank k (canonicalConePiece n) +
          Module.finrank k (LinearMap.range (gradedKoszulMiddle n)) =
        Module.finrank k (shiftedPiece 0 n) := by
    exact Submodule.finrank_quotient_add_finrank
      (LinearMap.range (gradedKoszulMiddle n))
  have hMiddle :
      Module.finrank k (LinearMap.range (gradedKoszulMiddle n)) +
          Module.finrank k (LinearMap.ker (gradedKoszulMiddle n)) =
        Module.finrank k
          (shiftedPiece 2 n × shiftedPiece 3 n) :=
    LinearMap.finrank_range_add_finrank_ker (gradedKoszulMiddle n)
  have hKernel :
      Module.finrank k (LinearMap.ker (gradedKoszulMiddle n)) =
        Module.finrank k (shiftedPiece 5 n) := by
    rw [(gradedKoszul_exact_top_middle n).linearMap_ker_eq]
    exact LinearMap.finrank_range_of_inj
      (gradedKoszulTop_injective n)
  rw [Module.finrank_prod] at hMiddle
  omega

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

/-- In every degree, the finrank of the literal piece of the actual quotient
ring is exactly the corresponding coefficient of the complete-intersection
Hilbert series.  The proof combines Koszul rank-nullity with the structural
monomial count for each shifted ambient piece. -/
theorem literalConePiece_finrank_eq_hilbertSeries_coeff (n : ℕ) :
    (Module.finrank k (literalConePiece n) : ℚ) =
      (completeIntersectionHilbertNumerator25 *
        PowerSeries.invOneSubPow ℚ 4 : PowerSeries ℚ).coeff n := by
  have hrank := literalConePiece_finrank n
  rw [shiftedPiece_finrank, shiftedPiece_finrank,
    shiftedPiece_finrank, shiftedPiece_finrank] at hrank
  rw [completeIntersectionHilbertNumerator25_expanded]
  push_cast
  change _ = PowerSeries.coeff n
    (((1 : PowerSeries ℚ) - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
      PowerSeries.X ^ 5) * (PowerSeries.invOneSubPow ℚ 4).val)
  rw [add_mul, sub_mul, sub_mul, map_add, map_sub, map_sub]
  simp only [one_mul]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul']
  simp only [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk]
  simp only [Nat.zero_le, if_true, Nat.sub_zero] at hrank
  have hrankQ :
      (Module.finrank k (literalConePiece n) : ℚ) +
          (if 2 ≤ n then ((3 + (n - 2)).choose 3 : ℚ) else 0) +
          (if 3 ≤ n then ((3 + (n - 3)).choose 3 : ℚ) else 0) =
        ((3 + n).choose 3 : ℚ) +
          (if 5 ≤ n then ((3 + (n - 5)).choose 3 : ℚ) else 0) := by
    exact_mod_cast (show
      Module.finrank k (literalConePiece n) +
          (if 2 ≤ n then (3 + (n - 2)).choose 3 else 0) +
          (if 3 ≤ n then (3 + (n - 3)).choose 3 else 0) =
        (3 + n).choose 3 +
          (if 5 ≤ n then (3 + (n - 5)).choose 3 else 0) by
      simpa [Nat.add_comm] using hrank)
  linarith

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

/-- Above the degree-five numerator bound, the actual quotient piece has
dimension `6n-3`.  Thus the graded coordinate ring itself, not merely a
formal candidate series, has the expected eventual Hilbert function. -/
theorem literalConePiece_finrank_eventually
    (n : ℕ) (hn : completeIntersectionHilbertNumerator25.natDegree < n) :
    (Module.finrank k (literalConePiece n) : ℚ) = 6 * (n : ℚ) - 3 := by
  rw [literalConePiece_finrank_eq_hilbertSeries_coeff]
  exact completeIntersectionHilbertSeries25_eventually n hn

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
