import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoGradedKoszul
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Tactic

/-!
# The literal quotient grading on the N25 canonical cone

This module supplies the two structural ingredients needed to replace
the presented Koszul cokernel by the actual homogeneous-coordinate quotient:
the defining ideal is homogeneous, and the image of each homogeneous piece
under the quotient map is an honest linear subspace of the literal quotient.
Taking homogeneous components of an arbitrary ideal representation proves
that the latter has exactly the relations supplied by the degreewise Koszul
map.  The first isomorphism theorem then identifies both degree-piece models.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoQuotientGrading

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoKoszul
open RationalPointsN25QuotientTwoGradedKoszul

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The quadric-cubic ideal is homogeneous for the standard total-degree
grading because both of its chosen generators are homogeneous. -/
theorem canonicalCurveIdeal25Two_isHomogeneous :
    canonicalCurveIdeal25Two.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 4) (ZMod 2)) := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨2, canonicalQuadricPolynomial25Two_isHomogeneous⟩
  · exact ⟨3, canonicalCubicPolynomial25Two_isHomogeneous⟩

/-! ## Homogeneous representatives of ideal relations -/

/-- Multiplication by a degree-`d` homogeneous polynomial shifts the
degree-`N` component by `d`; when `N<d`, that component vanishes.  The
truncated form is the one needed uniformly in all degrees of the Koszul
resolution. -/
theorem homogeneousComponent_mul_left_general {q : S} {d : ℕ}
    (hq : q.IsHomogeneous d) (s : S) (N : ℕ) :
    MvPolynomial.homogeneousComponent N (q * s) =
      if d ≤ N then
        q * MvPolynomial.homogeneousComponent (N - d) s
      else 0 := by
  by_cases hdN : d ≤ N
  · have hshift := homogeneousComponent_mul_left hq s (N - d)
    simpa [hdN, Nat.add_sub_of_le hdN] using hshift
  · nth_rw 1 [← MvPolynomial.sum_homogeneousComponent s]
    rw [Finset.mul_sum, map_sum]
    simp_rw [MvPolynomial.homogeneousComponent_of_mem
      (hq.mul (MvPolynomial.homogeneousComponent_isHomogeneous _ _))]
    have hNd : N < d := Nat.lt_of_not_ge hdN
    simp [hdN, Nat.ne_of_lt (lt_of_lt_of_le hNd (Nat.le_add_right d _))]

/-- The degree `n-debt` component of an arbitrary polynomial, packaged in
`S(-debt)_n`; below the shift this is the forced zero element. -/
def componentShifted (debt n : ℕ) (s : S) : shiftedPiece debt n :=
  if h : debt ≤ n then
    ⟨MvPolynomial.homogeneousComponent (n - debt) s, by
      rw [shiftedPiece, if_pos h]
      exact MvPolynomial.homogeneousComponent_isHomogeneous _ _⟩
  else
    ⟨0, by simp [shiftedPiece, h]⟩

/-- Forgetting the grading witness exposes the truncated homogeneous
component used to build degreewise relation coefficients. -/
@[simp]
theorem componentShifted_coe (debt n : ℕ) (s : S) :
    ((componentShifted debt n s : shiftedPiece debt n) : S) =
      if debt ≤ n then MvPolynomial.homogeneousComponent (n - debt) s
      else 0 := by
  by_cases h : debt ≤ n <;> simp [componentShifted, h]

/-- The literal degree-`n` part of the quotient is the image of homogeneous
degree-`n` polynomials under the actual quotient map `S → S/(Q,C)`. -/
def literalConePiece (n : ℕ) :
    Submodule (ZMod 2) CanonicalConeRing25Two :=
  (shiftedPiece 0 n).map (canonicalConeProjection.restrictScalars (ZMod 2))

/-- Restricting the quotient map to degree `n` lands in the literal degree
piece by construction. -/
def literalConeProjection (n : ℕ) :
    shiftedPiece 0 n →ₗ[ZMod 2] literalConePiece n :=
  ((canonicalConeProjection.restrictScalars (ZMod 2)).domRestrict
    (shiftedPiece 0 n)).codRestrict (literalConePiece n) (fun x ↦ by
      exact ⟨(x : S), x.property, rfl⟩)

/-- The kernel of the literal degree-`n` quotient map consists exactly of
the degree-`n` quadric-cubic relations.  Given an arbitrary ideal
representation, taking its degree-`n` component replaces both coefficients
by homogeneous ones of degrees `n-2` and `n-3`; no coefficient enumeration
or dimension comparison is involved. -/
theorem literalConeProjection_ker_eq_range (n : ℕ) :
    LinearMap.ker (literalConeProjection n) =
      LinearMap.range (gradedKoszulMiddle n) := by
  ext p
  constructor
  · intro hp
    rw [LinearMap.mem_ker] at hp
    have hpQuotient := congrArg
      (fun q : literalConePiece n ↦ (q : CanonicalConeRing25Two)) hp
    have hpIdeal : (p : S) ∈ canonicalCurveIdeal25Two := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa [literalConeProjection, canonicalConeProjection_apply] using hpQuotient
    rcases Ideal.mem_span_pair.mp hpIdeal with ⟨a, b, hab⟩
    have hpHomogeneous : (p : S).IsHomogeneous n := by
      simpa using shiftedPiece_isHomogeneous p
    have hpComponent :
        MvPolynomial.homogeneousComponent n (p : S) = (p : S) := by
      rw [MvPolynomial.homogeneousComponent_of_mem hpHomogeneous]
      simp
    let aₙ : shiftedPiece 2 n := componentShifted 2 n a
    let bₙ : shiftedPiece 3 n := componentShifted 3 n b
    have hrepresentation :
        canonicalQuadricPolynomial25Two * (aₙ : S) +
            canonicalCubicPolynomial25Two * (bₙ : S) = (p : S) := by
      calc
        canonicalQuadricPolynomial25Two * (aₙ : S) +
              canonicalCubicPolynomial25Two * (bₙ : S) =
            MvPolynomial.homogeneousComponent n
                (canonicalQuadricPolynomial25Two * a) +
              MvPolynomial.homogeneousComponent n
                (canonicalCubicPolynomial25Two * b) := by
                  simp only [aₙ, bₙ, componentShifted_coe]
                  rw [homogeneousComponent_mul_left_general
                    canonicalQuadricPolynomial25Two_isHomogeneous a n,
                    homogeneousComponent_mul_left_general
                      canonicalCubicPolynomial25Two_isHomogeneous b n]
                  by_cases htwo : 2 ≤ n <;>
                    by_cases hthree : 3 ≤ n <;> simp [htwo, hthree]
        _ = MvPolynomial.homogeneousComponent n
              (canonicalQuadricPolynomial25Two * a +
                canonicalCubicPolynomial25Two * b) := by
              rw [map_add]
        _ = MvPolynomial.homogeneousComponent n (p : S) := by
              rw [← hab]
              congr 1
              ring
        _ = (p : S) := hpComponent
    refine ⟨(aₙ, bₙ), ?_⟩
    apply Subtype.ext
    simpa only [gradedKoszulMiddle_coe] using hrepresentation
  · rintro ⟨q, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change canonicalConeProjection
      ((gradedKoszulMiddle n q : shiftedPiece 0 n) : S) = 0
    rw [gradedKoszulMiddle_coe]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_pair.mpr ⟨(q.1 : S), (q.2 : S), by ring⟩

/-- Every element of the literal degree piece has a homogeneous polynomial
representative, since that piece was defined as the image of the restricted
quotient map. -/
theorem literalConeProjection_surjective (n : ℕ) :
    Function.Surjective (literalConeProjection n) := by
  rintro ⟨q, hq⟩
  rcases hq with ⟨p, hp, rfl⟩
  exact ⟨⟨p, hp⟩, rfl⟩

/-- The cokernel occurring in the shifted Koszul resolution is canonically
the degree-`n` image inside the literal quotient ring.  This is the first
isomorphism theorem after the structural kernel computation above. -/
noncomputable def canonicalConePieceLinearEquiv (n : ℕ) :
    canonicalConePiece n ≃ₗ[ZMod 2] literalConePiece n :=
  (Submodule.quotEquivOfEq _ _
      (literalConeProjection_ker_eq_range n).symm).trans
    ((literalConeProjection n).quotKerEquivOfSurjective
      (literalConeProjection_surjective n))

/-- On a homogeneous polynomial representative, the canonical equivalence
is exactly the literal quotient map. -/
@[simp]
theorem canonicalConePieceLinearEquiv_mk (n : ℕ) (p : shiftedPiece 0 n) :
    canonicalConePieceLinearEquiv n (gradedConeProjection n p) =
      literalConeProjection n p := by
  rfl

end MazurProof.RationalPointsN25QuotientTwoQuotientGrading
