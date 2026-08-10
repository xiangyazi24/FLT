import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoQuotientGrading
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The graded algebra structure on the N25 binary canonical cone

The literal degree pieces in `S/(Q,C)` form an internal direct sum.  The
proof maps the standard homogeneous decomposition of `S` componentwise into
the quotient.  Homogeneity of `(Q,C)` shows that this map has exactly the
same kernel as the quotient map, so canonical recomposition is bijective.
Together with multiplication of homogeneous representatives, this installs
the actual quotient as a graded algebra and records explicit formulas for
its otherwise noncomputably chosen decomposition.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoQuotientGrading

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoKoszul
open RationalPointsN25QuotientTwoGradedKoszul
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The componentwise quotient map -/

/-- Reinterpret an ordinary homogeneous piece as the zero-shifted piece. -/
def homogeneousPieceEquivShifted (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) k n ≃ₗ[k] shiftedPiece 0 n :=
  LinearEquiv.ofEq _ _ (by simp [shiftedPiece])

/-- Map one standard polynomial component into its quotient component. -/
def homogeneousPieceToLiteral (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) k n →ₗ[k] literalConePiece n :=
  (literalConeProjection n).comp (homogeneousPieceEquivShifted n).toLinearMap

/-- The polynomial grading mapped componentwise into the literal quotient pieces. -/
def polynomialToLiteralPieces : S →ₗ[k] ⨁ n, literalConePiece n :=
  DirectSum.lmap homogeneousPieceToLiteral ∘ₗ
    DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule (Fin 4) k)

/-- The `n`th output is represented by the `n`th homogeneous component. -/
@[simp]
theorem polynomialToLiteralPieces_apply (p : S) (n : ℕ) :
    polynomialToLiteralPieces p n =
      literalConeProjection n
        (homogeneousPieceEquivShifted n
          ⟨MvPolynomial.homogeneousComponent n p,
            MvPolynomial.homogeneousComponent_isHomogeneous n p⟩) := by
  change literalConeProjection n
      (homogeneousPieceEquivShifted n
        (DirectSum.decompose
          (MvPolynomial.homogeneousSubmodule (Fin 4) k) p n)) = _
  apply congrArg (literalConeProjection n)
  apply Subtype.ext
  exact MvPolynomial.decomposition.decompose'_apply p n

/-- Every finitely supported family of literal pieces has a polynomial preimage. -/
theorem polynomialToLiteralPieces_surjective :
    Function.Surjective polynomialToLiteralPieces := by
  apply Function.Surjective.comp
    ((DirectSum.lmap_surjective homogeneousPieceToLiteral).mpr ?_)
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule (Fin 4) k)).surjective
  intro n
  exact Function.Surjective.comp
    (literalConeProjection_surjective n)
    (homogeneousPieceEquivShifted n).surjective

/-- Recombining the mapped homogeneous pieces is the original quotient map. -/
theorem coeLinearMap_polynomialToLiteralPieces :
    DirectSum.coeLinearMap literalConePiece ∘ₗ polynomialToLiteralPieces =
      canonicalConeProjection.restrictScalars k := by
  apply DirectSum.decompose_lhom_ext
    (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  intro n
  ext p
  simp [polynomialToLiteralPieces, homogeneousPieceToLiteral,
    homogeneousPieceEquivShifted, literalConeProjection,
    canonicalConeProjection_apply]

/-! ## Directness of the quotient pieces -/

/-- A polynomial maps to zero in every literal degree exactly when it maps
to zero in the quotient ring. -/
theorem polynomialToLiteralPieces_ker :
    LinearMap.ker polynomialToLiteralPieces =
      LinearMap.ker (canonicalConeProjection.restrictScalars k) := by
  ext p
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hp
    have hcomp := LinearMap.congr_fun
      coeLinearMap_polynomialToLiteralPieces p
    simpa [hp] using hcomp.symm
  · intro hp
    have hpIdeal : p ∈ canonicalCurveIdeal25Two := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa [canonicalConeProjection_apply] using hp
    have hpComponents :=
      (canonicalCurveIdeal25Two_isHomogeneous.mem_iff).mp hpIdeal
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    rw [polynomialToLiteralPieces_apply]
    change canonicalConeProjection
      (MvPolynomial.homogeneousComponent n p) = 0
    rw [canonicalConeProjection_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← MvPolynomial.decomposition.decompose'_apply p n]
    exact hpComponents n

/-- The literal quotient pieces form an internal direct sum in the quotient. -/
theorem literalConePiece_isInternal :
    DirectSum.IsInternal literalConePiece := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := polynomialToLiteralPieces_surjective x
    obtain ⟨q, rfl⟩ := polynomialToLiteralPieces_surjective y
    apply sub_eq_zero.mp
    have hpq : p - q ∈ LinearMap.ker polynomialToLiteralPieces := by
      rw [polynomialToLiteralPieces_ker, LinearMap.mem_ker]
      rw [map_sub, sub_eq_zero]
      calc
        canonicalConeProjection p =
            DirectSum.coeLinearMap literalConePiece
              (polynomialToLiteralPieces p) :=
          (LinearMap.congr_fun coeLinearMap_polynomialToLiteralPieces p).symm
        _ = DirectSum.coeLinearMap literalConePiece
              (polynomialToLiteralPieces q) := hxy
        _ = canonicalConeProjection q :=
          LinearMap.congr_fun coeLinearMap_polynomialToLiteralPieces q
    simpa only [LinearMap.mem_ker, map_sub] using hpq
  · intro q
    obtain ⟨p, rfl⟩ := canonicalConeProjection_surjective q
    refine ⟨polynomialToLiteralPieces p, ?_⟩
    exact LinearMap.congr_fun coeLinearMap_polynomialToLiteralPieces p

/-! ## Multiplication and the quotient grading -/

/-- The quotient unit is represented by the degree-zero polynomial one. -/
theorem one_mem_literalConePiece :
    (1 : CanonicalConeRing25Two) ∈ literalConePiece 0 := by
  refine ⟨1, ?_, ?_⟩
  · rw [shiftedPiece, if_pos (Nat.zero_le 0)]
    change (1 : S).IsHomogeneous 0
    exact MvPolynomial.isHomogeneous_one (Fin 4) k
  · simp [canonicalConeProjection_apply]

/-- Products of literal homogeneous quotient classes add their degrees. -/
theorem mul_mem_literalConePiece {i j : ℕ} {x y : CanonicalConeRing25Two}
    (hx : x ∈ literalConePiece i) (hy : y ∈ literalConePiece j) :
    x * y ∈ literalConePiece (i + j) := by
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨q, hq, rfl⟩
  refine ⟨p * q, ?_, ?_⟩
  · have hpHomogeneous := shiftedPiece_isHomogeneous ⟨p, hp⟩
    have hqHomogeneous := shiftedPiece_isHomogeneous ⟨q, hq⟩
    simpa [shiftedPiece] using hpHomogeneous.mul hqHomogeneous
  · simp [canonicalConeProjection_apply]

/-- The literal quotient pieces give the actual internal grading on
`S/(Q,C)`. -/
noncomputable instance literalConePieceGradedAlgebra :
    GradedAlgebra literalConePiece where
  one_mem := one_mem_literalConePiece
  mul_mem := fun _ _ _ _ hx hy ↦ mul_mem_literalConePiece hx hy
  decompose' :=
    (literalConePiece_isInternal.chooseDecomposition literalConePiece).decompose'
  left_inv :=
    (literalConePiece_isInternal.chooseDecomposition literalConePiece).left_inv
  right_inv :=
    (literalConePiece_isInternal.chooseDecomposition literalConePiece).right_inv

/-- The polynomial quotient map is a graded ring homomorphism from the
standard grading to the literal quotient grading. -/
def canonicalConeGradedProjection :
    MvPolynomial.homogeneousSubmodule (Fin 4) k →+*ᵍ literalConePiece where
  toRingHom := Ideal.Quotient.mk canonicalCurveIdeal25Two
  map_mem := by
    intro n p hp
    refine ⟨p, ?_, rfl⟩
    simpa [shiftedPiece] using hp

/-- The graded quotient map is surjective on the underlying rings. -/
theorem canonicalConeGradedProjection_surjective :
    Function.Surjective canonicalConeGradedProjection :=
  Ideal.Quotient.mk_surjective

/-! ## Explicit formulas for the chosen decomposition -/

/-- The quotient decomposition of a polynomial is its mapped homogeneous
decomposition, despite the noncomputable construction of the instance. -/
theorem decompose_canonicalConeProjection (p : S) :
    DirectSum.decompose literalConePiece (canonicalConeProjection p) =
      polynomialToLiteralPieces p := by
  apply (DirectSum.decompose literalConePiece).symm.injective
  rw [(DirectSum.decompose literalConePiece).symm_apply_apply]
  exact (LinearMap.congr_fun coeLinearMap_polynomialToLiteralPieces p).symm

/-- The degree-`n` quotient projection is represented by the degree-`n`
homogeneous component of any polynomial representative. -/
theorem decompose_canonicalConeProjection_apply (p : S) (n : ℕ) :
    DirectSum.decompose literalConePiece (canonicalConeProjection p) n =
      literalConeProjection n
        (homogeneousPieceEquivShifted n
          ⟨MvPolynomial.homogeneousComponent n p,
            MvPolynomial.homogeneousComponent_isHomogeneous n p⟩) := by
  rw [decompose_canonicalConeProjection,
    polynomialToLiteralPieces_apply]

/-- A literal homogeneous class decomposes as a single supported summand. -/
theorem decompose_literalConeProjection (n : ℕ) (p : shiftedPiece 0 n) :
    DirectSum.decompose literalConePiece
        ((literalConeProjection n p : literalConePiece n) :
          CanonicalConeRing25Two) =
      DirectSum.of (fun n ↦ literalConePiece n) n
        (literalConeProjection n p) := by
  exact DirectSum.decompose_coe literalConePiece (literalConeProjection n p)

end MazurProof.RationalPointsN25QuotientTwoQuotientGrading
