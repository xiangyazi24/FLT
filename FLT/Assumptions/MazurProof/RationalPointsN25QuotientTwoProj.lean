import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoGradedAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The projective spectrum of the N25 binary canonical cone

The surjective graded quotient map from the polynomial ring satisfies the
irrelevant-ideal hypothesis required by Mathlib's contravariant `Proj`
functor.  This module therefore constructs the canonical morphism from the
projective quotient to projective three-space and records its behavior on
basic opens.  The construction is scheme-theoretic; no point-set model or
dimension calculation is used.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoProj

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoKoszul
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open HomogeneousIdeal
open AlgebraicGeometry
open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Irrelevant ideals and the induced projective morphism -/

/-- Every positive-degree class in the quotient has a positive-degree
homogeneous representative in the polynomial ring. -/
theorem canonicalCone_irrelevant_le_map :
    literalConePiece₊ ≤
      (MvPolynomial.homogeneousSubmodule (Fin 4) k)₊.map
        canonicalConeGradedProjection := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  rcases hx with ⟨p, hp, rfl⟩
  apply Ideal.mem_map_of_mem canonicalConeGradedProjection
  apply HomogeneousIdeal.mem_irrelevant_of_mem _ hi
  simpa [shiftedPiece] using hp

/-! ## The degree-zero base ring -/

/-- In degree zero the middle Koszul differential has zero source: both
shifted summands are below their generating degrees. -/
theorem gradedKoszulMiddle_zero_eq_zero : gradedKoszulMiddle 0 = 0 := by
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  have hq1 : (q.1 : S) = 0 := by
    have hq1mem : (q.1 : S) ∈ (⊥ : Submodule k S) := by
      simpa only [shiftedPiece,
        if_neg (by norm_num : ¬ (2 : ℕ) ≤ 0)] using q.1.property
    exact (Submodule.mem_bot k).mp hq1mem
  have hq2 : (q.2 : S) = 0 := by
    have hq2mem : (q.2 : S) ∈ (⊥ : Submodule k S) := by
      simpa only [shiftedPiece,
        if_neg (by norm_num : ¬ (3 : ℕ) ≤ 0)] using q.2.property
    exact (Submodule.mem_bot k).mp hq2mem
  simp [gradedKoszulMiddle_coe, hq1, hq2]

/-- The quotient map is injective on degree-zero homogeneous polynomials.
Indeed, the degree-zero Koszul image is trivial. -/
theorem literalConeProjection_zero_injective :
    Function.Injective (literalConeProjection 0) := by
  rw [← LinearMap.ker_eq_bot]
  rw [literalConeProjection_ker_eq_range,
    gradedKoszulMiddle_zero_eq_zero, LinearMap.range_zero]

/-- Constants give every degree-zero class of the homogeneous quotient,
and no two constants become equal in that quotient. -/
theorem algebraMap_literalConePiece_zero_bijective :
    Function.Bijective (algebraMap k (literalConePiece 0)) := by
  constructor
  · intro a b hab
    let ca : shiftedPiece 0 0 := ⟨MvPolynomial.C a, by
      rw [shiftedPiece, if_pos (Nat.zero_le 0)]
      exact MvPolynomial.isHomogeneous_C (Fin 4) a⟩
    let cb : shiftedPiece 0 0 := ⟨MvPolynomial.C b, by
      rw [shiftedPiece, if_pos (Nat.zero_le 0)]
      exact MvPolynomial.isHomogeneous_C (Fin 4) b⟩
    have hab' : literalConeProjection 0 ca = literalConeProjection 0 cb := by
      apply Subtype.ext
      change canonicalConeProjection (MvPolynomial.C a) =
        canonicalConeProjection (MvPolynomial.C b)
      have habValue := congrArg Subtype.val hab
      rw [SetLike.GradeZero.coe_algebraMap,
        SetLike.GradeZero.coe_algebraMap] at habValue
      simpa only [canonicalConeProjection_apply,
        ← MvPolynomial.algebraMap_eq,
        Ideal.Quotient.mk_algebraMap] using habValue
    have hC : (MvPolynomial.C a : S) = MvPolynomial.C b := by
      exact congrArg Subtype.val (literalConeProjection_zero_injective hab')
    exact (MvPolynomial.C_injective (Fin 4) k) hC
  · intro x
    rcases x.property with ⟨p, hp, hpx⟩
    have hpHomogeneous : p.IsHomogeneous 0 := by
      simpa only [Nat.zero_sub] using
        shiftedPiece_isHomogeneous (⟨p, hp⟩ : shiftedPiece 0 0)
    have hpDegree : p.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr hpHomogeneous
    have hpConstant : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := p)).mp hpDegree
    refine ⟨MvPolynomial.coeff 0 p, ?_⟩
    apply Subtype.ext
    rw [SetLike.GradeZero.coe_algebraMap]
    change canonicalConeProjection (MvPolynomial.C (MvPolynomial.coeff 0 p)) = x
    rw [← hpConstant]
    exact hpx

/-- The degree-zero quotient ring is canonically the binary base field. -/
noncomputable def literalConePieceZeroRingEquiv :
    k ≃+* literalConePiece 0 :=
  RingEquiv.ofBijective (algebraMap k (literalConePiece 0))
    algebraMap_literalConePiece_zero_bijective

/-- The projective scheme cut out by the canonical quadric and cubic over
the binary field. -/
abbrev CanonicalProjectiveCurve25Two : Scheme :=
  AlgebraicGeometry.Proj literalConePiece

/-- Projective three-space presented as the `Proj` of the standard grading
on the four-variable binary polynomial ring. -/
abbrev BinaryProjectiveThreeSpace : Scheme :=
  AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin 4) k)

/-- The graded quotient map induces the canonical morphism from the
quadric-cubic projective quotient into projective three-space. -/
def canonicalProjectiveCurveMap :
    CanonicalProjectiveCurve25Two ⟶ BinaryProjectiveThreeSpace :=
  AlgebraicGeometry.Proj.map canonicalConeGradedProjection
    canonicalCone_irrelevant_le_map

/-- The structure morphism of the projective quotient, with its degree-zero
target identified with the binary base field. -/
def canonicalProjectiveCurveToSpec :
    CanonicalProjectiveCurve25Two ⟶ Spec (.of k) :=
  AlgebraicGeometry.Proj.toSpecZero literalConePiece ≫
    Spec.map (CommRingCat.ofHom (literalConePieceZeroRingEquiv).toRingHom)

/-! ## Basic-open compatibility -/

/-- Pulling back a standard projective basic open gives the basic open of
the corresponding quotient class. -/
@[simp]
theorem canonicalProjectiveCurveMap_preimage_basicOpen (s : S) :
    canonicalProjectiveCurveMap ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 4) k) s =
      AlgebraicGeometry.Proj.basicOpen literalConePiece
        (canonicalConeGradedProjection s) := by
  rfl

/-- In particular, the four standard coordinate charts pull back to the
four quotient-coordinate charts. -/
@[simp]
theorem canonicalProjectiveCurveMap_preimage_coordinate (i : Fin 4) :
    canonicalProjectiveCurveMap ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin 4) k)
          (MvPolynomial.X i) =
      AlgebraicGeometry.Proj.basicOpen literalConePiece
        (canonicalConeGradedProjection (MvPolynomial.X i)) := by
  rfl

end MazurProof.RationalPointsN25QuotientTwoProj
