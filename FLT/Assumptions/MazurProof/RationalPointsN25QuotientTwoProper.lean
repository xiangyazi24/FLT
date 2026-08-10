import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Properness of the N25 binary projective quotient

Finite generation over the binary field passes to the homogeneous coordinate
quotient and then to its degree-zero coefficient ring.  Mathlib's projective
spectrum theorem therefore makes the structure morphism proper.  Transporting
the degree-zero target along its canonical ring equivalence with `F₂`
preserves properness.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoProper

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoProj
open AlgebraicGeometry
open CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/- These explicit instances avoid an expensive search through the polymorphic
grade-zero instances when constructing the finite-type scalar tower. -/
local instance literalConePieceZero_algebra_on_cone :
    Algebra (literalConePiece 0) CanonicalConeRing25Two :=
  SetLike.GradeZero.instAlgebraSubtypeMemOfNat literalConePiece

local instance binary_algebra_on_literalConePieceZero :
    Algebra k (literalConePiece 0) :=
  SetLike.GradeZero.instAlgebra literalConePiece

local instance literalConePieceZero_smul_on_cone :
    SMul (literalConePiece 0) CanonicalConeRing25Two :=
  literalConePieceZero_algebra_on_cone.toSMul

/-- The homogeneous coordinate quotient is finitely generated over the
binary coefficient field. -/
instance canonicalCone_finiteType_over_binary :
    Algebra.FiniteType k CanonicalConeRing25Two := by
  infer_instance

/-- Enlarging the coefficient ring from the binary field to the degree-zero
piece preserves finite generation of the homogeneous coordinate ring. -/
instance canonicalCone_finiteType_over_degreeZero :
    Algebra.FiniteType (literalConePiece 0) CanonicalConeRing25Two := by
  let coneBinaryAlgebra : Algebra k CanonicalConeRing25Two := inferInstance
  -- The canonical `ZMod` scalar action is propositionally the algebra action,
  -- but the scalar-tower constructor requires these structures definitionally.
  letI : SMul k CanonicalConeRing25Two := coneBinaryAlgebra.toSMul
  letI : SMul k (literalConePiece 0) :=
    binary_algebra_on_literalConePieceZero.toSMul
  letI : IsScalarTower k (literalConePiece 0) CanonicalConeRing25Two := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    k (literalConePiece 0) CanonicalConeRing25Two

/-- The projective quotient is proper over its degree-zero spectrum. -/
instance canonicalProjectiveCurve_toSpecZero_isProper :
    IsProper (Proj.toSpecZero literalConePiece) := by
  infer_instance

/-- After identifying the degree-zero ring with the binary field, the
projective quotient remains proper over `Spec F₂`. -/
instance canonicalProjectiveCurveToSpec_isProper :
    IsProper canonicalProjectiveCurveToSpec := by
  -- Expose the ring equivalence as a categorical isomorphism so that
  -- `Spec.map` is recognized as an isomorphism by typeclass inference.
  letI : IsIso
      (CommRingCat.ofHom literalConePieceZeroRingEquiv.toRingHom) := by
    change IsIso literalConePieceZeroRingEquiv.toCommRingCatIso.hom
    infer_instance
  dsimp only [canonicalProjectiveCurveToSpec]
  infer_instance

end MazurProof.RationalPointsN25QuotientTwoProper
