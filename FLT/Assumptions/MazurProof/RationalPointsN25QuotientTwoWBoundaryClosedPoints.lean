import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFullClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDivisor

/-!
# Closed points on the canonical binary curve's \`W = 0\` boundary

The complement of the fixed \`w = 1\` chart consists of exactly the three
prime-field points \`[1:0:0:0]\`, \`[0:1:1:0]\`, and \`[0:0:1:0]\`.
They are Frobenius fixed, so an exact-period point on this boundary has degree
one.  This is a statement about closed-point support and residue degree; it
does not identify any hyperplane intersection multiplicity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientMiddleRiemannRoch
open NormalizedProjectiveCurveFrobenius
open FiniteFieldFrobeniusDescent
open CurveZetaFrobeniusOrbitGrading
open Function

/-- The prime-field boundary point `[1:0:0:0]`, complementary to the two
already named points on the hyperplane section `x = 0`. -/
def wBoundaryPointX : ExtensionIndex25Two.pointType .degreeOne :=
  ⟨.xChart 0 0 0, by
    norm_num [IsCanonicalNormalizedTwo, fieldBinaryOperations,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      canonicalQuadric25Binary, canonicalCubic25Binary]⟩

/-- A geometric curve point with fourth coordinate zero is one of the three
explicit prime-field boundary points. -/
theorem curvePoint_w_eq_zero_classification
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointTwo K)
    (hW : (normalizedCoordinates25 P.1).w = 0) :
    P.1 = .xChart 0 0 0 ∨
      P.1 = .yChart 1 0 ∨ P.1 = .zChart 0 := by
  rcases P with ⟨P, hP⟩
  cases P with
  | xChart y z w =>
      change w = 0 at hW
      subst w
      rcases hP with ⟨hq, hc⟩
      have hq0 : z + y * y + y * z = 0 := by
        simpa only [canonicalQuadric25Binary, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations,
          one_mul, mul_zero, zero_mul, add_zero, zero_add] using hq
      have hc0 : y * z = 0 := by
        simpa only [canonicalCubic25Binary, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations,
          one_mul, mul_zero, zero_mul, add_zero, zero_add] using hc
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hc0 with hy | hz
      · subst y
        simp at hq0
        subst z
        simp
      · subst z
        simp at hq0
        subst y
        simp
  | yChart z w =>
      change w = 0 at hW
      subst w
      have hq := hP.1
      have hq0 : 1 + z = 0 := by
        simpa only [canonicalQuadric25Binary, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations,
          one_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one] using hq
      have hz : z = -1 := eq_neg_of_add_eq_zero_right hq0
      rw [CharTwo.neg_eq] at hz
      subst z
      simp
  | zChart w =>
      change w = 0 at hW
      subst w
      simp
  | wChart =>
      simp [normalizedCoordinates25, NormalizedProjective4.coordinates,
        fieldBinaryOperations] at hW

/-- Every point on the `W = 0` boundary is fixed by arithmetic Frobenius. -/
theorem curvePoint_w_eq_zero_isFixedPt
    (d : ℕ) (P : CurvePointTwo (CommonField 2 d))
    (hW : (normalizedCoordinates25 P.1).w = 0) :
    IsFixedPt (degreePointFrobeniusTwo d) P := by
  rcases curvePoint_w_eq_zero_classification P hW with h | h | h
  · apply Subtype.ext
    change RationalPointsN25QuotientBaseChange.NormalizedProjective4.map
      (commonFrobenius 2 d).toRingEquiv.toRingHom P.1 = P.1
    rw [h]
    simp
  · apply Subtype.ext
    change RationalPointsN25QuotientBaseChange.NormalizedProjective4.map
      (commonFrobenius 2 d).toRingEquiv.toRingHom P.1 = P.1
    rw [h]
    simp
  · apply Subtype.ext
    change RationalPointsN25QuotientBaseChange.NormalizedProjective4.map
      (commonFrobenius 2 d).toRingEquiv.toRingHom P.1 = P.1
    rw [h]
    simp

/-- An exact-period point on the `W = 0` boundary necessarily has degree
one. -/
theorem exactPeriodicPoint_w_eq_zero_degree_eq_one
    (d : ℕ) (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hW : (normalizedCoordinates25 Q.1.1).w = 0) : d = 1 := by
  calc
    d = minimalPeriod (degreePointFrobeniusTwo d) Q.1 := Q.2.symm
    _ = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr
      (curvePoint_w_eq_zero_isFixedPt d Q.1 hW)

/-- Every exact-period point of degree greater than one belongs to the fixed
`W` open. -/
theorem exactPeriodicPoint_w_ne_zero_of_one_lt
    (d : ℕ) (hd : 1 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    (normalizedCoordinates25 Q.1.1).w ≠ 0 := by
  intro hW
  have hd1 := exactPeriodicPoint_w_eq_zero_degree_eq_one d Q hW
  omega

/-- Every exact-period point either belongs to the fixed `W` open or is an
explicit degree-one boundary point. -/
theorem exactPeriodicPoint_wOpen_or_degreeOne_boundary
    (d : ℕ) (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    (normalizedCoordinates25 Q.1.1).w ≠ 0 ∨
      d = 1 ∧
        (Q.1.1 = .xChart 0 0 0 ∨
          Q.1.1 = .yChart 1 0 ∨ Q.1.1 = .zChart 0) := by
  by_cases hW : (normalizedCoordinates25 Q.1.1).w ≠ 0
  · exact Or.inl hW
  · have hW0 : (normalizedCoordinates25 Q.1.1).w = 0 :=
      not_ne_iff.mp hW
    exact Or.inr ⟨exactPeriodicPoint_w_eq_zero_degree_eq_one d Q hW0,
      curvePoint_w_eq_zero_classification Q.1 hW0⟩

/-- Over the prime field, the three abstract boundary alternatives are the
named rational points `X`, `YZ`, and `Z`. -/
theorem primeFieldCurvePoint_w_eq_zero_classification
    (P : ExtensionIndex25Two.pointType .degreeOne)
    (hW : (normalizedCoordinates25 P.1).w = 0) :
    P = wBoundaryPointX ∨ P = hyperplanePointYZ ∨ P = hyperplanePointZ := by
  rcases curvePoint_w_eq_zero_classification P hW with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-! ## Boundary atoms in the full closed-point grading -/

/-- The boundary point `[1:0:0:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointX :
    fullClosedPointGrading25Two.Closed 1 :=
  closedPointDegreeOneEquiv (degreeOneClosedPoint wBoundaryPointX)

/-- The boundary point `[0:1:1:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointYZ :
    fullClosedPointGrading25Two.Closed 1 :=
  closedPointDegreeOneEquiv (degreeOneClosedPoint hyperplanePointYZ)

/-- The boundary point `[0:0:1:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointZ :
    fullClosedPointGrading25Two.Closed 1 :=
  closedPointDegreeOneEquiv (degreeOneClosedPoint hyperplanePointZ)

/-- The point `[1:0:0:0]` as an atom of the full grading. -/
noncomputable def fullBoundaryAtomX : fullClosedPointGrading25Two.Atom :=
  ⟨1, fullBoundaryClosedPointX⟩

/-- The point `[0:1:1:0]` as an atom of the full grading. -/
noncomputable def fullBoundaryAtomYZ : fullClosedPointGrading25Two.Atom :=
  ⟨1, fullBoundaryClosedPointYZ⟩

/-- The point `[0:0:1:0]` as an atom of the full grading. -/
noncomputable def fullBoundaryAtomZ : fullClosedPointGrading25Two.Atom :=
  ⟨1, fullBoundaryClosedPointZ⟩

@[simp]
theorem fullBoundaryAtomX_degree :
    fullClosedPointGrading25Two.atomDegree fullBoundaryAtomX = 1 :=
  rfl

@[simp]
theorem fullBoundaryAtomYZ_degree :
    fullClosedPointGrading25Two.atomDegree fullBoundaryAtomYZ = 1 :=
  rfl

@[simp]
theorem fullBoundaryAtomZ_degree :
    fullClosedPointGrading25Two.atomDegree fullBoundaryAtomZ = 1 :=
  rfl

end MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints
