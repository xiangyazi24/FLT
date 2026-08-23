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

/-! ## Degree-one orbit classes -/

/-- Passing from a prime-field point to its period-one Frobenius orbit is
injective. -/
theorem degreeOneClosedPoint_injective :
    Function.Injective degreeOneClosedPoint := by
  intro P Q hPQ
  have horbit :
      SameExactOrbit commonPointFrobeniusTwo 1
        (exactDegreeOnePoint P) (exactDegreeOnePoint Q) :=
    Quotient.exact hPQ
  rcases horbit with ⟨i, hi⟩
  have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change (exactDegreeOnePoint P).1 = (exactDegreeOnePoint Q).1 at hi
  apply (extensionFixedPointRealization25Two.realize .degreeOne).injective
  apply Subtype.ext
  change (realizedDegreeOnePoint P).1 = (realizedDegreeOnePoint Q).1
  exact hi

/-- Every period-one orbit is represented by a unique prime-field point. -/
theorem degreeOneClosedPoint_surjective :
    Function.Surjective degreeOneClosedPoint := by
  intro c
  let Q : ExactPeriodicPoint commonPointFrobeniusTwo 1 :=
    orbitRepresentative commonPointFrobeniusTwo 1 (by norm_num) c
  let qfix : FixedByIterate commonPointFrobeniusTwo 1 :=
    ⟨Q.1, exactPeriodicPoint_iterate commonPointFrobeniusTwo Q⟩
  let P : ExtensionIndex25Two.pointType .degreeOne :=
    (extensionFixedPointRealization25Two.realize .degreeOne).symm qfix
  refine ⟨P, ?_⟩
  have hval : (exactDegreeOnePoint P).1 = Q.1 := by
    change (realizedDegreeOnePoint P).1 = Q.1
    change ((extensionFixedPointRealization25Two.realize .degreeOne) P).1 =
      qfix.1
    exact congrArg Subtype.val
      ((extensionFixedPointRealization25Two.realize .degreeOne).apply_symm_apply
        qfix)
  have hclasses :
      orbitClassMk commonPointFrobeniusTwo 1 (by norm_num)
          (exactDegreeOnePoint P) =
        orbitClassMk commonPointFrobeniusTwo 1 (by norm_num) Q := by
    apply Quotient.sound
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    simpa only [Function.iterate_zero, id_eq] using hval
  exact hclasses.trans
    (orbitRepresentative_class commonPointFrobeniusTwo 1 (by norm_num) c)

/-- Prime-field curve points are equivalent to degree-one closed orbits in
the original bounded grading. -/
noncomputable def degreeOnePointClosedEquiv :
    ExtensionIndex25Two.pointType .degreeOne ≃
      frobeniusOrbitGrading25TwoLE4.Closed 1 :=
  Equiv.ofBijective degreeOneClosedPoint
    ⟨degreeOneClosedPoint_injective, degreeOneClosedPoint_surjective⟩

/-- Prime-field curve points are equivalent to degree-one closed points in
the full grading. -/
noncomputable def fullDegreeOnePointEquiv :
    ExtensionIndex25Two.pointType .degreeOne ≃
      fullClosedPointGrading25Two.Closed 1 :=
  degreeOnePointClosedEquiv.trans closedPointDegreeOneEquiv

/-- Package a prime-field point as a degree-one full closed point. -/
noncomputable def fullDegreeOneClosedPoint
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    fullClosedPointGrading25Two.Closed 1 :=
  fullDegreeOnePointEquiv P

@[simp]
theorem fullDegreeOneClosedPoint_eq_transport
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    fullDegreeOneClosedPoint P =
      closedPointDegreeOneEquiv (degreeOneClosedPoint P) :=
  rfl

@[simp]
theorem fullDegreeOneClosedPoint_eq_iff
    (P Q : ExtensionIndex25Two.pointType .degreeOne) :
    fullDegreeOneClosedPoint P = fullDegreeOneClosedPoint Q ↔ P = Q :=
  fullDegreeOnePointEquiv.injective.eq_iff

/-! ## Boundary atoms in the full closed-point grading -/

/-- The boundary point `[1:0:0:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointX :
    fullClosedPointGrading25Two.Closed 1 :=
  fullDegreeOneClosedPoint wBoundaryPointX

/-- The boundary point `[0:1:1:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointYZ :
    fullClosedPointGrading25Two.Closed 1 :=
  fullDegreeOneClosedPoint hyperplanePointYZ

/-- The boundary point `[0:0:1:0]` as a degree-one full closed point. -/
noncomputable def fullBoundaryClosedPointZ :
    fullClosedPointGrading25Two.Closed 1 :=
  fullDegreeOneClosedPoint hyperplanePointZ

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

theorem wBoundaryPointX_ne_hyperplanePointYZ :
    wBoundaryPointX ≠ hyperplanePointYZ := by
  intro h
  have h' := congrArg Subtype.val h
  simp [wBoundaryPointX, hyperplanePointYZ] at h'

theorem wBoundaryPointX_ne_hyperplanePointZ :
    wBoundaryPointX ≠ hyperplanePointZ := by
  intro h
  have h' := congrArg Subtype.val h
  simp [wBoundaryPointX, hyperplanePointZ] at h'

theorem hyperplanePointYZ_ne_hyperplanePointZ :
    hyperplanePointYZ ≠ hyperplanePointZ := by
  intro h
  have h' := congrArg Subtype.val h
  simp [hyperplanePointYZ, hyperplanePointZ] at h'

theorem fullBoundaryClosedPointX_ne_YZ :
    fullBoundaryClosedPointX ≠ fullBoundaryClosedPointYZ := by
  intro h
  exact wBoundaryPointX_ne_hyperplanePointYZ
    ((fullDegreeOneClosedPoint_eq_iff
      wBoundaryPointX hyperplanePointYZ).mp h)

theorem fullBoundaryClosedPointX_ne_Z :
    fullBoundaryClosedPointX ≠ fullBoundaryClosedPointZ := by
  intro h
  exact wBoundaryPointX_ne_hyperplanePointZ
    ((fullDegreeOneClosedPoint_eq_iff
      wBoundaryPointX hyperplanePointZ).mp h)

theorem fullBoundaryClosedPointYZ_ne_Z :
    fullBoundaryClosedPointYZ ≠ fullBoundaryClosedPointZ := by
  intro h
  exact hyperplanePointYZ_ne_hyperplanePointZ
    ((fullDegreeOneClosedPoint_eq_iff
      hyperplanePointYZ hyperplanePointZ).mp h)

theorem fullBoundaryAtomX_ne_YZ :
    fullBoundaryAtomX ≠ fullBoundaryAtomYZ := by
  intro h
  have hc : fullBoundaryClosedPointX = fullBoundaryClosedPointYZ :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact fullBoundaryClosedPointX_ne_YZ hc

theorem fullBoundaryAtomX_ne_Z :
    fullBoundaryAtomX ≠ fullBoundaryAtomZ := by
  intro h
  have hc : fullBoundaryClosedPointX = fullBoundaryClosedPointZ :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact fullBoundaryClosedPointX_ne_Z hc

theorem fullBoundaryAtomYZ_ne_Z :
    fullBoundaryAtomYZ ≠ fullBoundaryAtomZ := by
  intro h
  have hc : fullBoundaryClosedPointYZ = fullBoundaryClosedPointZ :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact fullBoundaryClosedPointYZ_ne_Z hc

/-- Every full degree-one closed point is one of the three boundary points or
has a nonzero `W` coordinate on its unique prime-field representative. -/
theorem fullDegreeOne_boundary_or_wOpen
    (c : fullClosedPointGrading25Two.Closed 1) :
    c = fullBoundaryClosedPointX ∨
      c = fullBoundaryClosedPointYZ ∨
      c = fullBoundaryClosedPointZ ∨
      (normalizedCoordinates25 ((fullDegreeOnePointEquiv.symm c).1)).w ≠ 0 := by
  let P : ExtensionIndex25Two.pointType .degreeOne :=
    fullDegreeOnePointEquiv.symm c
  have hPc : fullDegreeOnePointEquiv P = c :=
    fullDegreeOnePointEquiv.apply_symm_apply c
  by_cases hW : (normalizedCoordinates25 P.1).w = 0
  · rcases primeFieldCurvePoint_w_eq_zero_classification P hW with
      hX | hYZ | hZ
    · left
      exact hPc.symm.trans (congrArg fullDegreeOnePointEquiv hX)
    · right; left
      exact hPc.symm.trans (congrArg fullDegreeOnePointEquiv hYZ)
    · right; right; left
      exact hPc.symm.trans (congrArg fullDegreeOnePointEquiv hZ)
  · exact Or.inr (Or.inr (Or.inr hW))

end MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints
