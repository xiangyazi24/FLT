import FLT.Assumptions.MazurProof.CurveDivisorPicard
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoHyperplaneArtinLocal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoConormalBasis

/-!
# A concrete degree-six hyperplane section in characteristic two

For the canonical quadric-cubic model, the hyperplane `x=0` makes the cubic
factor as

`z * w * (y + z + w)`.

Restricting the quadric to those three line factors gives `y^2`,
`y*(y+z)`, and `w^2`.  The resulting intersection multiplicity pattern is

`2[0:0:0:1] + [0:0:1:0] + 3[0:1:1:0]`.

This file kernel-checks the polynomial restrictions, realizes the three
prime-field points as degree-one Frobenius closed points, and constructs the
corresponding effective divisor of degree six.  It deliberately stops short
of calling the divisor canonical: that final word requires the adjunction
theorem identifying a hyperplane section of the smooth `(2,3)` complete
intersection with its dualizing divisor.
-/

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDivisor

open CurveZetaEffectiveDivisors
open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientMiddleRiemannRoch
open RationalPointsN25QuotientTwoFrobeniusOrbits
open Function

/-! ## Exact hyperplane-restriction identities -/

/-- On `x=0` the characteristic-two cubic is the product of three rational
lines. -/
theorem cubic_x_zero_factor
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    canonicalCubic25Over (⟨0, y, z, w⟩ : Coordinates4 K) =
      z * w * (y + z + w) := by
  dsimp [canonicalCubic25Over]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination -(z * w ^ 2) * htwo

/-- On the cubic factor `z=0`, the quadric restricts to the double equation
`y^2=0`. -/
theorem quadric_xz_zero {K : Type*} [CommRing K] (y w : K) :
    canonicalQuadric25Over (⟨0, y, 0, w⟩ : Coordinates4 K) = y ^ 2 := by
  simp [canonicalQuadric25Over]

/-- On the cubic factor `w=0`, the quadric splits as `y*(y+z)`. -/
theorem quadric_xw_zero {K : Type*} [CommRing K] (y z : K) :
    canonicalQuadric25Over (⟨0, y, z, 0⟩ : Coordinates4 K) =
      y * (y + z) := by
  simp [canonicalQuadric25Over]
  ring

/-- On the third cubic factor `y+z+w=0`, the quadric restricts to the double
equation `w^2=0`. -/
theorem quadric_x_zero_third_line
    {K : Type*} [CommRing K] [CharP K 2] (z w : K) :
    canonicalQuadric25Over (⟨0, z + w, z, w⟩ : Coordinates4 K) = w ^ 2 := by
  dsimp [canonicalQuadric25Over]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (z ^ 2 + 2 * z * w) * htwo

/-! ## The three rational points as Frobenius closed points -/

/-- The point `[0:0:0:1]` on the binary canonical curve. -/
def hyperplanePointW : ExtensionIndex25Two.pointType .degreeOne :=
  ⟨.wChart, by
    norm_num [IsCanonicalNormalizedTwo, fieldBinaryOperations,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      canonicalQuadric25Binary, canonicalCubic25Binary]⟩

/-- The point `[0:0:1:0]` on the binary canonical curve. -/
def hyperplanePointZ : ExtensionIndex25Two.pointType .degreeOne :=
  ⟨.zChart 0, by
    norm_num [IsCanonicalNormalizedTwo, fieldBinaryOperations,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      canonicalQuadric25Binary, canonicalCubic25Binary]⟩

/-- The point `[0:1:1:0]` on the binary canonical curve. -/
def hyperplanePointYZ : ExtensionIndex25Two.pointType .degreeOne :=
  ⟨.yChart 1 0, by
    norm_num [IsCanonicalNormalizedTwo, fieldBinaryOperations,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      canonicalQuadric25Binary, canonicalCubic25Binary]
    exact CharP.cast_eq_zero F2 2⟩

/-- Embed a prime-field curve point into the common field as a fixed point of
one arithmetic-Frobenius iterate. -/
noncomputable def realizedDegreeOnePoint
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    FixedByIterate commonPointFrobeniusTwo 1 :=
  extensionFixedPointRealization25Two.realize .degreeOne P

/-- A point fixed by the first Frobenius iterate has exact period one. -/
noncomputable def exactDegreeOnePoint
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    ExactPeriodicPoint commonPointFrobeniusTwo 1 :=
  ⟨(realizedDegreeOnePoint P).1,
    minimalPeriod_eq_one_iff_isFixedPt.mpr (by
      change commonPointFrobeniusTwo (realizedDegreeOnePoint P).1 =
        (realizedDegreeOnePoint P).1
      simpa only [iterate_one] using (realizedDegreeOnePoint P).2)⟩

/-- The degree-one closed point represented by a rational binary curve
point. -/
noncomputable def degreeOneClosedPoint
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    frobeniusOrbitGrading25TwoLE4.Closed 1 :=
  orbitClassMk commonPointFrobeniusTwo 1 (by norm_num)
    (exactDegreeOnePoint P)

/-- Package a rational point as a degree-one atom in the closed-point
grading. -/
noncomputable def degreeOneAtom
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    frobeniusOrbitGrading25TwoLE4.Atom :=
  ⟨1, degreeOneClosedPoint P⟩

@[simp]
theorem atomDegree_degreeOne
    (P : ExtensionIndex25Two.pointType .degreeOne) :
    frobeniusOrbitGrading25TwoLE4.atomDegree (degreeOneAtom P) = 1 :=
  rfl

/-! ## The degree-six divisor candidate -/

/-- The effective closed-point combination dictated by the three restricted
quadric equations on `x=0`. -/
noncomputable def hyperplaneSectionDivisor :
    frobeniusOrbitGrading25TwoLE4.EffDiv :=
  Finsupp.single (degreeOneAtom hyperplanePointW) 2 +
    Finsupp.single (degreeOneAtom hyperplanePointZ) 1 +
    Finsupp.single (degreeOneAtom hyperplanePointYZ) 3

/-- The displayed multiplicities have total closed-point degree six. -/
theorem hyperplaneSectionDivisor_degree :
    frobeniusOrbitGrading25TwoLE4.divDegree hyperplaneSectionDivisor = 6 := by
  rw [hyperplaneSectionDivisor,
    frobeniusOrbitGrading25TwoLE4.divDegree_add,
    frobeniusOrbitGrading25TwoLE4.divDegree_add]
  simp [frobeniusOrbitGrading25TwoLE4.divDegree_single]

/-- The concrete degree-six effective divisor, ready to be mapped into any
honestly constructed divisor-class quotient for this closed-point grading. -/
noncomputable def hyperplaneSectionEffectiveDegreeSix :
    frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 6 :=
  ⟨hyperplaneSectionDivisor, hyperplaneSectionDivisor_degree⟩

/-- A rational degree-one base divisor, chosen from the same hyperplane
section. -/
noncomputable def basePointDivisor :
    frobeniusOrbitGrading25TwoLE4.EffDiv :=
  Finsupp.single (degreeOneAtom hyperplanePointW) 1

/-- The chosen rational base point has divisor degree one. -/
theorem basePointDivisor_degree :
    frobeniusOrbitGrading25TwoLE4.divDegree basePointDivisor = 1 := by
  simp [basePointDivisor,
    frobeniusOrbitGrading25TwoLE4.divDegree_single]

/-- The chosen base point as a degree-one effective divisor. -/
noncomputable def basePointEffectiveDegreeOne :
    frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 1 :=
  ⟨basePointDivisor, basePointDivisor_degree⟩

/-- The divisor class of the chosen rational base point. -/
noncomputable def basePointClass
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker) :
    frobeniusOrbitGrading25TwoLE4.DivisorClass Principal :=
  (frobeniusOrbitGrading25TwoLE4.effectiveClass
    Principal hPrincipal 1 basePointEffectiveDegreeOne).1

/-- The chosen base-point class has degree one in the divisor-class
quotient. -/
theorem basePointClass_degree
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker) :
    frobeniusOrbitGrading25TwoLE4.classDegree Principal hPrincipal
      (basePointClass Principal hPrincipal) = 1 :=
  (frobeniusOrbitGrading25TwoLE4.effectiveClass
    Principal hPrincipal 1 basePointEffectiveDegreeOne).2

/-- The class of the explicit degree-six hyperplane-section divisor. -/
noncomputable def hyperplaneSectionClass
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker) :
    frobeniusOrbitGrading25TwoLE4.DivisorClass Principal :=
  (frobeniusOrbitGrading25TwoLE4.effectiveClass
    Principal hPrincipal 6 hyperplaneSectionEffectiveDegreeSix).1

/-- The hyperplane-section class has degree six.  Proving that this class is
canonical remains the specific adjunction seam. -/
theorem hyperplaneSectionClass_degree
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker) :
    frobeniusOrbitGrading25TwoLE4.classDegree Principal hPrincipal
      (hyperplaneSectionClass Principal hPrincipal) = 6 :=
  (frobeniusOrbitGrading25TwoLE4.effectiveClass
    Principal hPrincipal 6 hyperplaneSectionEffectiveDegreeSix).2

end MazurProof.RationalPointsN25QuotientTwoCanonicalDivisor
