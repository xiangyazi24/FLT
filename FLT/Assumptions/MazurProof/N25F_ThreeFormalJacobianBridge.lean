import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF3
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Integer formal Jacobian bridge for the characteristic-three N25 curve

The two integer homogeneous polynomials evaluate to the existing canonical
quadric and cubic. Their formal partial derivatives evaluate, in
characteristic three, to the existing geometric gradient rows.

The last two theorems retain the curve-point hypothesis and use the existing
projective nonsingularity certificate to obtain a nonzero formal Jacobian
minor. No scheme-level smoothness assertion is made here.

The source quadric gradient begins with `-P.z - P.w`.
-/

noncomputable section

namespace MazurProof.N25F_ThreeFormalJacobianBridge

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmoothF3

/-- The integer homogeneous coordinate polynomial ring, ordered x,y,z,w. -/
abbrev HomogeneousRing25ThreeZ := MvPolynomial (Fin 4) ℤ

/-- The canonical quadric with its original integer coefficients. -/
def canonicalQuadricPolynomial25Three : HomogeneousRing25ThreeZ :=
  -(MvPolynomial.X 0 * MvPolynomial.X 2) -
    MvPolynomial.X 0 * MvPolynomial.X 3 +
    MvPolynomial.X 1 ^ 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 2 * MvPolynomial.X 3

/-- The canonical cubic with its original integer coefficients. -/
def canonicalCubicPolynomial25Three : HomogeneousRing25ThreeZ :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
    MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 ^ 2 * MvPolynomial.X 3 -
    MvPolynomial.X 2 * MvPolynomial.X 3 ^ 2

/-- The integer quadric is homogeneous of degree two. -/
theorem canonicalQuadricPolynomial25Three_isHomogeneous :
    canonicalQuadricPolynomial25Three.IsHomogeneous 2 := by
  have hMul (i j : Fin 4) :
      (MvPolynomial.X i * MvPolynomial.X j :
        HomogeneousRing25ThreeZ).IsHomogeneous 2 := by
    simpa using
      (MvPolynomial.isHomogeneous_X ℤ i).mul
        (MvPolynomial.isHomogeneous_X ℤ j)
  have hSq (i : Fin 4) :
      (MvPolynomial.X i ^ 2 :
        HomogeneousRing25ThreeZ).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow i 2
  unfold canonicalQuadricPolynomial25Three
  have h := (hMul 0 2).neg.sub (hMul 0 3)
  have h := h.add (hSq 1)
  have h := h.add (hMul 1 2)
  exact h.add (hMul 2 3)

/-- The integer cubic is homogeneous of degree three. -/
theorem canonicalCubicPolynomial25Three_isHomogeneous :
    canonicalCubicPolynomial25Three.IsHomogeneous 3 := by
  have hTriple (i j k : Fin 4) :
      (MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k :
        HomogeneousRing25ThreeZ).IsHomogeneous 3 := by
    simpa using
      ((MvPolynomial.isHomogeneous_X ℤ i).mul
        (MvPolynomial.isHomogeneous_X ℤ j)).mul
          (MvPolynomial.isHomogeneous_X ℤ k)
  have hSqMul (i j : Fin 4) :
      (MvPolynomial.X i ^ 2 * MvPolynomial.X j :
        HomogeneousRing25ThreeZ).IsHomogeneous 3 := by
    simpa using
      (MvPolynomial.isHomogeneous_X_pow i 2).mul
        (MvPolynomial.isHomogeneous_X ℤ j)
  have hMulSq (i j : Fin 4) :
      (MvPolynomial.X i * MvPolynomial.X j ^ 2 :
        HomogeneousRing25ThreeZ).IsHomogeneous 3 := by
    simpa using
      (MvPolynomial.isHomogeneous_X ℤ i).mul
        (MvPolynomial.isHomogeneous_X_pow j 2)
  unfold canonicalCubicPolynomial25Three
  have h := (hSqMul 0 3).add (hTriple 0 1 2)
  have h := h.sub (hTriple 0 1 3)
  have h := h.sub (hTriple 0 2 3)
  have h := h.add (hTriple 1 2 3)
  have h := h.add (hSqMul 2 3)
  exact h.sub (hMulSq 2 3)

/-- Coordinates as a function on the four polynomial variables. -/
def coordinates4ToFun25Three {K : Type*}
    (P : Coordinates4 K) : Fin 4 → K :=
  ![P.x, P.y, P.z, P.w]

/-- Evaluation casts integer coefficients and uses the order x,y,z,w. -/
def evaluateAt25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : HomogeneousRing25ThreeZ →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K)
    (coordinates4ToFun25Three P)

@[simp]
theorem evaluateAt25Three_C {K : Type*} [CommRing K]
    (P : Coordinates4 K) (a : ℤ) :
    evaluateAt25Three P (MvPolynomial.C a) = (a : K) := by
  exact MvPolynomial.eval₂Hom_C (Int.castRingHom K)
    (coordinates4ToFun25Three P) a

@[simp]
theorem evaluateAt25Three_X {K : Type*} [CommRing K]
    (P : Coordinates4 K) (i : Fin 4) :
    evaluateAt25Three P (MvPolynomial.X i) =
      coordinates4ToFun25Three P i := by
  exact MvPolynomial.eval₂Hom_X' (Int.castRingHom K)
    (coordinates4ToFun25Three P) i

/-- Polynomial evaluation recovers the existing canonical quadric. -/
@[simp]
theorem eval_canonicalQuadricPolynomial25Three
    {K : Type*} [Field K] (P : Coordinates4 K) :
    evaluateAt25Three P canonicalQuadricPolynomial25Three =
      canonicalQuadric25Three P := by
  simp [canonicalQuadricPolynomial25Three, canonicalQuadric25Three,
    coordinates4ToFun25Three] <;> ring

/-- Polynomial evaluation recovers the existing canonical cubic. -/
@[simp]
theorem eval_canonicalCubicPolynomial25Three
    {K : Type*} [Field K] (P : Coordinates4 K) :
    evaluateAt25Three P canonicalCubicPolynomial25Three =
      canonicalCubic25Three P := by
  simp [canonicalCubicPolynomial25Three, canonicalCubic25Three,
    coordinates4ToFun25Three] <;> ring

/-- The normalized curve predicate is exactly vanishing of both polynomials. -/
theorem isCanonicalNormalizedThree_iff_eval_eq_zero
    {K : Type*} [Field K] (P : NormalizedProjective4 K) :
    IsCanonicalNormalizedThree P ↔
      evaluateAt25Three (normalizedCoordinatesThree P)
          canonicalQuadricPolynomial25Three = 0 ∧
      evaluateAt25Three (normalizedCoordinatesThree P)
          canonicalCubicPolynomial25Three = 0 := by
  rw [eval_canonicalQuadricPolynomial25Three,
    eval_canonicalCubicPolynomial25Three]
  rfl

/-! ## Formal derivative identities over the integers -/

/-- The four partial derivatives of the integer quadric. -/
theorem pderiv_canonicalQuadricPolynomial25Three (i : Fin 4) :
    MvPolynomial.pderiv i canonicalQuadricPolynomial25Three =
      ![-MvPolynomial.X 2 - MvPolynomial.X 3,
        2 * MvPolynomial.X 1 + MvPolynomial.X 2,
        -MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 3,
        -MvPolynomial.X 0 + MvPolynomial.X 2] i := by
  fin_cases i <;>
    simp [canonicalQuadricPolynomial25Three,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      Pi.single_apply] <;> ring

/-- The four partial derivatives of the integer cubic. -/
theorem pderiv_canonicalCubicPolynomial25Three (i : Fin 4) :
    MvPolynomial.pderiv i canonicalCubicPolynomial25Three =
      ![2 * MvPolynomial.X 0 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 2 -
          MvPolynomial.X 1 * MvPolynomial.X 3 -
          MvPolynomial.X 2 * MvPolynomial.X 3,
        MvPolynomial.X 0 * MvPolynomial.X 2 -
          MvPolynomial.X 0 * MvPolynomial.X 3 +
          MvPolynomial.X 2 * MvPolynomial.X 3,
        MvPolynomial.X 0 * MvPolynomial.X 1 -
          MvPolynomial.X 0 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 3 +
          2 * MvPolynomial.X 2 * MvPolynomial.X 3 -
          MvPolynomial.X 3 ^ 2,
        MvPolynomial.X 0 ^ 2 -
          MvPolynomial.X 0 * MvPolynomial.X 1 -
          MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 2 ^ 2 -
          2 * MvPolynomial.X 2 * MvPolynomial.X 3] i := by
  fin_cases i <;>
    simp [canonicalCubicPolynomial25Three,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
      Pi.single_apply] <;> ring

/-! ## Evaluation of the formal rows in characteristic three -/

/-- Every evaluated quadric partial is the corresponding named gradient entry. -/
theorem eval_pderiv_canonicalQuadricPolynomial25Three
    {K : Type*} [CommRing K] [CharP K 3]
    (P : Coordinates4 K) (i : Fin 4) :
    evaluateAt25Three P
        (MvPolynomial.pderiv i canonicalQuadricPolynomial25Three) =
      coordinates4ToFun25Three (canonicalQuadricGradient25Three P) i := by
  rw [pderiv_canonicalQuadricPolynomial25Three i]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  have hEval2 :
      evaluateAt25Three P (2 : HomogeneousRing25ThreeZ) = (-1 : K) := by
    rw [map_ofNat, h2]
  fin_cases i <;>
    simp [coordinates4ToFun25Three,
      canonicalQuadricGradient25Three, hEval2] <;> ring

/-- Every evaluated cubic partial is the corresponding named gradient entry. -/
theorem eval_pderiv_canonicalCubicPolynomial25Three
    {K : Type*} [CommRing K] [CharP K 3]
    (P : Coordinates4 K) (i : Fin 4) :
    evaluateAt25Three P
        (MvPolynomial.pderiv i canonicalCubicPolynomial25Three) =
      coordinates4ToFun25Three (canonicalCubicGradient25Three P) i := by
  rw [pderiv_canonicalCubicPolynomial25Three i]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  have hEval2 :
      evaluateAt25Three P (2 : HomogeneousRing25ThreeZ) = (-1 : K) := by
    rw [map_ofNat, h2]
  fin_cases i <;>
    simp [coordinates4ToFun25Three,
      canonicalCubicGradient25Three, hEval2] <;> ring

/-! ## Formal minors and the existing six-minor certificate -/

/-- The integer formal Jacobian minor on columns i and j. -/
def formalJacobianMinor25Three (i j : Fin 4) :
    HomogeneousRing25ThreeZ :=
  MvPolynomial.pderiv i canonicalQuadricPolynomial25Three *
      MvPolynomial.pderiv j canonicalCubicPolynomial25Three -
    MvPolynomial.pderiv j canonicalQuadricPolynomial25Three *
      MvPolynomial.pderiv i canonicalCubicPolynomial25Three

/-- Evaluation identifies a formal minor with the named gradient determinant. -/
theorem eval_formalJacobianMinor25Three
    {K : Type*} [CommRing K] [CharP K 3]
    (P : Coordinates4 K) (i j : Fin 4) :
    evaluateAt25Three P (formalJacobianMinor25Three i j) =
      coordinates4ToFun25Three (canonicalQuadricGradient25Three P) i *
          coordinates4ToFun25Three (canonicalCubicGradient25Three P) j -
        coordinates4ToFun25Three (canonicalQuadricGradient25Three P) j *
          coordinates4ToFun25Three (canonicalCubicGradient25Three P) i := by
  simp only [formalJacobianMinor25Three, map_sub, map_mul,
    eval_pderiv_canonicalQuadricPolynomial25Three,
    eval_pderiv_canonicalCubicPolynomial25Three]

/-- The six evaluated formal minors, ordered xy,xz,xw,yz,yw,zw. -/
def evaluatedFormalJacobianMinors25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    CanonicalJacobianMinors25Three K :=
  ⟨evaluateAt25Three P (formalJacobianMinor25Three 0 1),
    evaluateAt25Three P (formalJacobianMinor25Three 0 2),
    evaluateAt25Three P (formalJacobianMinor25Three 0 3),
    evaluateAt25Three P (formalJacobianMinor25Three 1 2),
    evaluateAt25Three P (formalJacobianMinor25Three 1 3),
    evaluateAt25Three P (formalJacobianMinor25Three 2 3)⟩

/-- All six formal minors are exactly the minors in the existing certificate. -/
theorem evaluatedFormalJacobianMinors25Three_eq
    {K : Type*} [CommRing K] [CharP K 3] (P : Coordinates4 K) :
    evaluatedFormalJacobianMinors25Three P =
      canonicalJacobianMinors25Three P := by
  simp [evaluatedFormalJacobianMinors25Three,
    eval_formalJacobianMinor25Three, coordinates4ToFun25Three,
    canonicalJacobianMinors25Three]

/-- At every normalized curve point, an evaluated formal minor is nonzero.
The curve hypothesis supplies both equations in the singularity predicate. -/
theorem normalized_exists_formalJacobianMinor_ne_zero
    {K : Type*} [Field K] [CharP K 3]
    (P : NormalizedProjective4 K) (hP : IsCanonicalNormalizedThree P) :
    ∃ i j : Fin 4, i < j ∧
      evaluateAt25Three (normalizedCoordinatesThree P)
        (formalJacobianMinor25Three i j) ≠ 0 := by
  classical
  by_contra h
  have hzero (i j : Fin 4) (hij : i < j) :
      evaluateAt25Three (normalizedCoordinatesThree P)
        (formalJacobianMinor25Three i j) = 0 := by
    by_contra hm
    exact h ⟨i, j, hij, hm⟩
  have hM := evaluatedFormalJacobianMinors25Three_eq
    (normalizedCoordinatesThree P)
  apply normalized_projective_point_not_singular P
  refine ⟨hP.1, hP.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg CanonicalJacobianMinors25Three.xy hM).symm.trans
      (hzero (0 : Fin 4) (1 : Fin 4) (by decide))
  · exact (congrArg CanonicalJacobianMinors25Three.xz hM).symm.trans
      (hzero (0 : Fin 4) (2 : Fin 4) (by decide))
  · exact (congrArg CanonicalJacobianMinors25Three.xw hM).symm.trans
      (hzero (0 : Fin 4) (3 : Fin 4) (by decide))
  · exact (congrArg CanonicalJacobianMinors25Three.yz hM).symm.trans
      (hzero (1 : Fin 4) (2 : Fin 4) (by decide))
  · exact (congrArg CanonicalJacobianMinors25Three.yw hM).symm.trans
      (hzero (1 : Fin 4) (3 : Fin 4) (by decide))
  · exact (congrArg CanonicalJacobianMinors25Three.zw hM).symm.trans
      (hzero (2 : Fin 4) (3 : Fin 4) (by decide))

/-- The same result written directly as a determinant of evaluated partials. -/
theorem normalized_exists_evaluated_pderiv_minor_ne_zero
    {K : Type*} [Field K] [CharP K 3]
    (P : NormalizedProjective4 K) (hP : IsCanonicalNormalizedThree P) :
    ∃ i j : Fin 4, i < j ∧
      evaluateAt25Three (normalizedCoordinatesThree P)
          (MvPolynomial.pderiv i canonicalQuadricPolynomial25Three) *
        evaluateAt25Three (normalizedCoordinatesThree P)
          (MvPolynomial.pderiv j canonicalCubicPolynomial25Three) -
      evaluateAt25Three (normalizedCoordinatesThree P)
          (MvPolynomial.pderiv j canonicalQuadricPolynomial25Three) *
        evaluateAt25Three (normalizedCoordinatesThree P)
          (MvPolynomial.pderiv i canonicalCubicPolynomial25Three) ≠ 0 := by
  simpa only [formalJacobianMinor25Three, map_sub, map_mul] using
    normalized_exists_formalJacobianMinor_ne_zero P hP

end MazurProof.N25F_ThreeFormalJacobianBridge
