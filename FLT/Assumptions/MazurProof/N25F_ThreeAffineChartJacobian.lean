import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF3
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Affine-chart Jacobian rank for the characteristic-three N25 curve

For every projective pivot, this file dehomogenizes the canonical homogeneous
quadric and cubic by setting the pivot coordinate equal to one.  The other
three ambient coordinates index the affine polynomial variables.

The formal derivative chain rule identifies the two affine Jacobian rows with
the corresponding three non-pivot columns of the homogeneous Jacobian.  At a
normalized curve point, homogeneous Euler identities show that the pivot
column is controlled by those three free columns.  Consequently, if all
three affine `2 × 2` minors vanished, all six homogeneous minors would vanish,
contradicting the existing characteristic-three nonsingularity theorem.
-/

noncomputable section

namespace MazurProof.N25F_ThreeAffineChartJacobian

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmoothF3

/-! ## Generic ambient and affine polynomial rings -/

/-- The four-variable homogeneous polynomial ring over the selected
coefficient ring. -/
abbrev AmbientPolynomial25Three (K : Type*) [CommRing K] :=
  MvPolynomial (Fin 4) K

/-- The three affine coordinates on the chart whose distinguished homogeneous
coordinate is `pivot`. -/
abbrev AffineCoordinate25Three (pivot : Fin 4) :=
  {j : Fin 4 // j ≠ pivot}

/-- The ordinary three-variable affine polynomial ring on the selected
projective chart. -/
abbrev AffinePolynomial25Three (K : Type*) [CommRing K]
    (pivot : Fin 4) :=
  MvPolynomial (AffineCoordinate25Three pivot) K

/-- Read one of the four entries of a homogeneous coordinate vector. -/
def coordinate25Three {K : Type*} (P : Coordinates4 K) : Fin 4 → K :=
  ![P.x, P.y, P.z, P.w]

/-- The characteristic-three canonical quadric as a formal homogeneous
polynomial. -/
def canonicalQuadricPolynomial25Three
    {K : Type*} [CommRing K] : AmbientPolynomial25Three K :=
  -MvPolynomial.X 0 * MvPolynomial.X 2 -
    MvPolynomial.X 0 * MvPolynomial.X 3 +
    MvPolynomial.X 1 ^ 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 2 * MvPolynomial.X 3

/-- The characteristic-three canonical cubic as a formal homogeneous
polynomial. -/
def canonicalCubicPolynomial25Three
    {K : Type*} [CommRing K] : AmbientPolynomial25Three K :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 -
    MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 +
    MvPolynomial.X 2 ^ 2 * MvPolynomial.X 3 -
    MvPolynomial.X 2 * MvPolynomial.X 3 ^ 2

/-- Under dehomogenization, the pivot variable becomes one and every other
ambient variable becomes its canonically labelled affine variable. -/
def dehomogenizedVariable25Three
    {K : Type*} [CommRing K] (pivot j : Fin 4) :
    AffinePolynomial25Three K pivot :=
  if h : j ≠ pivot then MvPolynomial.X ⟨j, h⟩ else 1

/-- Set the selected homogeneous coordinate equal to one. -/
def ambientDehomogenize25Three
    {K : Type*} [CommRing K] (pivot : Fin 4) :
    AmbientPolynomial25Three K →+* AffinePolynomial25Three K pivot :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (dehomogenizedVariable25Three pivot)

/-- The dehomogenized canonical quadric on the chart `X_pivot = 1`. -/
def canonicalAffineQuadricPolynomial25Three
    {K : Type*} [CommRing K] (pivot : Fin 4) :
    AffinePolynomial25Three K pivot :=
  ambientDehomogenize25Three pivot
    (canonicalQuadricPolynomial25Three (K := K))

/-- The dehomogenized canonical cubic on the chart `X_pivot = 1`. -/
def canonicalAffineCubicPolynomial25Three
    {K : Type*} [CommRing K] (pivot : Fin 4) :
    AffinePolynomial25Three K pivot :=
  ambientDehomogenize25Three pivot
    (canonicalCubicPolynomial25Three (K := K))

@[simp]
theorem ambientDehomogenize_X25Three
    {K : Type*} [CommRing K] (pivot j : Fin 4) :
    ambientDehomogenize25Three pivot (MvPolynomial.X j : MvPolynomial (Fin 4) K) =
      dehomogenizedVariable25Three pivot j := by
  simp [ambientDehomogenize25Three]

/-! ## Formal derivative chain rule -/

/-- Differentiating one dehomogenized ambient variable agrees with first
differentiating in the corresponding ambient non-pivot coordinate and then
dehomogenizing. -/
@[simp]
theorem pderiv_dehomogenizedVariable25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (r : AffineCoordinate25Three pivot) (j : Fin 4) :
    MvPolynomial.pderiv r
        (dehomogenizedVariable25Three (K := K) pivot j) =
      ambientDehomogenize25Three pivot
        (MvPolynomial.pderiv r.1
          (MvPolynomial.X j : AmbientPolynomial25Three K)) := by
  by_cases hjp : j = pivot
  · subst j
    simp [dehomogenizedVariable25Three, ambientDehomogenize25Three, r.2]
  · by_cases hjr : j = r.1
    · subst j
      simp [dehomogenizedVariable25Three, ambientDehomogenize25Three, r.2]
    · have hsub :
          (⟨j, hjp⟩ : AffineCoordinate25Three pivot) ≠ r := by
        intro h
        exact hjr (congrArg Subtype.val h)
      have hjr' : r.1 ≠ j := Ne.symm hjr
      have hsub' : r ≠ (⟨j, hjp⟩ : AffineCoordinate25Three pivot) :=
        Ne.symm hsub
      simp [dehomogenizedVariable25Three, ambientDehomogenize25Three,
        hjp, hjr, hjr', hsub, hsub']

/-- Formal chain rule for the substitution `X_pivot = 1`: partial
differentiation in any free affine variable commutes with ambient
dehomogenization. -/
theorem pderiv_ambientDehomogenize25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (r : AffineCoordinate25Three pivot)
    (f : AmbientPolynomial25Three K) :
    MvPolynomial.pderiv r (ambientDehomogenize25Three pivot f) =
      ambientDehomogenize25Three pivot
        (MvPolynomial.pderiv r.1 f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp [ambientDehomogenize25Three]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.pderiv_mul, map_add]
      rw [hp, ambientDehomogenize_X25Three,
        pderiv_dehomogenizedVariable25Three]

/-! ## Evaluation on a chart point -/

/-- Restrict the four coordinates of `P` to the three non-pivot coordinate
labels. -/
def affineCoordinateValues25Three
    {K : Type*} (pivot : Fin 4) (P : Coordinates4 K) :
    AffineCoordinate25Three pivot → K :=
  fun j => coordinate25Three P j.1

/-- Evaluation of ambient four-variable polynomials at a homogeneous point. -/
def ambientEvaluation25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    AmbientPolynomial25Three K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (coordinate25Three P)

/-- Evaluation of affine chart polynomials at the three non-pivot entries of
`P`. -/
def affineEvaluation25Three
    {K : Type*} [CommRing K] (pivot : Fin 4) (P : Coordinates4 K) :
    AffinePolynomial25Three K pivot →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K)
    (affineCoordinateValues25Three pivot P)

@[simp]
theorem ambientEvaluation_X25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) (j : Fin 4) :
    ambientEvaluation25Three P (MvPolynomial.X j) =
      coordinate25Three P j := by
  simp [ambientEvaluation25Three]

/-- If the pivot entry of `P` is one, evaluating a dehomogenized ambient
variable recovers its original homogeneous coordinate. -/
@[simp]
theorem affineEvaluation_dehomogenizedVariable25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1) (j : Fin 4) :
    affineEvaluation25Three pivot P
        (dehomogenizedVariable25Three pivot j) =
      coordinate25Three P j := by
  by_cases hj : j ≠ pivot
  · simp [affineEvaluation25Three, affineCoordinateValues25Three,
      dehomogenizedVariable25Three, hj]
  · have hj' : j = pivot := by simpa using hj
    subst j
    simp [affineEvaluation25Three, affineCoordinateValues25Three,
      dehomogenizedVariable25Three, hpivot]

/-- Evaluation after dehomogenization agrees with ambient evaluation whenever
the pivot coordinate is one. -/
theorem affineEvaluation_ambientDehomogenize25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1)
    (f : AmbientPolynomial25Three K) :
    affineEvaluation25Three pivot P
        (ambientDehomogenize25Three pivot f) =
      ambientEvaluation25Three P f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp [affineEvaluation25Three, ambientEvaluation25Three,
        ambientDehomogenize25Three]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, ambientDehomogenize_X25Three,
        affineEvaluation_dehomogenizedVariable25Three
          pivot P hpivot j,
        ambientEvaluation_X25Three]

/-- Evaluating the formal homogeneous quadric recovers the existing
coordinate formula. -/
theorem ambientEvaluation_canonicalQuadricPolynomial25Three
    {K : Type*} [Field K] (P : Coordinates4 K) :
    ambientEvaluation25Three P
        (canonicalQuadricPolynomial25Three (K := K)) =
      canonicalQuadric25Three P := by
  rcases P with ⟨x, y, z, w⟩
  simp [ambientEvaluation25Three, coordinate25Three,
    canonicalQuadricPolynomial25Three, canonicalQuadric25Three] <;>
    ring

/-- Evaluating the formal homogeneous cubic recovers the existing coordinate
formula. -/
theorem ambientEvaluation_canonicalCubicPolynomial25Three
    {K : Type*} [Field K] (P : Coordinates4 K) :
    ambientEvaluation25Three P
        (canonicalCubicPolynomial25Three (K := K)) =
      canonicalCubic25Three P := by
  rcases P with ⟨x, y, z, w⟩
  simp [ambientEvaluation25Three, coordinate25Three,
    canonicalCubicPolynomial25Three, canonicalCubic25Three] <;>
    ring

/-- The generic dehomogenized quadric is the actual quadric equation on a
point whose pivot coordinate is one. -/
theorem affineEvaluation_canonicalAffineQuadric25Three
    {K : Type*} [Field K]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1) :
    affineEvaluation25Three pivot P
        (canonicalAffineQuadricPolynomial25Three (K := K) pivot) =
      canonicalQuadric25Three P := by
  rw [canonicalAffineQuadricPolynomial25Three,
    affineEvaluation_ambientDehomogenize25Three pivot P hpivot,
    ambientEvaluation_canonicalQuadricPolynomial25Three]

/-- The generic dehomogenized cubic is the actual cubic equation on a point
whose pivot coordinate is one. -/
theorem affineEvaluation_canonicalAffineCubic25Three
    {K : Type*} [Field K]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1) :
    affineEvaluation25Three pivot P
        (canonicalAffineCubicPolynomial25Three (K := K) pivot) =
      canonicalCubic25Three P := by
  rw [canonicalAffineCubicPolynomial25Three,
    affineEvaluation_ambientDehomogenize25Three pivot P hpivot,
    ambientEvaluation_canonicalCubicPolynomial25Three]

/-! ## Affine derivatives and homogeneous gradients -/

/-- Ambient evaluation of a formal quadric derivative is the corresponding
entry of the characteristic-three homogeneous gradient. -/
theorem ambientEvaluation_pderiv_canonicalQuadric25Three
    {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (a : Fin 4) :
    ambientEvaluation25Three P
        (MvPolynomial.pderiv a
          (canonicalQuadricPolynomial25Three (K := K))) =
      coordinate25Three (canonicalQuadricGradient25Three P) a := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  rcases P with ⟨x, y, z, w⟩
  fin_cases a <;>
    simp [ambientEvaluation25Three, coordinate25Three,
      canonicalQuadricPolynomial25Three,
      canonicalQuadricGradient25Three, h2] <;>
    ring

set_option maxHeartbeats 400000 in
/-- Ambient evaluation of a formal cubic derivative is the corresponding
entry of the characteristic-three homogeneous gradient. -/
theorem ambientEvaluation_pderiv_canonicalCubic25Three
    {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (a : Fin 4) :
    ambientEvaluation25Three P
        (MvPolynomial.pderiv a
          (canonicalCubicPolynomial25Three (K := K))) =
      coordinate25Three (canonicalCubicGradient25Three P) a := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  rcases P with ⟨x, y, z, w⟩
  fin_cases a <;>
    simp [ambientEvaluation25Three, coordinate25Three,
      canonicalCubicPolynomial25Three,
      canonicalCubicGradient25Three, h2] <;>
    ring

/-- The partial derivatives of the dehomogenized quadric are the three
non-pivot entries of the homogeneous quadric gradient. -/
theorem affineEvaluation_pderiv_canonicalAffineQuadric25Three
    {K : Type*} [Field K] [CharP K 3]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1)
    (a : AffineCoordinate25Three pivot) :
    affineEvaluation25Three pivot P
        (MvPolynomial.pderiv a
          (canonicalAffineQuadricPolynomial25Three (K := K) pivot)) =
      coordinate25Three (canonicalQuadricGradient25Three P) a.1 := by
  rw [canonicalAffineQuadricPolynomial25Three,
    pderiv_ambientDehomogenize25Three,
    affineEvaluation_ambientDehomogenize25Three pivot P hpivot,
    ambientEvaluation_pderiv_canonicalQuadric25Three]

/-- The partial derivatives of the dehomogenized cubic are the three
non-pivot entries of the homogeneous cubic gradient. -/
theorem affineEvaluation_pderiv_canonicalAffineCubic25Three
    {K : Type*} [Field K] [CharP K 3]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1)
    (a : AffineCoordinate25Three pivot) :
    affineEvaluation25Three pivot P
        (MvPolynomial.pderiv a
          (canonicalAffineCubicPolynomial25Three (K := K) pivot)) =
      coordinate25Three (canonicalCubicGradient25Three P) a.1 := by
  rw [canonicalAffineCubicPolynomial25Three,
    pderiv_ambientDehomogenize25Three,
    affineEvaluation_ambientDehomogenize25Three pivot P hpivot,
    ambientEvaluation_pderiv_canonicalCubic25Three]

/-! ## Affine and homogeneous Jacobian minors -/

/-- A two-by-two minor of the homogeneous `2 × 4` Jacobian. -/
def homogeneousJacobianMinor25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) (a b : Fin 4) : K :=
  coordinate25Three (canonicalQuadricGradient25Three P) a *
      coordinate25Three (canonicalCubicGradient25Three P) b -
    coordinate25Three (canonicalQuadricGradient25Three P) b *
      coordinate25Three (canonicalCubicGradient25Three P) a

/-- A two-by-two minor of the dehomogenized `2 × 3` affine Jacobian. -/
def affineJacobianMinor25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (P : Coordinates4 K)
    (a b : AffineCoordinate25Three pivot) : K :=
  affineEvaluation25Three pivot P
      (MvPolynomial.pderiv a
        (canonicalAffineQuadricPolynomial25Three (K := K) pivot)) *
    affineEvaluation25Three pivot P
      (MvPolynomial.pderiv b
        (canonicalAffineCubicPolynomial25Three (K := K) pivot)) -
  affineEvaluation25Three pivot P
      (MvPolynomial.pderiv b
        (canonicalAffineQuadricPolynomial25Three (K := K) pivot)) *
    affineEvaluation25Three pivot P
      (MvPolynomial.pderiv a
        (canonicalAffineCubicPolynomial25Three (K := K) pivot))

/-- The pointwise assertion that the affine `2 × 3` Jacobian has rank two. -/
def AffineJacobianRankTwoAt25Three
    {K : Type*} [CommRing K]
    (pivot : Fin 4) (P : Coordinates4 K) : Prop :=
  ∃ a b : AffineCoordinate25Three pivot,
    a ≠ b ∧ affineJacobianMinor25Three pivot P a b ≠ 0

/-- Every affine Jacobian minor is the corresponding non-pivot homogeneous
minor when the pivot coordinate is one. -/
theorem affineJacobianMinor_eq_homogeneous25Three
    {K : Type*} [Field K] [CharP K 3]
    (pivot : Fin 4) (P : Coordinates4 K)
    (hpivot : coordinate25Three P pivot = 1)
    (a b : AffineCoordinate25Three pivot) :
    affineJacobianMinor25Three pivot P a b =
      homogeneousJacobianMinor25Three P a.1 b.1 := by
  unfold affineJacobianMinor25Three homogeneousJacobianMinor25Three
  rw [affineEvaluation_pderiv_canonicalAffineQuadric25Three
        pivot P hpivot a,
    affineEvaluation_pderiv_canonicalAffineCubic25Three
        pivot P hpivot b,
    affineEvaluation_pderiv_canonicalAffineQuadric25Three
        pivot P hpivot b,
    affineEvaluation_pderiv_canonicalAffineCubic25Three
        pivot P hpivot a]

/-- Reversing the two columns reverses the sign of the minor. -/
theorem homogeneousJacobianMinor_swap25Three
    {K : Type*} [CommRing K]
    (P : Coordinates4 K) (a b : Fin 4) :
    homogeneousJacobianMinor25Three P a b =
      -homogeneousJacobianMinor25Three P b a := by
  unfold homogeneousJacobianMinor25Three
  ring

/-- A repeated-column homogeneous minor is zero. -/
@[simp]
theorem homogeneousJacobianMinor_self25Three
    {K : Type*} [CommRing K]
    (P : Coordinates4 K) (a : Fin 4) :
    homogeneousJacobianMinor25Three P a a = 0 := by
  simp [homogeneousJacobianMinor25Three]

@[simp]
theorem homogeneousJacobianMinor_xy25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 0 1 =
      (canonicalJacobianMinors25Three P).xy := rfl

@[simp]
theorem homogeneousJacobianMinor_xz25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 0 2 =
      (canonicalJacobianMinors25Three P).xz := rfl

@[simp]
theorem homogeneousJacobianMinor_xw25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 0 3 =
      (canonicalJacobianMinors25Three P).xw := rfl

@[simp]
theorem homogeneousJacobianMinor_yz25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 1 2 =
      (canonicalJacobianMinors25Three P).yz := rfl

@[simp]
theorem homogeneousJacobianMinor_yw25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 1 3 =
      (canonicalJacobianMinors25Three P).yw := rfl

@[simp]
theorem homogeneousJacobianMinor_zw25Three
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    homogeneousJacobianMinor25Three P 2 3 =
      (canonicalJacobianMinors25Three P).zw := rfl

/-! ## Homogeneous Euler identities -/

/-- Euler's identity for the characteristic-three homogeneous quadric. -/
theorem canonicalQuadricGradient_euler25Three
    {K : Type*} [Field K] [CharP K 3] (P : Coordinates4 K) :
    P.x * (canonicalQuadricGradient25Three P).x +
      P.y * (canonicalQuadricGradient25Three P).y +
      P.z * (canonicalQuadricGradient25Three P).z +
      P.w * (canonicalQuadricGradient25Three P).w =
        2 * canonicalQuadric25Three P := by
  rcases P with ⟨x, y, z, w⟩
  dsimp [canonicalQuadricGradient25Three, canonicalQuadric25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination (-y ^ 2) * h3

set_option maxHeartbeats 400000 in
/-- Euler's identity for the characteristic-three homogeneous cubic. -/
theorem canonicalCubicGradient_euler25Three
    {K : Type*} [Field K] [CharP K 3] (P : Coordinates4 K) :
    P.x * (canonicalCubicGradient25Three P).x +
      P.y * (canonicalCubicGradient25Three P).y +
      P.z * (canonicalCubicGradient25Three P).z +
      P.w * (canonicalCubicGradient25Three P).w =
        3 * canonicalCubic25Three P := by
  rcases P with ⟨x, y, z, w⟩
  dsimp [canonicalCubicGradient25Three, canonicalCubic25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  ring_nf
  simp [h3]

/-- On the complete intersection, the weighted sum of homogeneous minors
against any fixed column vanishes.  This is the minor form of the two Euler
identities. -/
theorem homogeneousJacobianMinor_weighted_sum_zero25Three
    {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (a : Fin 4)
    (hQ : canonicalQuadric25Three P = 0)
    (hC : canonicalCubic25Three P = 0) :
    P.x * homogeneousJacobianMinor25Three P 0 a +
      P.y * homogeneousJacobianMinor25Three P 1 a +
      P.z * homogeneousJacobianMinor25Three P 2 a +
      P.w * homogeneousJacobianMinor25Three P 3 a = 0 := by
  have hQE :
      P.x * (canonicalQuadricGradient25Three P).x +
        P.y * (canonicalQuadricGradient25Three P).y +
        P.z * (canonicalQuadricGradient25Three P).z +
        P.w * (canonicalQuadricGradient25Three P).w = 0 := by
    calc
      _ = 2 * canonicalQuadric25Three P :=
        canonicalQuadricGradient_euler25Three P
      _ = 0 := by rw [hQ, mul_zero]
  have hCE :
      P.x * (canonicalCubicGradient25Three P).x +
        P.y * (canonicalCubicGradient25Three P).y +
        P.z * (canonicalCubicGradient25Three P).z +
        P.w * (canonicalCubicGradient25Three P).w = 0 := by
    calc
      _ = 3 * canonicalCubic25Three P :=
        canonicalCubicGradient_euler25Three P
      _ = 0 := by rw [hC, mul_zero]
  calc
    P.x * homogeneousJacobianMinor25Three P 0 a +
        P.y * homogeneousJacobianMinor25Three P 1 a +
        P.z * homogeneousJacobianMinor25Three P 2 a +
        P.w * homogeneousJacobianMinor25Three P 3 a =
      (P.x * (canonicalQuadricGradient25Three P).x +
          P.y * (canonicalQuadricGradient25Three P).y +
          P.z * (canonicalQuadricGradient25Three P).z +
          P.w * (canonicalQuadricGradient25Three P).w) *
            coordinate25Three (canonicalCubicGradient25Three P) a -
        coordinate25Three (canonicalQuadricGradient25Three P) a *
          (P.x * (canonicalCubicGradient25Three P).x +
            P.y * (canonicalCubicGradient25Three P).y +
            P.z * (canonicalCubicGradient25Three P).z +
            P.w * (canonicalCubicGradient25Three P).w) := by
      unfold homogeneousJacobianMinor25Three
      fin_cases a <;> simp [coordinate25Three] <;> ring
    _ = 0 := by rw [hQE, hCE]; ring

/-- Package the two equations and six generic minor equalities into the
existing singularity predicate. -/
theorem isCanonicalSingular25Three_of_minors_zero
    {K : Type*} [Field K]
    (P : Coordinates4 K)
    (hQ : canonicalQuadric25Three P = 0)
    (hC : canonicalCubic25Three P = 0)
    (hxy : homogeneousJacobianMinor25Three P 0 1 = 0)
    (hxz : homogeneousJacobianMinor25Three P 0 2 = 0)
    (hxw : homogeneousJacobianMinor25Three P 0 3 = 0)
    (hyz : homogeneousJacobianMinor25Three P 1 2 = 0)
    (hyw : homogeneousJacobianMinor25Three P 1 3 = 0)
    (hzw : homogeneousJacobianMinor25Three P 2 3 = 0) :
    IsCanonicalSingular25Three P := by
  unfold IsCanonicalSingular25Three
  dsimp only
  refine ⟨hQ, hC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hxy
  · simpa using hxz
  · simpa using hxw
  · simpa using hyz
  · simpa using hyw
  · simpa using hzw

/-! ## Named free coordinates on the four normalized charts -/

def xChartY25Three : AffineCoordinate25Three 0 := ⟨1, by decide⟩
def xChartZ25Three : AffineCoordinate25Three 0 := ⟨2, by decide⟩
def xChartW25Three : AffineCoordinate25Three 0 := ⟨3, by decide⟩

def yChartX25Three : AffineCoordinate25Three 1 := ⟨0, by decide⟩
def yChartZ25Three : AffineCoordinate25Three 1 := ⟨2, by decide⟩
def yChartW25Three : AffineCoordinate25Three 1 := ⟨3, by decide⟩

def zChartX25Three : AffineCoordinate25Three 2 := ⟨0, by decide⟩
def zChartY25Three : AffineCoordinate25Three 2 := ⟨1, by decide⟩
def zChartW25Three : AffineCoordinate25Three 2 := ⟨3, by decide⟩

def wChartX25Three : AffineCoordinate25Three 3 := ⟨0, by decide⟩
def wChartY25Three : AffineCoordinate25Three 3 := ⟨1, by decide⟩
def wChartZ25Three : AffineCoordinate25Three 3 := ⟨2, by decide⟩

/-! ## Pointwise rank-two theorem on each normalized chart -/

/-- On the normalized `x=1` chart, at least one of the `yz`, `yw`, `zw`
affine minors is nonzero. -/
theorem xChart_affineJacobian_rankTwo25Three
    {K : Type*} [Field K] [CharP K 3]
    (y z w : K)
    (hcurve : IsCanonicalNormalizedThree (.xChart y z w)) :
    AffineJacobianRankTwoAt25Three 0
      (⟨1, y, z, w⟩ : Coordinates4 K) := by
  classical
  let P : Coordinates4 K := ⟨1, y, z, w⟩
  have hpivot : coordinate25Three P 0 = 1 := rfl
  have hcurve' :
      canonicalQuadric25Three P = 0 ∧ canonicalCubic25Three P = 0 := by
    simpa [P, IsCanonicalNormalizedThree, normalizedCoordinatesThree] using hcurve
  rcases hcurve' with ⟨hQ, hC⟩
  by_contra hRank
  unfold AffineJacobianRankTwoAt25Three at hRank
  have hzero
      (a b : AffineCoordinate25Three (0 : Fin 4)) (hab : a ≠ b) :
      affineJacobianMinor25Three 0 P a b = 0 := by
    by_contra hne
    exact hRank ⟨a, b, hab, hne⟩
  have hfree
      (a b : AffineCoordinate25Three (0 : Fin 4)) (hab : a ≠ b) :
      homogeneousJacobianMinor25Three P a.1 b.1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P a.1 b.1 =
          affineJacobianMinor25Three 0 P a b :=
        (affineJacobianMinor_eq_homogeneous25Three
          0 P hpivot a b).symm
      _ = 0 := hzero a b hab
  have h12 : homogeneousJacobianMinor25Three P 1 2 = 0 := by
    simpa [xChartY25Three, xChartZ25Three] using
      (hfree xChartY25Three xChartZ25Three (by decide))
  have h13 : homogeneousJacobianMinor25Three P 1 3 = 0 := by
    simpa [xChartY25Three, xChartW25Three] using
      (hfree xChartY25Three xChartW25Three (by decide))
  have h23 : homogeneousJacobianMinor25Three P 2 3 = 0 := by
    simpa [xChartZ25Three, xChartW25Three] using
      (hfree xChartZ25Three xChartW25Three (by decide))
  have h21 : homogeneousJacobianMinor25Three P 2 1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 2 1 =
          -homogeneousJacobianMinor25Three P 1 2 :=
        homogeneousJacobianMinor_swap25Three P 2 1
      _ = 0 := by rw [h12]; simp
  have h31 : homogeneousJacobianMinor25Three P 3 1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 1 =
          -homogeneousJacobianMinor25Three P 1 3 :=
        homogeneousJacobianMinor_swap25Three P 3 1
      _ = 0 := by rw [h13]; simp
  have h32 : homogeneousJacobianMinor25Three P 3 2 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 2 =
          -homogeneousJacobianMinor25Three P 2 3 :=
        homogeneousJacobianMinor_swap25Three P 3 2
      _ = 0 := by rw [h23]; simp
  have h01 : homogeneousJacobianMinor25Three P 0 1 = 0 := by
    simpa [P, h21, h31] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (1 : Fin 4) hQ hC)
  have h02 : homogeneousJacobianMinor25Three P 0 2 = 0 := by
    simpa [P, h12, h32] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (2 : Fin 4) hQ hC)
  have h03 : homogeneousJacobianMinor25Three P 0 3 = 0 := by
    simpa [P, h13, h23] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (3 : Fin 4) hQ hC)
  have hsng : IsCanonicalSingular25Three P :=
    isCanonicalSingular25Three_of_minors_zero
      P hQ hC h01 h02 h03 h12 h13 h23
  exact
    (normalized_projective_point_not_singular (.xChart y z w))
      (by simpa [P, normalizedCoordinatesThree] using hsng)

/-- On the normalized `y=1` chart, at least one of the `xz`, `xw`, `zw`
affine minors is nonzero. -/
theorem yChart_affineJacobian_rankTwo25Three
    {K : Type*} [Field K] [CharP K 3]
    (z w : K)
    (hcurve : IsCanonicalNormalizedThree (.yChart z w)) :
    AffineJacobianRankTwoAt25Three 1
      (⟨0, 1, z, w⟩ : Coordinates4 K) := by
  classical
  let P : Coordinates4 K := ⟨0, 1, z, w⟩
  have hpivot : coordinate25Three P 1 = 1 := rfl
  have hcurve' :
      canonicalQuadric25Three P = 0 ∧ canonicalCubic25Three P = 0 := by
    simpa [P, IsCanonicalNormalizedThree, normalizedCoordinatesThree] using hcurve
  rcases hcurve' with ⟨hQ, hC⟩
  by_contra hRank
  unfold AffineJacobianRankTwoAt25Three at hRank
  have hzero
      (a b : AffineCoordinate25Three (1 : Fin 4)) (hab : a ≠ b) :
      affineJacobianMinor25Three 1 P a b = 0 := by
    by_contra hne
    exact hRank ⟨a, b, hab, hne⟩
  have hfree
      (a b : AffineCoordinate25Three (1 : Fin 4)) (hab : a ≠ b) :
      homogeneousJacobianMinor25Three P a.1 b.1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P a.1 b.1 =
          affineJacobianMinor25Three 1 P a b :=
        (affineJacobianMinor_eq_homogeneous25Three
          1 P hpivot a b).symm
      _ = 0 := hzero a b hab
  have h02 : homogeneousJacobianMinor25Three P 0 2 = 0 := by
    simpa [yChartX25Three, yChartZ25Three] using
      (hfree yChartX25Three yChartZ25Three (by decide))
  have h03 : homogeneousJacobianMinor25Three P 0 3 = 0 := by
    simpa [yChartX25Three, yChartW25Three] using
      (hfree yChartX25Three yChartW25Three (by decide))
  have h23 : homogeneousJacobianMinor25Three P 2 3 = 0 := by
    simpa [yChartZ25Three, yChartW25Three] using
      (hfree yChartZ25Three yChartW25Three (by decide))
  have h20 : homogeneousJacobianMinor25Three P 2 0 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 2 0 =
          -homogeneousJacobianMinor25Three P 0 2 :=
        homogeneousJacobianMinor_swap25Three P 2 0
      _ = 0 := by rw [h02]; simp
  have h30 : homogeneousJacobianMinor25Three P 3 0 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 0 =
          -homogeneousJacobianMinor25Three P 0 3 :=
        homogeneousJacobianMinor_swap25Three P 3 0
      _ = 0 := by rw [h03]; simp
  have h32 : homogeneousJacobianMinor25Three P 3 2 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 2 =
          -homogeneousJacobianMinor25Three P 2 3 :=
        homogeneousJacobianMinor_swap25Three P 3 2
      _ = 0 := by rw [h23]; simp
  have h10 : homogeneousJacobianMinor25Three P 1 0 = 0 := by
    simpa [P, h20, h30] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (0 : Fin 4) hQ hC)
  have h01 : homogeneousJacobianMinor25Three P 0 1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 0 1 =
          -homogeneousJacobianMinor25Three P 1 0 :=
        homogeneousJacobianMinor_swap25Three P 0 1
      _ = 0 := by rw [h10]; simp
  have h12 : homogeneousJacobianMinor25Three P 1 2 = 0 := by
    simpa [P, h02, h32] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (2 : Fin 4) hQ hC)
  have h13 : homogeneousJacobianMinor25Three P 1 3 = 0 := by
    simpa [P, h03, h23] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (3 : Fin 4) hQ hC)
  have hsng : IsCanonicalSingular25Three P :=
    isCanonicalSingular25Three_of_minors_zero
      P hQ hC h01 h02 h03 h12 h13 h23
  exact
    (normalized_projective_point_not_singular (.yChart z w))
      (by simpa [P, normalizedCoordinatesThree] using hsng)

/-- On the normalized `z=1` chart, at least one of the `xy`, `xw`, `yw`
affine minors is nonzero. -/
theorem zChart_affineJacobian_rankTwo25Three
    {K : Type*} [Field K] [CharP K 3]
    (w : K)
    (hcurve : IsCanonicalNormalizedThree (.zChart w)) :
    AffineJacobianRankTwoAt25Three 2
      (⟨0, 0, 1, w⟩ : Coordinates4 K) := by
  classical
  let P : Coordinates4 K := ⟨0, 0, 1, w⟩
  have hpivot : coordinate25Three P 2 = 1 := rfl
  have hcurve' :
      canonicalQuadric25Three P = 0 ∧ canonicalCubic25Three P = 0 := by
    simpa [P, IsCanonicalNormalizedThree, normalizedCoordinatesThree] using hcurve
  rcases hcurve' with ⟨hQ, hC⟩
  by_contra hRank
  unfold AffineJacobianRankTwoAt25Three at hRank
  have hzero
      (a b : AffineCoordinate25Three (2 : Fin 4)) (hab : a ≠ b) :
      affineJacobianMinor25Three 2 P a b = 0 := by
    by_contra hne
    exact hRank ⟨a, b, hab, hne⟩
  have hfree
      (a b : AffineCoordinate25Three (2 : Fin 4)) (hab : a ≠ b) :
      homogeneousJacobianMinor25Three P a.1 b.1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P a.1 b.1 =
          affineJacobianMinor25Three 2 P a b :=
        (affineJacobianMinor_eq_homogeneous25Three
          2 P hpivot a b).symm
      _ = 0 := hzero a b hab
  have h01 : homogeneousJacobianMinor25Three P 0 1 = 0 := by
    simpa [zChartX25Three, zChartY25Three] using
      (hfree zChartX25Three zChartY25Three (by decide))
  have h03 : homogeneousJacobianMinor25Three P 0 3 = 0 := by
    simpa [zChartX25Three, zChartW25Three] using
      (hfree zChartX25Three zChartW25Three (by decide))
  have h13 : homogeneousJacobianMinor25Three P 1 3 = 0 := by
    simpa [zChartY25Three, zChartW25Three] using
      (hfree zChartY25Three zChartW25Three (by decide))
  have h30 : homogeneousJacobianMinor25Three P 3 0 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 0 =
          -homogeneousJacobianMinor25Three P 0 3 :=
        homogeneousJacobianMinor_swap25Three P 3 0
      _ = 0 := by rw [h03]; simp
  have h31 : homogeneousJacobianMinor25Three P 3 1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 3 1 =
          -homogeneousJacobianMinor25Three P 1 3 :=
        homogeneousJacobianMinor_swap25Three P 3 1
      _ = 0 := by rw [h13]; simp
  have h20 : homogeneousJacobianMinor25Three P 2 0 = 0 := by
    simpa [P, h30] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (0 : Fin 4) hQ hC)
  have h02 : homogeneousJacobianMinor25Three P 0 2 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 0 2 =
          -homogeneousJacobianMinor25Three P 2 0 :=
        homogeneousJacobianMinor_swap25Three P 0 2
      _ = 0 := by rw [h20]; simp
  have h21 : homogeneousJacobianMinor25Three P 2 1 = 0 := by
    simpa [P, h31] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (1 : Fin 4) hQ hC)
  have h12 : homogeneousJacobianMinor25Three P 1 2 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 1 2 =
          -homogeneousJacobianMinor25Three P 2 1 :=
        homogeneousJacobianMinor_swap25Three P 1 2
      _ = 0 := by rw [h21]; simp
  have h23 : homogeneousJacobianMinor25Three P 2 3 = 0 := by
    simpa [P, h03, h13] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (3 : Fin 4) hQ hC)
  have hsng : IsCanonicalSingular25Three P :=
    isCanonicalSingular25Three_of_minors_zero
      P hQ hC h01 h02 h03 h12 h13 h23
  exact
    (normalized_projective_point_not_singular (.zChart w))
      (by simpa [P, normalizedCoordinatesThree] using hsng)

/-- At the normalized `w=1` point, at least one of the `xy`, `xz`, `yz`
affine minors is nonzero. -/
theorem wChart_affineJacobian_rankTwo25Three
    {K : Type*} [Field K] [CharP K 3]
    (hcurve : IsCanonicalNormalizedThree
      (.wChart : NormalizedProjective4 K)) :
    AffineJacobianRankTwoAt25Three 3
      (⟨0, 0, 0, 1⟩ : Coordinates4 K) := by
  classical
  let P : Coordinates4 K := ⟨0, 0, 0, 1⟩
  have hpivot : coordinate25Three P 3 = 1 := rfl
  have hcurve' :
      canonicalQuadric25Three P = 0 ∧ canonicalCubic25Three P = 0 := by
    simpa [P, IsCanonicalNormalizedThree, normalizedCoordinatesThree] using hcurve
  rcases hcurve' with ⟨hQ, hC⟩
  by_contra hRank
  unfold AffineJacobianRankTwoAt25Three at hRank
  have hzero
      (a b : AffineCoordinate25Three (3 : Fin 4)) (hab : a ≠ b) :
      affineJacobianMinor25Three 3 P a b = 0 := by
    by_contra hne
    exact hRank ⟨a, b, hab, hne⟩
  have hfree
      (a b : AffineCoordinate25Three (3 : Fin 4)) (hab : a ≠ b) :
      homogeneousJacobianMinor25Three P a.1 b.1 = 0 := by
    calc
      homogeneousJacobianMinor25Three P a.1 b.1 =
          affineJacobianMinor25Three 3 P a b :=
        (affineJacobianMinor_eq_homogeneous25Three
          3 P hpivot a b).symm
      _ = 0 := hzero a b hab
  have h01 : homogeneousJacobianMinor25Three P 0 1 = 0 := by
    simpa [wChartX25Three, wChartY25Three] using
      (hfree wChartX25Three wChartY25Three (by decide))
  have h02 : homogeneousJacobianMinor25Three P 0 2 = 0 := by
    simpa [wChartX25Three, wChartZ25Three] using
      (hfree wChartX25Three wChartZ25Three (by decide))
  have h12 : homogeneousJacobianMinor25Three P 1 2 = 0 := by
    simpa [wChartY25Three, wChartZ25Three] using
      (hfree wChartY25Three wChartZ25Three (by decide))
  have h30 : homogeneousJacobianMinor25Three P 3 0 = 0 := by
    simpa [P] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (0 : Fin 4) hQ hC)
  have h03 : homogeneousJacobianMinor25Three P 0 3 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 0 3 =
          -homogeneousJacobianMinor25Three P 3 0 :=
        homogeneousJacobianMinor_swap25Three P 0 3
      _ = 0 := by rw [h30]; simp
  have h31 : homogeneousJacobianMinor25Three P 3 1 = 0 := by
    simpa [P] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (1 : Fin 4) hQ hC)
  have h13 : homogeneousJacobianMinor25Three P 1 3 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 1 3 =
          -homogeneousJacobianMinor25Three P 3 1 :=
        homogeneousJacobianMinor_swap25Three P 1 3
      _ = 0 := by rw [h31]; simp
  have h32 : homogeneousJacobianMinor25Three P 3 2 = 0 := by
    simpa [P] using
      (homogeneousJacobianMinor_weighted_sum_zero25Three
        P (2 : Fin 4) hQ hC)
  have h23 : homogeneousJacobianMinor25Three P 2 3 = 0 := by
    calc
      homogeneousJacobianMinor25Three P 2 3 =
          -homogeneousJacobianMinor25Three P 3 2 :=
        homogeneousJacobianMinor_swap25Three P 2 3
      _ = 0 := by rw [h32]; simp
  have hsng : IsCanonicalSingular25Three P :=
    isCanonicalSingular25Three_of_minors_zero
      P hQ hC h01 h02 h03 h12 h13 h23
  exact
    (normalized_projective_point_not_singular
      (.wChart : NormalizedProjective4 K))
      (by simpa [P, normalizedCoordinatesThree] using hsng)

/-! ## Uniform normalized-point statement -/

/-- The distinguished coordinate of each first-nonzero normalized chart. -/
def normalizedChartPivot25Three {K : Type*} :
    NormalizedProjective4 K → Fin 4
  | .xChart _ _ _ => 0
  | .yChart _ _ => 1
  | .zChart _ => 2
  | .wChart => 3

/-- At every normalized characteristic-three point of the canonical N25
curve, the `2 × 3` Jacobian of the two dehomogenized chart equations has a
nonzero `2 × 2` minor. -/
theorem normalized_projective_point_affineJacobian_rankTwo25Three
    {K : Type*} [Field K] [CharP K 3]
    (P : NormalizedProjective4 K)
    (hP : IsCanonicalNormalizedThree P) :
    AffineJacobianRankTwoAt25Three
      (normalizedChartPivot25Three P) (normalizedCoordinatesThree P) := by
  cases P with
  | xChart y z w =>
      simpa [normalizedChartPivot25Three, normalizedCoordinatesThree] using
        xChart_affineJacobian_rankTwo25Three y z w hP
  | yChart z w =>
      simpa [normalizedChartPivot25Three, normalizedCoordinatesThree] using
        yChart_affineJacobian_rankTwo25Three z w hP
  | zChart w =>
      simpa [normalizedChartPivot25Three, normalizedCoordinatesThree] using
        zChart_affineJacobian_rankTwo25Three w hP
  | wChart =>
      simpa [normalizedChartPivot25Three, normalizedCoordinatesThree] using
        wChart_affineJacobian_rankTwo25Three (K := K) hP

end MazurProof.N25F_ThreeAffineChartJacobian
