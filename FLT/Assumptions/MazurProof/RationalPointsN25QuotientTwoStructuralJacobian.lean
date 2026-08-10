import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCharts
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Structural Jacobian identities for the N25 affine charts

This module proves the two identities that connect the homogeneous canonical
model to every standard affine chart.  First, dehomogenization commutes with
differentiation in a non-pivot coordinate.  Second, Euler's identity for the
homogeneous quadric and cubic controls the weighted sums of their Jacobian
minors.  These statements replace chart-by-chart expansion of derivatives.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoStructuralJacobian

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoAffineCharts

/-- The affine variable in position `r`, labelled by its original ambient
coordinate rather than by a chart-specific permutation. -/
def affineCoordinate (pivot : Fin 4) (r : Fin 3) : OtherCoordinate pivot :=
  finSuccAboveEquiv pivot r

/-- A non-pivot ambient variable dehomogenizes to its canonically labelled
affine variable. -/
@[simp]
theorem dehomogenizedVariable_succAbove (pivot : Fin 4) (r : Fin 3) :
    dehomogenizedVariable pivot (pivot.succAbove r) =
      MvPolynomial.X (affineCoordinate pivot r) := by
  simp [dehomogenizedVariable, affineCoordinate, finSuccAboveEquiv_apply]

/-- Dehomogenization sends a variable to the corresponding normalized
coordinate by definition.  Naming this equality prevents the elaborator from
unfolding the whole evaluation homomorphism in later chain-rule rewrites. -/
@[simp]
theorem ambientDehomogenize_X (pivot j : Fin 4) :
    ambientDehomogenize pivot (MvPolynomial.X j) =
      dehomogenizedVariable pivot j := by
  simp [ambientDehomogenize]

/-- The derivative of a dehomogenized ambient variable is the
dehomogenization of its ambient derivative.  The pivot variable contributes
zero because it was specialized to one. -/
@[simp]
theorem pderiv_dehomogenizedVariable
    (pivot : Fin 4) (r : Fin 3) (j : Fin 4) :
    MvPolynomial.pderiv (affineCoordinate pivot r)
        (dehomogenizedVariable pivot j) =
      ambientDehomogenize pivot
        (MvPolynomial.pderiv (pivot.succAbove r)
          (MvPolynomial.X j : S)) := by
  by_cases hjp : j = pivot
  · subst j
    simp [dehomogenizedVariable, affineCoordinate]
  · by_cases hjs : j = pivot.succAbove r
    · subst j
      simp [affineCoordinate, finSuccAboveEquiv_apply]
    · simp [dehomogenizedVariable, affineCoordinate,
        finSuccAboveEquiv_apply, hjp, hjs]

/-- Formal chain rule for the substitution `X_pivot = 1`: differentiating
in a free affine coordinate commutes with ambient dehomogenization. -/
theorem pderiv_ambientDehomogenize
    (pivot : Fin 4) (r : Fin 3) (f : S) :
    MvPolynomial.pderiv (affineCoordinate pivot r)
        (ambientDehomogenize pivot f) =
      ambientDehomogenize pivot
        (MvPolynomial.pderiv (pivot.succAbove r) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp [ambientDehomogenize]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.pderiv_mul, map_add]
      rw [hp, ambientDehomogenize_X, pderiv_dehomogenizedVariable]

/-- The ambient polynomial Jacobian minor formed from the homogeneous
quadric and cubic. -/
def ambientPolynomialMinor (a b : Fin 4) : S :=
  MvPolynomial.pderiv a canonicalQuadricPolynomial25Two *
      MvPolynomial.pderiv b canonicalCubicPolynomial25Two -
    MvPolynomial.pderiv b canonicalQuadricPolynomial25Two *
      MvPolynomial.pderiv a canonicalCubicPolynomial25Two

/-- The coordinate-form Jacobian minor used by the geometric Bézout
certificates.  Its orientation agrees with `ambientPolynomialMinor`. -/
def ambientJacobianMinor {K : Type*} [CommRing K]
    (P : Coordinates4 K) (a b : Fin 4) : K :=
  coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
      coordinates4ToFun (canonicalCubicGradient25CharTwo P) b -
    coordinates4ToFun (canonicalQuadricGradient25CharTwo P) b *
      coordinates4ToFun (canonicalCubicGradient25CharTwo P) a

/-- The four images of the homogeneous coordinate variables under a ring
homomorphism, packaged as the coordinate vector used by the certificates. -/
def mappedAmbientPoint {K : Type*} [CommRing K] (φ : S →+* K) :
    Coordinates4 K :=
  ⟨φ (MvPolynomial.X 0), φ (MvPolynomial.X 1),
    φ (MvPolynomial.X 2), φ (MvPolynomial.X 3)⟩

/-- Reading a coordinate of the induced point is the same as mapping the
corresponding homogeneous variable. -/
@[simp]
theorem coordinates4ToFun_mappedAmbientPoint
    {K : Type*} [CommRing K] (φ : S →+* K) (a : Fin 4) :
    coordinates4ToFun (mappedAmbientPoint φ) a = φ (MvPolynomial.X a) := by
  fin_cases a <;> rfl

/-- Apply a ring homomorphism to all four entries of a coordinate vector. -/
def mapCoordinates4 {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) : Coordinates4 L :=
  ⟨φ P.x, φ P.y, φ P.z, φ P.w⟩

/-- The coordinate quadric formula is natural under ring homomorphisms. -/
@[simp]
theorem map_canonicalQuadric_coordinates
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalQuadric25CharTwo P) =
      canonicalQuadric25CharTwo (mapCoordinates4 φ P) := by
  simp [canonicalQuadric25CharTwo, mapCoordinates4]

/-- The coordinate cubic formula is natural under ring homomorphisms. -/
@[simp]
theorem map_canonicalCubic_coordinates
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalCubic25CharTwo P) =
      canonicalCubic25CharTwo (mapCoordinates4 φ P) := by
  simp [canonicalCubic25CharTwo, mapCoordinates4]

/-- Coordinate-form Jacobian minors are natural under ring homomorphisms. -/
theorem map_ambientJacobianMinor_coordinates
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) (a b : Fin 4) :
    φ (ambientJacobianMinor P a b) =
      ambientJacobianMinor (mapCoordinates4 φ P) a b := by
  fin_cases a <;> fin_cases b <;>
    simp [ambientJacobianMinor, mapCoordinates4, coordinates4ToFun,
      canonicalQuadricGradient25CharTwo,
      canonicalCubicGradient25CharTwo]

/-- Naturality of the named `xy` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_xy
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).xy =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).xy := by
  exact map_ambientJacobianMinor_coordinates φ P 0 1

/-- Naturality of the named `xz` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_xz
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).xz =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).xz := by
  exact map_ambientJacobianMinor_coordinates φ P 0 2

/-- Naturality of the named `xw` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_xw
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).xw =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).xw := by
  exact map_ambientJacobianMinor_coordinates φ P 0 3

/-- Naturality of the named `yz` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_yz
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).yz =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).yz := by
  exact map_ambientJacobianMinor_coordinates φ P 1 2

/-- Naturality of the named `yw` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_yw
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).yw =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).yw := by
  exact map_ambientJacobianMinor_coordinates φ P 1 3

/-- Naturality of the named `zw` Jacobian minor. -/
@[simp]
theorem map_canonicalJacobianMinors_zw
    {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (P : Coordinates4 K) :
    φ (canonicalJacobianMinors25CharTwo P).zw =
      (canonicalJacobianMinors25CharTwo (mapCoordinates4 φ P)).zw := by
  exact map_ambientJacobianMinor_coordinates φ P 2 3

/-- Evaluating a quadric partial derivative through a ring homomorphism gives
the corresponding coordinate of the geometric quadric gradient. -/
theorem map_pderiv_canonicalQuadric
    {K : Type*} [CommRing K] (φ : S →+* K) (a : Fin 4) :
    φ (MvPolynomial.pderiv a canonicalQuadricPolynomial25Two) =
      coordinates4ToFun
        (canonicalQuadricGradient25CharTwo (mappedAmbientPoint φ)) a := by
  have htwo : (2 : S) = 0 := CharP.cast_eq_zero S 2
  fin_cases a <;>
    simp [canonicalQuadricPolynomial25Two, mappedAmbientPoint,
      coordinates4ToFun, canonicalQuadricGradient25CharTwo, htwo]

/-- Evaluating a cubic partial derivative through a ring homomorphism gives
the corresponding coordinate of the geometric cubic gradient. -/
theorem map_pderiv_canonicalCubic
    {K : Type*} [CommRing K] (φ : S →+* K) (a : Fin 4) :
    φ (MvPolynomial.pderiv a canonicalCubicPolynomial25Two) =
      coordinates4ToFun
        (canonicalCubicGradient25CharTwo (mappedAmbientPoint φ)) a := by
  have htwo : (2 : S) = 0 := CharP.cast_eq_zero S 2
  fin_cases a <;>
    simp [canonicalCubicPolynomial25Two, mappedAmbientPoint,
      coordinates4ToFun, canonicalCubicGradient25CharTwo, htwo] <;> ring

/-- Ring maps carry the polynomial Jacobian minor to the coordinate minor at
the induced four-coordinate point. -/
theorem map_ambientPolynomialMinor
    {K : Type*} [CommRing K] (φ : S →+* K) (a b : Fin 4) :
    φ (ambientPolynomialMinor a b) =
      ambientJacobianMinor (mappedAmbientPoint φ) a b := by
  simp only [ambientPolynomialMinor, map_sub, map_mul,
    ambientJacobianMinor, map_pderiv_canonicalQuadric,
    map_pderiv_canonicalCubic]

/-- Evaluating the homogeneous quadric through a ring homomorphism recovers
the coordinate formula at the induced point. -/
theorem map_canonicalQuadric
    {K : Type*} [CommRing K] (φ : S →+* K) :
    φ canonicalQuadricPolynomial25Two =
      canonicalQuadric25CharTwo (mappedAmbientPoint φ) := by
  simp [canonicalQuadricPolynomial25Two, mappedAmbientPoint,
    canonicalQuadric25CharTwo]

/-- Evaluating the homogeneous cubic through a ring homomorphism recovers
the coordinate formula at the induced point. -/
theorem map_canonicalCubic
    {K : Type*} [CommRing K] (φ : S →+* K) :
    φ canonicalCubicPolynomial25Two =
      canonicalCubic25CharTwo (mappedAmbientPoint φ) := by
  simp [canonicalCubicPolynomial25Two, mappedAmbientPoint,
    canonicalCubic25CharTwo]

/-- Euler's identity expresses the weighted sum of minors against column
`a` using the two defining homogeneous equations. -/
theorem ambientPolynomialMinor_weighted_sum (a : Fin 4) :
    ∑ t : Fin 4, MvPolynomial.X t * ambientPolynomialMinor t a =
      (2 • canonicalQuadricPolynomial25Two) *
          MvPolynomial.pderiv a canonicalCubicPolynomial25Two -
        MvPolynomial.pderiv a canonicalQuadricPolynomial25Two *
          (3 • canonicalCubicPolynomial25Two) := by
  calc
    ∑ t : Fin 4, MvPolynomial.X t * ambientPolynomialMinor t a =
        (∑ t : Fin 4, MvPolynomial.X t *
            MvPolynomial.pderiv t canonicalQuadricPolynomial25Two) *
            MvPolynomial.pderiv a canonicalCubicPolynomial25Two -
          MvPolynomial.pderiv a canonicalQuadricPolynomial25Two *
            (∑ t : Fin 4, MvPolynomial.X t *
              MvPolynomial.pderiv t canonicalCubicPolynomial25Two) := by
      simp only [ambientPolynomialMinor, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = _ := by
      rw [canonicalQuadricPolynomial25Two_isHomogeneous.sum_X_mul_pderiv,
        canonicalCubicPolynomial25Two_isHomogeneous.sum_X_mul_pderiv]

/-- In the binary polynomial ring, the quadric Euler term vanishes and the
cubic degree reduces to one. -/
theorem ambientPolynomialMinor_weighted_sum_charTwo (a : Fin 4) :
    ∑ t : Fin 4, MvPolynomial.X t * ambientPolynomialMinor t a =
      MvPolynomial.pderiv a canonicalQuadricPolynomial25Two *
        canonicalCubicPolynomial25Two := by
  rw [ambientPolynomialMinor_weighted_sum]
  have htwo (f : S) : 2 • f = 0 := CharTwo.two_nsmul f
  have hthree (f : S) : 3 • f = f := by
    rw [show 3 = 2 + 1 by norm_num, add_nsmul, htwo, one_nsmul,
      zero_add]
  rw [htwo, hthree, zero_mul, zero_sub]
  exact @CharTwo.neg_eq S _ (inferInstance : CharP S 2) _

/-- Reversing the columns of a two-by-two Jacobian minor changes its sign. -/
theorem ambientPolynomialMinor_swap (a b : Fin 4) :
    ambientPolynomialMinor a b = -ambientPolynomialMinor b a := by
  simp only [ambientPolynomialMinor]
  ring

/-- In characteristic two the two orientations of a Jacobian minor agree. -/
theorem ambientPolynomialMinor_comm (a b : Fin 4) :
    ambientPolynomialMinor a b = ambientPolynomialMinor b a := by
  rw [ambientPolynomialMinor_swap]
  exact CharTwo.neg_eq _

/-- A Jacobian minor with two equal columns vanishes. -/
@[simp]
theorem ambientPolynomialMinor_self (a : Fin 4) :
    ambientPolynomialMinor a a = 0 := by
  simp [ambientPolynomialMinor]

end MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
