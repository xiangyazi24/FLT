import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF2
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Finite.Extension

/-!
# A function-field model for the binary N25 plane sextic

The canonical complete intersection on the affine chart `w = 1` projects to
a monic quartic in `x` over `F₂[z]`.  Specializing `z = 1` gives the
irreducible quartic `x⁴ + x + 1`, so the plane equation is irreducible and its
coordinate ring is a domain.  The final elimination identity connects this
integral plane model to the existing canonical quadric and cubic.
-/

open Polynomial

namespace MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField

noncomputable section

private abbrev k := ZMod 2
private abbrev zRing := k[X]

/-- The affine plane sextic on the chart `w = 1`, viewed as a monic
polynomial in `x` with coefficients in `F₂[z]`. -/
def planeSexticPolynomial : zRing[X] :=
  X ^ 4 + C (X ^ 3 + 1) * X ^ 3 + C (X ^ 2 + X) * X ^ 2 +
    C (X ^ 4) * X + C (X ^ 2)

theorem planeSexticPolynomial_monic : planeSexticPolynomial.Monic := by
  unfold planeSexticPolynomial
  monicity!

/-- The specialization at `z = 1` used to certify irreducibility. -/
def specializedQuartic : k[X] := X ^ 4 + X + 1

theorem planeSexticPolynomial_specialize_one :
    planeSexticPolynomial.map (Polynomial.evalRingHom 1) = specializedQuartic := by
  simp [planeSexticPolynomial, specializedQuartic]
  have htwo : (2 : k[X]) = 0 := CharP.cast_eq_zero k[X] 2
  linear_combination (X ^ 3 + X ^ 2) * htwo

theorem specializedQuartic_monic : specializedQuartic.Monic := by
  unfold specializedQuartic
  monicity!

theorem specializedQuartic_natDegree : specializedQuartic.natDegree = 4 := by
  unfold specializedQuartic
  compute_degree!

private theorem irreducible_dvd_own_frobenius
    {p : k[X]} (hp : Irreducible p) :
    p ∣ X ^ (2 ^ p.natDegree) - X := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : Module.Finite k (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  letI : Finite (AdjoinRoot p) := Module.finite_of_finite k
  letI : Fintype (AdjoinRoot p) := Fintype.ofFinite (AdjoinRoot p)
  have hcard : Fintype.card (AdjoinRoot p) = 2 ^ p.natDegree := by
    rw [Module.card_eq_pow_finrank (K := k) (V := AdjoinRoot p),
      (AdjoinRoot.powerBasis hp.ne_zero).finrank, ZMod.card,
      AdjoinRoot.powerBasis_dim]
  have hroot :
      (AdjoinRoot.root p) ^ (2 ^ p.natDegree) = AdjoinRoot.root p := by
    rw [← hcard]
    exact FiniteField.pow_card _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X]
  exact sub_eq_zero.mpr hroot

private theorem specializedQuartic_coprime_frobenius_two :
    IsCoprime specializedQuartic (X ^ 4 - X) := by
  refine ⟨1, 1, ?_⟩
  simp [specializedQuartic]
  have htwo : (2 : k[X]) = 0 := CharP.cast_eq_zero k[X] 2
  linear_combination X ^ 4 * htwo

theorem specializedQuartic_irreducible : Irreducible specializedQuartic := by
  have hf1 : specializedQuartic ≠ 1 := by
    intro h
    have hdegree := specializedQuartic_natDegree
    rw [h] at hdegree
    norm_num at hdegree
  rw [specializedQuartic_monic.irreducible_iff_lt_natDegree_lt hf1]
  intro q hq hdegree hqf
  rw [specializedQuartic_natDegree] at hdegree
  have hdegree' : 0 < q.natDegree ∧ q.natDegree ≤ 2 := by
    simpa using (Finset.mem_Ioc.mp hdegree)
  obtain ⟨r, _hrmonic, hrirreducible, hrq⟩ :=
    Polynomial.exists_monic_irreducible_factor q
      (not_isUnit_of_natDegree_pos q hdegree'.1)
  have hrf : r ∣ specializedQuartic := dvd_trans hrq hqf
  have hrle : r.natDegree ≤ 2 :=
    (natDegree_le_of_dvd hrq hq.ne_zero).trans hdegree'.2
  have hrpos : 0 < r.natDegree := hrirreducible.natDegree_pos
  have hcases : r.natDegree = 1 ∨ r.natDegree = 2 := by omega
  have hrfrob := irreducible_dvd_own_frobenius hrirreducible
  have hrfrobFour : r ∣ X ^ 4 - X := by
    rcases hcases with hdegreeOne | hdegreeTwo
    · rw [hdegreeOne] at hrfrob
      norm_num at hrfrob
      exact dvd_trans hrfrob (by
        use X ^ 2 + X + 1
        ring)
    · rw [hdegreeTwo] at hrfrob
      norm_num at hrfrob
      exact hrfrob
  exact hrirreducible.not_isUnit
    (specializedQuartic_coprime_frobenius_two.isUnit_of_dvd' hrf hrfrobFour)

theorem planeSexticPolynomial_irreducible :
    Irreducible planeSexticPolynomial := by
  apply planeSexticPolynomial_monic.irreducible_of_irreducible_map
    (Polynomial.evalRingHom 1) planeSexticPolynomial
  simpa [planeSexticPolynomial_specialize_one] using specializedQuartic_irreducible

/-- The integral affine plane coordinate ring of the binary N25 model. -/
abbrev PlaneCoordinateRing := AdjoinRoot planeSexticPolynomial

instance planeCoordinateRing_isDomain : IsDomain PlaneCoordinateRing :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      planeSexticPolynomial_irreducible)

/-- The `x` coordinate in the integral affine plane model. -/
def planeX : PlaneCoordinateRing :=
  AdjoinRoot.root planeSexticPolynomial

/-- The `z` coordinate in the integral affine plane model. -/
def planeZ : PlaneCoordinateRing :=
  AdjoinRoot.of planeSexticPolynomial Polynomial.X

/-- The fraction field of the integral affine plane model. -/
abbrev PlaneFunctionField := FractionRing PlaneCoordinateRing

/-- The chart `w = 1` as a four-coordinate point. -/
def wChartPoint {K : Type*} [CommRing K] (x y z : K) :
    RationalPointsN25QuotientF2.Coordinates4 K := ⟨x, y, z, 1⟩

def projectionDenominator {K : Type*} [CommRing K] (x z : K) : K :=
  x * z + x + z

def projectionNumerator {K : Type*} [CommRing K] (x z : K) : K :=
  x ^ 2 + x * z + z ^ 2 + z

def planeSexticValue {K : Type*} [CommRing K] (x z : K) : K :=
  x ^ 4 + x ^ 3 * z ^ 3 + x ^ 3 + x ^ 2 * z ^ 2 +
    x ^ 2 * z + x * z ^ 4 + z ^ 2

/-- Evaluating the nested polynomial first in `z` and then in `x` gives the
displayed affine sextic equation. -/
theorem planeSexticPolynomial_eval
    {K : Type*} [CommRing K] [Algebra k K] (x z : K) :
    planeSexticPolynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap k K) z) x =
      planeSexticValue x z := by
  simp only [planeSexticPolynomial, planeSexticValue, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C, eval₂_one, map_add, map_pow, map_one,
    coe_eval₂RingHom]
  ring

/-- Evaluating a coefficient polynomial at the plane-model `z` coordinate is
the canonical coefficient map into the `AdjoinRoot` coordinate ring. -/
theorem evalAtPlaneZ_eq_adjoinRootOf :
    Polynomial.eval₂RingHom (algebraMap k PlaneCoordinateRing) planeZ =
      AdjoinRoot.of planeSexticPolynomial := by
  apply Polynomial.ringHom_ext
  · intro a
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply k zRing PlaneCoordinateRing a)
  · simp [planeZ]

/-- The two universal affine coordinates satisfy the displayed plane
sextic equation in its integral coordinate ring. -/
theorem planeSexticValue_planeCoordinates :
    planeSexticValue planeX planeZ = 0 := by
  rw [← planeSexticPolynomial_eval]
  rw [evalAtPlaneZ_eq_adjoinRootOf]
  exact AdjoinRoot.eval₂_root planeSexticPolynomial

/-- The denominator of the inverse projection, as an element of the plane
coordinate ring. -/
def planeProjectionDenominator : PlaneCoordinateRing :=
  projectionDenominator planeX planeZ

/-- The numerator of the inverse projection, as an element of the plane
coordinate ring. -/
def planeProjectionNumerator : PlaneCoordinateRing :=
  projectionNumerator planeX planeZ

/-- Rewriting the plane sextic using the numerator and denominator of the
inverse projection.  This is the division-free identity used on the
principal open where the denominator is invertible. -/
theorem planeSextic_reconstruction_identity_of_two_eq_zero
    {K : Type*} [CommRing K] (x z : K) (htwo : (2 : K) = 0) :
    planeSexticValue x z =
      projectionDenominator x z ^ 3 + projectionNumerator x z ^ 2 +
        projectionNumerator x z * projectionDenominator x z * z := by
  simp [planeSexticValue, projectionDenominator, projectionNumerator]
  linear_combination
    -(2 * x ^ 3 * z ^ 2 + 3 * x ^ 3 * z + 2 * x ^ 2 * z ^ 3 +
      5 * x ^ 2 * z ^ 2 + 2 * x ^ 2 * z + 4 * x * z ^ 3 +
      3 * x * z ^ 2 + z ^ 4 + 2 * z ^ 3) * htwo

/-- The characteristic-two specialization of the reconstruction identity. -/
theorem planeSextic_reconstruction_identity
    {K : Type*} [CommRing K] [CharP K 2] (x z : K) :
    planeSexticValue x z =
      projectionDenominator x z ^ 3 + projectionNumerator x z ^ 2 +
        projectionNumerator x z * projectionDenominator x z * z :=
  planeSextic_reconstruction_identity_of_two_eq_zero x z
    (CharP.cast_eq_zero K 2)

/-- On `w = 1`, the canonical quadric is `D + y² + yz`. -/
theorem canonicalQuadric_wChart
    {K : Type*} [CommRing K] (x y z : K) :
    RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
        (wChartPoint x y z) =
      projectionDenominator x z + y ^ 2 + y * z := by
  simp [RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo,
    wChartPoint, projectionDenominator]
  ring

/-- On `w = 1`, the canonical cubic is exactly the numerator relation
`yD + N`. -/
theorem canonicalCubic_wChart
    {K : Type*} [CommRing K] (x y z : K) :
    RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
        (wChartPoint x y z) =
      y * projectionDenominator x z + projectionNumerator x z := by
  simp [RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo,
    wChartPoint, projectionDenominator, projectionNumerator]
  ring

/-- Division-free syzygy proving that the inverse-projection candidate
satisfies the quadric after its cubic relation and the plane equation are
known. -/
theorem denominator_sq_mul_canonicalQuadric_of_two_eq_zero
    {K : Type*} [CommRing K] (x y z : K) (htwo : (2 : K) = 0) :
    projectionDenominator x z ^ 2 *
        RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
          (wChartPoint x y z) =
      planeSexticValue x z +
        RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
            (wChartPoint x y z) *
          (RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
              (wChartPoint x y z) +
            z * projectionDenominator x z) := by
  rw [canonicalQuadric_wChart, canonicalCubic_wChart,
    planeSextic_reconstruction_identity_of_two_eq_zero x z htwo]
  linear_combination
    -(projectionNumerator x z *
      (projectionDenominator x z * y +
        projectionDenominator x z * z + projectionNumerator x z)) * htwo

/-- The characteristic-two specialization of the division-free chart
syzygy. -/
theorem denominator_sq_mul_canonicalQuadric
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    projectionDenominator x z ^ 2 *
        RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
          (wChartPoint x y z) =
      planeSexticValue x z +
        RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
            (wChartPoint x y z) *
          (RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
              (wChartPoint x y z) +
            z * projectionDenominator x z) :=
  denominator_sq_mul_canonicalQuadric_of_two_eq_zero x y z
    (CharP.cast_eq_zero K 2)

/-- The exact characteristic-two elimination identity connecting the
canonical complete intersection on `w = 1` to the plane sextic. -/
theorem planeSextic_elimination_identity
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    planeSexticValue x z =
      projectionDenominator x z ^ 2 *
          RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
            (wChartPoint x y z) +
        (projectionNumerator x z + projectionDenominator x z * y +
            z * projectionDenominator x z) *
          RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
            (wChartPoint x y z) := by
  simp [planeSexticValue, projectionDenominator, projectionNumerator,
    wChartPoint,
    RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo,
    RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination
    -(x ^ 3 * y * z + x ^ 3 * y + 2 * x ^ 3 * z ^ 2 + 3 * x ^ 3 * z +
      x ^ 2 * y ^ 2 * z ^ 2 + 2 * x ^ 2 * y ^ 2 * z + x ^ 2 * y ^ 2 +
      x ^ 2 * y * z ^ 3 + 3 * x ^ 2 * y * z ^ 2 + 3 * x ^ 2 * y * z +
      2 * x ^ 2 * z ^ 3 + 5 * x ^ 2 * z ^ 2 + 2 * x ^ 2 * z +
      2 * x * y ^ 2 * z ^ 2 + 2 * x * y ^ 2 * z + 3 * x * y * z ^ 3 +
      5 * x * y * z ^ 2 + x * y * z + 4 * x * z ^ 3 + 3 * x * z ^ 2 +
      y ^ 2 * z ^ 2 + 2 * y * z ^ 3 + y * z ^ 2 + z ^ 4 + 2 * z ^ 3) * htwo

/-- Every point of the canonical complete intersection on `w = 1` projects
to the integral affine plane sextic. -/
theorem planeSexticPolynomial_eval_eq_zero_of_canonical
    {K : Type*} [CommRing K] [CharP K 2] [Algebra k K] (x y z : K)
    (hquadric :
      RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo
        (wChartPoint x y z) = 0)
    (hcubic :
      RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo
        (wChartPoint x y z) = 0) :
    planeSexticPolynomial.eval₂
        (Polynomial.eval₂RingHom (algebraMap k K) z) x = 0 := by
  rw [planeSexticPolynomial_eval, planeSextic_elimination_identity,
    hquadric, hcubic]
  ring

end

end MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField
