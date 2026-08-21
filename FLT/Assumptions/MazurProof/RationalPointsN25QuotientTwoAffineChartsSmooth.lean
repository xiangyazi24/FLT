import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCharts
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoStructuralJacobian
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF2
import FLT.Mathlib.RingTheory.RingHom.SmoothJacobian

/-!
# Smoothness of all four affine charts of the N25 binary quotient

This module develops one selected-Jacobian presentation for every
standard chart.  Coordinate labels are removed with `Fin.succAbove`; no
chart-specific permutation of an anonymous three-variable ring is chosen.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoStructuralJacobian
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ordinary complete-intersection coordinate ring on `D₊(X pivot)`. -/
abbrev ChartQuotient (pivot : Fin 4) :=
  AffineChart pivot ⧸ chartAffineEquationIdeal pivot

/-- Homogeneous polynomials are first dehomogenized at the chart pivot and
then reduced modulo the two affine equations. -/
def chartMap (pivot : Fin 4) : S →+* ChartQuotient pivot :=
  (algebraMap (AffineChart pivot) (ChartQuotient pivot)).comp
    (ambientDehomogenize pivot)

/-- The affine-to-homogeneous chart equivalence sends a dehomogenized
homogeneous polynomial to its canonical homogeneous fraction. -/
theorem chartCoordinateRingEquivAffine_chartMap
    (pivot : Fin 4) (n : ℕ) (p : S)
    (hp : p ∈ standardConePiece (n • (1 : ℕ))) :
    chartCoordinateRingEquivAffine pivot (chartMap pivot p) =
      Away.mk literalConePiece
        (canonicalConeGradedProjection.map_mem (coordinate_isHomogeneous pivot)) n
        (canonicalConeGradedProjection p)
        (canonicalConeGradedProjection.map_mem hp) := by
  change chartCoordinateRingEquivAffine pivot
      (Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
        (ambientDehomogenize pivot p)) = _
  rw [chartCoordinateRingEquivAffine_mk,
    standardChartEquiv_ambientDehomogenize]
  · rw [canonicalConeChartMap, Away.map_mk]
  · exact hp

/-- After omitting one of the three free coordinate positions, these are the
two ambient coordinate labels used as Jacobian columns. -/
def selectedChartVariable (pivot : Fin 4) (omitted : Fin 3) (r : Fin 2) :
    OtherCoordinate pivot :=
  affineCoordinate pivot (omitted.succAbove r)

/-- The two selected ambient labels are distinct. -/
theorem selectedChartVariable_injective (pivot : Fin 4) (omitted : Fin 3) :
    Function.Injective (selectedChartVariable pivot omitted) := by
  exact (finSuccAboveEquiv pivot).injective.comp
    omitted.succAbove_right_injective

/-- The naive two-equation presentation using the two affine variables not
occupying the omitted free-coordinate position. -/
noncomputable def chartPreSubmersive (pivot : Fin 4) (omitted : Fin 3) :
    Algebra.PreSubmersivePresentation k (ChartQuotient pivot)
      (OtherCoordinate pivot) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive
    (R := k) (v := chartAffineRelation pivot)
    (selectedChartVariable pivot omitted)
    (selectedChartVariable_injective pivot omitted)

/-- The selected Jacobian matrix is the matrix of the two displayed
relations differentiated in the two retained affine variables. -/
@[simp]
theorem chartPreSubmersive_jacobiMatrix
    (pivot : Fin 4) (omitted : Fin 3) (i j : Fin 2) :
    (chartPreSubmersive pivot omitted).jacobiMatrix i j =
      MvPolynomial.pderiv (selectedChartVariable pivot omitted i)
        (chartAffineRelation pivot j) := by
  exact Algebra.PreSubmersivePresentation.jacobiMatrix_naive
    (selectedChartVariable pivot omitted)
    (selectedChartVariable_injective pivot omitted) _ _ i j

/-- For every naive chart presentation, the presentation algebra map is the
ordinary quotient map by the two dehomogenized equations. -/
theorem chartPreSubmersive_algebraMap (pivot : Fin 4) (omitted : Fin 3) :
    algebraMap (chartPreSubmersive pivot omitted).Ring (ChartQuotient pivot) =
      Ideal.Quotient.mk (chartAffineEquationIdeal pivot) := by
  change algebraMap (chartPreSubmersive pivot omitted).Ring
      (AffineChart pivot ⧸ Ideal.span (Set.range (chartAffineRelation pivot))) =
    Ideal.Quotient.mk (Ideal.span (Set.range (chartAffineRelation pivot)))
  apply MvPolynomial.ringHom_ext
  · intro r
    rfl
  · intro i
    rfl

/-- The universal normalized point on a chart, before quotienting by its two
equations. -/
def chartUniversalPoint (pivot : Fin 4) : Coordinates4 (AffineChart pivot) :=
  mappedAmbientPoint (ambientDehomogenize pivot)

/-- The polynomial determinant selected by a chart presentation. -/
def chartSelectedMinor (pivot : Fin 4) (omitted : Fin 3) : AffineChart pivot :=
  MvPolynomial.pderiv (selectedChartVariable pivot omitted 0)
      (chartAffineRelation pivot 0) *
    MvPolynomial.pderiv (selectedChartVariable pivot omitted 1)
      (chartAffineRelation pivot 1) -
  MvPolynomial.pderiv (selectedChartVariable pivot omitted 0)
      (chartAffineRelation pivot 1) *
    MvPolynomial.pderiv (selectedChartVariable pivot omitted 1)
      (chartAffineRelation pivot 0)

/-- Differentiating after dehomogenization selects exactly the corresponding
homogeneous polynomial minor between the two retained ambient coordinates. -/
theorem chartSelectedMinor_eq_dehomogenize
    (pivot : Fin 4) (omitted : Fin 3) :
    chartSelectedMinor pivot omitted =
      ambientDehomogenize pivot
        (ambientPolynomialMinor
          (pivot.succAbove (omitted.succAbove 0))
          (pivot.succAbove (omitted.succAbove 1))) := by
  simp only [chartSelectedMinor, chartAffineRelation_zero,
    chartAffineRelation_one, chartAffineQuadric, chartAffineCubic,
    selectedChartVariable]
  rw [pderiv_ambientDehomogenize, pderiv_ambientDehomogenize,
    pderiv_ambientDehomogenize, pderiv_ambientDehomogenize]
  simp only [ambientPolynomialMinor, map_sub, map_mul]
  ring

/-- The presentation Jacobian is the quotient image of its selected
projective minor. -/
theorem chartPreSubmersive_jacobian
    (pivot : Fin 4) (omitted : Fin 3) :
    (chartPreSubmersive pivot omitted).jacobian =
      chartMap pivot
        (ambientPolynomialMinor
          (pivot.succAbove (omitted.succAbove 0))
          (pivot.succAbove (omitted.succAbove 1))) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  simp_rw [chartPreSubmersive_jacobiMatrix]
  rw [chartPreSubmersive_algebraMap]
  change Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
      (chartSelectedMinor pivot omitted) =
    Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
      (ambientDehomogenize pivot
        (ambientPolynomialMinor
          (pivot.succAbove (omitted.succAbove 0))
          (pivot.succAbove (omitted.succAbove 1))))
  rw [chartSelectedMinor_eq_dehomogenize]


/-! ## Polynomial Euler transport to the affine quotients -/

/-- The quotient class of either displayed affine relation is zero. -/
@[simp]
theorem chartQuotient_relation_zero (pivot : Fin 4) (r : Fin 2) :
    algebraMap (AffineChart pivot) (ChartQuotient pivot)
        (chartAffineRelation pivot r) = 0 := by
  change Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
      (chartAffineRelation pivot r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨r, rfl⟩

/-- The chart map kills the homogeneous quadric because its dehomogenization
is the first affine relation. -/
@[simp]
theorem chartMap_quadric_zero (pivot : Fin 4) :
    chartMap pivot canonicalQuadricPolynomial25Two = 0 := by
  simpa [chartMap, chartAffineQuadric] using
    chartQuotient_relation_zero pivot 0

/-- The chart map kills the homogeneous cubic because its dehomogenization
is the second affine relation. -/
@[simp]
theorem chartMap_cubic_zero (pivot : Fin 4) :
    chartMap pivot canonicalCubicPolynomial25Two = 0 := by
  simpa [chartMap, chartAffineCubic] using
    chartQuotient_relation_zero pivot 1

/-- The universal normalized point of a quotient chart is induced directly
by the homogeneous-to-affine chart map. -/
def chartQuotientPoint (pivot : Fin 4) : Coordinates4 (ChartQuotient pivot) :=
  mappedAmbientPoint (chartMap pivot)

/-- The distinguished homogeneous coordinate maps to one on its standard
affine chart. -/
@[simp]
theorem chartMap_X_pivot (pivot : Fin 4) :
    chartMap pivot (MvPolynomial.X pivot) = 1 := by
  change algebraMap (AffineChart pivot) (ChartQuotient pivot)
      (ambientDehomogenize pivot (MvPolynomial.X pivot)) = 1
  rw [ambientDehomogenize_X_self, map_one]

/-- The distinguished coordinate of the universal quotient point is one. -/
@[simp]
theorem chartQuotientPoint_pivot (pivot : Fin 4) :
    coordinates4ToFun (chartQuotientPoint pivot) pivot = 1 := by
  rw [show coordinates4ToFun (chartQuotientPoint pivot) pivot =
      chartMap pivot (MvPolynomial.X pivot) by
    exact coordinates4ToFun_mappedAmbientPoint (chartMap pivot) pivot]
  exact chartMap_X_pivot pivot

/-- The homogeneous quadric vanishes at the universal quotient point. -/
@[simp]
theorem chartQuotientPoint_quadric (pivot : Fin 4) :
    canonicalQuadric25CharTwo (chartQuotientPoint pivot) = 0 := by
  change canonicalQuadric25CharTwo (mappedAmbientPoint (chartMap pivot)) = 0
  rw [← map_canonicalQuadric (chartMap pivot)]
  exact chartMap_quadric_zero pivot

/-- The homogeneous cubic vanishes at the universal quotient point. -/
@[simp]
theorem chartQuotientPoint_cubic (pivot : Fin 4) :
    canonicalCubic25CharTwo (chartQuotientPoint pivot) = 0 := by
  change canonicalCubic25CharTwo (mappedAmbientPoint (chartMap pivot)) = 0
  rw [← map_canonicalCubic (chartMap pivot)]
  exact chartMap_cubic_zero pivot

/-- Mapping a homogeneous polynomial minor to a quotient chart agrees with
forming the coordinate minor at the induced quotient point. -/
theorem chartQuotientPoint_minor (pivot a b : Fin 4) :
    ambientJacobianMinor (chartQuotientPoint pivot) a b =
      chartMap pivot (ambientPolynomialMinor a b) := by
  simpa [chartQuotientPoint] using
    (map_ambientPolynomialMinor (chartMap pivot) a b).symm

/-- The ideal generated by the three selected presentation Jacobians on one
standard chart. -/
def chartJacobianIdeal (pivot : Fin 4) : Ideal (ChartQuotient pivot) :=
  Ideal.span (Set.range fun omitted ↦
    (chartPreSubmersive pivot omitted).jacobian)

/-- Each selected homogeneous minor maps into the ideal generated by the
three presentation Jacobians. -/
theorem selected_polynomial_minor_mem (pivot : Fin 4) (omitted : Fin 3) :
    chartMap pivot
        (ambientPolynomialMinor
          (pivot.succAbove (omitted.succAbove 0))
          (pivot.succAbove (omitted.succAbove 1))) ∈
      chartJacobianIdeal pivot := by
  rw [← chartPreSubmersive_jacobian]
  exact Ideal.subset_span ⟨omitted, rfl⟩

/-- Two distinct non-pivot coordinates are precisely the retained pair for
one omitted affine coordinate, up to orientation.  This finite lemma concerns
only coordinate labels and contains no polynomial expansion. -/
theorem free_pair_is_selected (pivot a b : Fin 4)
    (ha : a ≠ pivot) (hb : b ≠ pivot) (hab : a ≠ b) :
    ∃ omitted : Fin 3,
      (a = pivot.succAbove (omitted.succAbove 0) ∧
          b = pivot.succAbove (omitted.succAbove 1)) ∨
        (b = pivot.succAbove (omitted.succAbove 0) ∧
          a = pivot.succAbove (omitted.succAbove 1)) := by
  fin_cases pivot <;> fin_cases a <;> fin_cases b <;>
    first | omega | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ |
      exact ⟨2, by decide⟩

/-- Any mapped minor whose two columns avoid the chart pivot is one of the
three selected minors.  The finite split only identifies the three unordered
pairs of free coordinate labels. -/
theorem free_polynomial_minor_mem (pivot a b : Fin 4)
    (ha : a ≠ pivot) (hb : b ≠ pivot) :
    chartMap pivot (ambientPolynomialMinor a b) ∈
      chartJacobianIdeal pivot := by
  by_cases hab : a = b
  · subst b
    simp
  obtain ⟨omitted, h | h⟩ := free_pair_is_selected pivot a b ha hb hab
  · rcases h with ⟨rfl, rfl⟩
    exact selected_polynomial_minor_mem pivot omitted
  · rcases h with ⟨rfl, rfl⟩
    rw [ambientPolynomialMinor_comm]
    exact selected_polynomial_minor_mem pivot omitted

/-- On every quotient chart, Euler's characteristic-two identity makes the
coordinate-weighted sum of the four minors vanish.  Keeping the full sum
avoids choosing a complementary coordinate until a later geometric use. -/
theorem chartMap_weighted_minor_sum_zero (pivot a : Fin 4) :
    ∑ t : Fin 4,
        chartMap pivot (MvPolynomial.X t) *
          chartMap pivot (ambientPolynomialMinor t a) = 0 := by
  calc
    ∑ t : Fin 4,
        chartMap pivot (MvPolynomial.X t) *
          chartMap pivot (ambientPolynomialMinor t a) =
        chartMap pivot
          (∑ t : Fin 4,
            MvPolynomial.X t * ambientPolynomialMinor t a) := by
          simp
    _ = chartMap pivot
          (MvPolynomial.pderiv a canonicalQuadricPolynomial25Two *
            canonicalCubicPolynomial25Two) := by
          rw [ambientPolynomialMinor_weighted_sum_charTwo]
    _ = 0 := by simp

/-- Euler's identity removes a minor containing the normalized pivot.  The
argument is performed in the source polynomial ring and then mapped, so the
quotient need not synthesize a characteristic instance. -/
theorem pivot_polynomial_minor_mem (pivot a : Fin 4) :
    chartMap pivot (ambientPolynomialMinor pivot a) ∈
      chartJacobianIdeal pivot := by
  by_cases ha : a = pivot
  · subst a
    simp
  · have hsum := chartMap_weighted_minor_sum_zero pivot a
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pivot),
      chartMap_X_pivot, one_mul] at hsum
    have hfree :
        ∑ t ∈ Finset.univ.erase pivot,
            chartMap pivot (MvPolynomial.X t) *
              chartMap pivot (ambientPolynomialMinor t a) ∈
          chartJacobianIdeal pivot := by
      apply Ideal.sum_mem
      intro t ht
      exact (chartJacobianIdeal pivot).mul_mem_left _
        (free_polynomial_minor_mem pivot t a
          (Finset.mem_erase.mp ht).1 ha)
    have hpivot :
        chartMap pivot (ambientPolynomialMinor pivot a) =
          -(∑ t ∈ Finset.univ.erase pivot,
              chartMap pivot (MvPolynomial.X t) *
                chartMap pivot (ambientPolynomialMinor t a)) := by
      linear_combination hsum
    rw [hpivot]
    exact (chartJacobianIdeal pivot).neg_mem hfree

/-- Every mapped homogeneous Jacobian minor belongs to the selected affine
Jacobian ideal. -/
theorem all_polynomial_minors_mem (pivot a b : Fin 4) :
    chartMap pivot (ambientPolynomialMinor a b) ∈
      chartJacobianIdeal pivot := by
  by_cases ha : a = pivot
  · subst a
    exact pivot_polynomial_minor_mem pivot b
  by_cases hb : b = pivot
  · subst b
    rw [ambientPolynomialMinor_comm]
    exact pivot_polynomial_minor_mem pivot a
  exact free_polynomial_minor_mem pivot a b ha hb

/-- Every coordinate-form projective minor belongs to the selected affine
Jacobian ideal at the universal quotient point. -/
theorem all_ambient_minors_mem (pivot a b : Fin 4) :
    ambientJacobianMinor (chartQuotientPoint pivot) a b ∈
      chartJacobianIdeal pivot := by
  rw [chartQuotientPoint_minor]
  exact all_polynomial_minors_mem pivot a b

/-! ## The projective certificates generate the selected Jacobian ideal -/

/-- The indexed minor at columns `x,y` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_xy
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 0 1 =
      (canonicalJacobianMinors25CharTwo P).xy := by
  rfl

/-- The indexed minor at columns `x,z` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_xz
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 0 2 =
      (canonicalJacobianMinors25CharTwo P).xz := by
  rfl

/-- The indexed minor at columns `x,w` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_xw
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 0 3 =
      (canonicalJacobianMinors25CharTwo P).xw := by
  rfl

/-- The indexed minor at columns `y,z` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_yz
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 1 2 =
      (canonicalJacobianMinors25CharTwo P).yz := by
  rfl

/-- The indexed minor at columns `y,w` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_yw
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 1 3 =
      (canonicalJacobianMinors25CharTwo P).yw := by
  rfl

/-- The indexed minor at columns `z,w` is the named projective minor. -/
@[simp]
theorem ambientJacobianMinor_zw
    {K : Type*} [CommRing K] (P : Coordinates4 K) :
    ambientJacobianMinor P 2 3 =
      (canonicalJacobianMinors25CharTwo P).zw := by
  rfl

/-- The selected Jacobians generate the unit ideal on the chart `x=1`.
The existing projective certificate is used only after Euler transport has
put every projective minor in the selected affine ideal. -/
theorem chartJacobianIdeal_zero_eq_top :
    chartJacobianIdeal 0 = ⊤ := by
  let P := chartQuotientPoint 0
  let M := canonicalJacobianMinors25CharTwo P
  let J := chartJacobianIdeal 0
  have hP :
      mapCoordinates4 (chartMap 0)
          (⟨1, MvPolynomial.X 1, MvPolynomial.X 2,
            MvPolynomial.X 3⟩ : Coordinates4 S) = P := by
    simp [mapCoordinates4, P, chartQuotientPoint, mappedAmbientPoint,
      chartMap_X_pivot]
  have hcertSource := xChart_jacobian_certificate
    (K := S) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)
  have hcert := congrArg (chartMap 0) hcertSource
  simp only [map_add, map_mul, map_pow, map_one,
    map_canonicalQuadric_coordinates, map_canonicalCubic_coordinates,
    map_canonicalJacobianMinors_xz, map_canonicalJacobianMinors_xw,
    map_canonicalJacobianMinors_yz,
    map_canonicalJacobianMinors_yw, map_canonicalJacobianMinors_zw] at hcert
  rw [hP] at hcert
  change
    let b := P.y*P.w + P.y + P.z + P.w + 1
    let A := P.y*P.z*P.w + P.z^2 + P.z*P.w + P.w^2 + P.y + P.w
    let B := P.y*P.z*P.w + P.z^2 + P.y*P.w + P.z*P.w + P.w^2 +
      P.z + P.w
    let D := P.y*P.z^2*P.w + P.z^3 + P.y^2*P.w + P.z^2*P.w +
      P.y*P.w^2 + P.z*P.w^2 + P.y^2 + P.y*P.z + P.y*P.w +
      P.w^2 + P.y + P.z + P.w
    A * canonicalQuadric25CharTwo P +
      B * canonicalCubic25CharTwo P + b * M.xz + b * M.xw +
      D * M.yz + (P.y + 1) * M.yw + (P.y + 1) * M.zw = 1 at hcert
  rw [chartQuotientPoint_quadric, chartQuotientPoint_cubic] at hcert
  simp only [mul_zero, zero_add] at hcert
  have hxy : M.xy ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 0 1
  have hxz : M.xz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 0 2
  have hxw : M.xw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 0 3
  have hyz : M.yz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 1 2
  have hyw : M.yw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 1 3
  have hzw : M.zw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 0 2 3
  apply (Ideal.eq_top_iff_one J).mpr
  rw [← hcert]
  exact J.add_mem
    (J.add_mem
      (J.add_mem
        (J.add_mem (J.mul_mem_left _ hxz) (J.mul_mem_left _ hxw))
        (J.mul_mem_left _ hyz))
      (J.mul_mem_left _ hyw))
    (J.mul_mem_left _ hzw)

/-- The selected Jacobians generate the unit ideal on the chart `y=1`. -/
theorem chartJacobianIdeal_one_eq_top :
    chartJacobianIdeal 1 = ⊤ := by
  let P := chartQuotientPoint 1
  let M := canonicalJacobianMinors25CharTwo P
  let J := chartJacobianIdeal 1
  have hP :
      mapCoordinates4 (chartMap 1)
          (⟨MvPolynomial.X 0, 1, MvPolynomial.X 2,
            MvPolynomial.X 3⟩ : Coordinates4 S) = P := by
    simp [mapCoordinates4, P, chartQuotientPoint, mappedAmbientPoint,
      chartMap_X_pivot]
  have hcertSource := yChart_jacobian_certificate
    (K := S) (MvPolynomial.X 0) (MvPolynomial.X 2) (MvPolynomial.X 3)
  have hcert := congrArg (chartMap 1) hcertSource
  simp only [map_add, map_mul, map_pow, map_one,
    map_canonicalQuadric_coordinates, map_canonicalCubic_coordinates,
    map_canonicalJacobianMinors_xy, map_canonicalJacobianMinors_xz,
    map_canonicalJacobianMinors_yz,
    map_canonicalJacobianMinors_yw] at hcert
  rw [hP] at hcert
  change
    (P.x*P.z^2*P.w + P.z^3*P.w + P.x*P.z*P.w^2 + P.z^2*P.w^2 +
        P.z*P.w^3 + P.x*P.z^2 + P.z^3 + P.x*P.z*P.w + P.z^2*P.w +
        P.x*P.w + P.z + 1) * canonicalQuadric25CharTwo P +
      (P.x*P.z*P.w + P.z^2*P.w + P.z*P.w^2 + P.x*P.w) *
        canonicalCubic25CharTwo P +
      (P.x*P.z*P.w + P.z^2*P.w + P.z*P.w^2 + P.z^2 + P.x*P.w) * M.xy +
      (P.x^2*P.z + P.x*P.z^2 + P.x*P.z*P.w + P.z^2*P.w +
        P.x^2 + P.z^2 + P.x + P.z) * M.xz +
      (P.z*P.w^2 + P.z^2 + P.z + P.w + 1) * M.yz +
      (P.z*P.w) * M.yw = 1 at hcert
  rw [chartQuotientPoint_quadric, chartQuotientPoint_cubic] at hcert
  simp only [mul_zero, zero_add] at hcert
  have hxy : M.xy ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 1 0 1
  have hxz : M.xz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 1 0 2
  have hyz : M.yz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 1 1 2
  have hyw : M.yw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 1 1 3
  apply (Ideal.eq_top_iff_one J).mpr
  rw [← hcert]
  exact J.add_mem
    (J.add_mem
      (J.add_mem (J.mul_mem_left _ hxy) (J.mul_mem_left _ hxz))
      (J.mul_mem_left _ hyz))
    (J.mul_mem_left _ hyw)

/-- The selected Jacobians generate the unit ideal on the chart `z=1`. -/
theorem chartJacobianIdeal_two_eq_top :
    chartJacobianIdeal 2 = ⊤ := by
  let P := chartQuotientPoint 2
  let M := canonicalJacobianMinors25CharTwo P
  let J := chartJacobianIdeal 2
  have hP :
      mapCoordinates4 (chartMap 2)
          (⟨MvPolynomial.X 0, MvPolynomial.X 1, 1,
            MvPolynomial.X 3⟩ : Coordinates4 S) = P := by
    simp [mapCoordinates4, P, chartQuotientPoint, mappedAmbientPoint,
      chartMap_X_pivot]
  have hcertSource := zChart_jacobian_certificate
    (K := S) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 3)
  have hcert := congrArg (chartMap 2) hcertSource
  simp only [map_add, map_mul, map_pow, map_one,
    map_canonicalQuadric_coordinates,
    map_canonicalJacobianMinors_xy, map_canonicalJacobianMinors_xz,
    map_canonicalJacobianMinors_xw, map_canonicalJacobianMinors_yz,
    map_canonicalJacobianMinors_yw, map_canonicalJacobianMinors_zw] at hcert
  rw [hP] at hcert
  change
    (P.x^2 + P.x*P.y + P.x*P.w + P.y) *
        canonicalQuadric25CharTwo P +
      (P.x*P.w + P.w^2 + P.w + 1) * M.xy +
      (P.x^2 + P.x*P.w + P.x + P.w) * M.xz +
      (P.x^2*P.w + P.w^3 + P.x*P.y + P.y*P.w + P.w^2 + P.w) * M.xw +
      (P.x*P.w + P.w^2 + P.y + P.w + 1) * M.yz +
      (P.x^2*P.w + P.w^3 + P.x*P.y + P.x*P.w + P.y*P.w +
        P.y + P.w + 1) * M.yw +
      (P.x*P.w + P.w^2 + P.y + 1) * M.zw = 1 at hcert
  rw [chartQuotientPoint_quadric] at hcert
  simp only [mul_zero, zero_add] at hcert
  have hxy : M.xy ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 0 1
  have hxz : M.xz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 0 2
  have hxw : M.xw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 0 3
  have hyz : M.yz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 1 2
  have hyw : M.yw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 1 3
  have hzw : M.zw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 2 2 3
  apply (Ideal.eq_top_iff_one J).mpr
  rw [← hcert]
  exact J.add_mem
    (J.add_mem
      (J.add_mem
        (J.add_mem
          (J.add_mem (J.mul_mem_left _ hxy) (J.mul_mem_left _ hxz))
          (J.mul_mem_left _ hxw))
        (J.mul_mem_left _ hyz))
      (J.mul_mem_left _ hyw))
    (J.mul_mem_left _ hzw)

/-- The selected Jacobians generate the unit ideal on the chart `w=1`. -/
theorem chartJacobianIdeal_three_eq_top :
    chartJacobianIdeal 3 = ⊤ := by
  let P := chartQuotientPoint 3
  let M := canonicalJacobianMinors25CharTwo P
  let J := chartJacobianIdeal 3
  have hP :
      mapCoordinates4 (chartMap 3)
          (⟨MvPolynomial.X 0, MvPolynomial.X 1,
            MvPolynomial.X 2, 1⟩ : Coordinates4 S) = P := by
    simp [mapCoordinates4, P, chartQuotientPoint, mappedAmbientPoint,
      chartMap_X_pivot]
  have hcertSource := wChart_jacobian_certificate
    (K := S) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
  have hcert := congrArg (chartMap 3) hcertSource
  simp only [map_add, map_mul, map_pow, map_one,
    map_canonicalQuadric_coordinates, map_canonicalCubic_coordinates,
    map_canonicalJacobianMinors_xy, map_canonicalJacobianMinors_xz,
    map_canonicalJacobianMinors_yz,
    map_canonicalJacobianMinors_yw, map_canonicalJacobianMinors_zw] at hcert
  rw [hP] at hcert
  change
    (P.x*P.z^4 + P.z^4 + P.x*P.y*P.z + P.y^2*P.z + P.z^3 +
        P.x*P.y + P.y^2 + P.x*P.z + P.y*P.z) *
        canonicalQuadric25CharTwo P +
      (P.x*P.z^2 + P.x*P.z + P.y + P.z + 1) *
        canonicalCubic25CharTwo P +
      (P.x*P.z^3 + P.x*P.z^2 + P.z^3 + P.x*P.y + P.y^2 +
        P.z^2 + P.x + 1) * M.xy +
      (P.x*P.z^3 + P.x*P.z^2 + P.z^3 + P.x*P.y + P.y^2 +
        P.z^2 + P.x + P.z + 1) * M.xz +
      (P.x*P.z + P.x + P.z) * M.yz +
      (P.x*P.z^2 + P.x*P.z + P.z^2) * M.yw +
      (P.z^2 + 1) * M.zw = 1 at hcert
  rw [chartQuotientPoint_quadric, chartQuotientPoint_cubic] at hcert
  simp only [mul_zero, zero_add] at hcert
  have hxy : M.xy ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 3 0 1
  have hxz : M.xz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 3 0 2
  have hyz : M.yz ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 3 1 2
  have hyw : M.yw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 3 1 3
  have hzw : M.zw ∈ J := by
    simpa [M, P] using all_ambient_minors_mem 3 2 3
  apply (Ideal.eq_top_iff_one J).mpr
  rw [← hcert]
  exact J.add_mem
    (J.add_mem
      (J.add_mem
        (J.add_mem (J.mul_mem_left _ hxy) (J.mul_mem_left _ hxz))
        (J.mul_mem_left _ hyz))
      (J.mul_mem_left _ hyw))
    (J.mul_mem_left _ hzw)

/-- For every pivot, the three selected presentation Jacobians span the unit
ideal in the affine equation quotient. -/
theorem chartPreSubmersive_jacobian_span (pivot : Fin 4) :
    Ideal.span (Set.range fun omitted ↦
      (chartPreSubmersive pivot omitted).jacobian) = ⊤ := by
  change chartJacobianIdeal pivot = ⊤
  fin_cases pivot
  · exact chartJacobianIdeal_zero_eq_top
  · exact chartJacobianIdeal_one_eq_top
  · exact chartJacobianIdeal_two_eq_top
  · exact chartJacobianIdeal_three_eq_top

/-- Each selected chart presentation has three affine variables and two
relations, so its complete-intersection relative dimension is one. -/
theorem chartPreSubmersive_dimension (pivot : Fin 4) (omitted : Fin 3) :
    (chartPreSubmersive pivot omitted).dimension = 1 := by
  rw [Algebra.Presentation.dimension]
  rw [Nat.card_congr (finSuccAboveEquiv pivot).symm]
  norm_num

/-- Every ordinary chart quotient is locally standard smooth of relative
dimension one over the binary coefficient field. -/
theorem chartAffineQuotient_locallyStandardSmoothOfRelativeDimension
    (pivot : Fin 4) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (ChartQuotient pivot)) :=
  RingHom.Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
    (chartPreSubmersive pivot) (chartPreSubmersive_dimension pivot)
    (chartPreSubmersive_jacobian_span pivot)

/-- Every ordinary two-equation affine chart quotient is smooth over the
binary coefficient field. -/
theorem chartAffineQuotient_smooth (pivot : Fin 4) :
    RingHom.Smooth (algebraMap k (ChartQuotient pivot)) :=
  RingHom.Smooth.of_jacobian_span (chartPreSubmersive pivot)
    (chartPreSubmersive_jacobian_span pivot)

/-! ## Transport to the actual homogeneous projective charts -/

/-- The actual degree-zero coordinate ring of `D₊(X pivot)` in the
projective canonical curve. -/
abbrev ChartCoordinateRing (pivot : Fin 4) :=
  Away literalConePiece
    (canonicalConeGradedProjection (MvPolynomial.X pivot))

/-- Binary constants on the projective chart are transported through the
proved ordinary-affine coordinate equivalence. -/
noncomputable instance chartCoordinateRingAlgebra (pivot : Fin 4) :
    Algebra k (ChartCoordinateRing pivot) :=
  ((chartCoordinateRingEquivAffine pivot).toRingHom.comp
    (algebraMap k (ChartQuotient pivot))).toAlgebra

/-- Smoothness of the ordinary quotient presentation transports to every
actual degree-zero homogeneous coordinate ring. -/
theorem chartCoordinateRing_smooth (pivot : Fin 4) :
    RingHom.Smooth (algebraMap k (ChartCoordinateRing pivot)) := by
  have hEquiv :
      RingHom.Smooth (chartCoordinateRingEquivAffine pivot).toRingHom :=
    RingHom.Smooth.of_bijective
      (chartCoordinateRingEquivAffine pivot).bijective
  have hComp := (chartAffineQuotient_smooth pivot).comp hEquiv
  have hRingHom :
      (chartCoordinateRingEquivAffine pivot).toRingHom.comp
          (algebraMap k (ChartQuotient pivot)) =
        algebraMap k (ChartCoordinateRing pivot) :=
    RingHom.ext_zmod _ _
  rw [hRingHom] at hComp
  exact hComp

/-- Relative dimension one transports through the proved equivalence from
the ordinary affine quotient to the actual projective chart ring. -/
theorem chartCoordinateRing_locallyStandardSmoothOfRelativeDimension
    (pivot : Fin 4) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (ChartCoordinateRing pivot)) := by
  have hTransport :=
    (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left
      (algebraMap k (ChartQuotient pivot))
      (chartCoordinateRingEquivAffine pivot)
      (chartAffineQuotient_locallyStandardSmoothOfRelativeDimension pivot)
  have hRingHom :
      (chartCoordinateRingEquivAffine pivot).toRingHom.comp
          (algebraMap k (ChartQuotient pivot)) =
        algebraMap k (ChartCoordinateRing pivot) :=
    RingHom.ext_zmod _ _
  rw [hRingHom] at hTransport
  exact hTransport

end MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
