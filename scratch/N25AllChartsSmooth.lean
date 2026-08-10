import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCharts
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmoothF2
import FLT.Mathlib.RingTheory.RingHom.SmoothJacobian

/-!
# Smoothness of all four affine charts of the N25 binary quotient

This module develops one selected-Jacobian presentation for every
standard chart.  Coordinate labels are removed with `Fin.succAbove`; no
chart-specific permutation of an anonymous three-variable ring is chosen.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoAffineCharts

/-- The ordinary complete-intersection coordinate ring on `D₊(X pivot)`. -/
abbrev ChartQuotient (pivot : Fin 4) :=
  AffineChart pivot ⧸ chartAffineEquationIdeal pivot

/-- After omitting one of the three free coordinate positions, these are the
two ambient coordinate labels used as Jacobian columns. -/
def selectedChartVariable (pivot : Fin 4) (omitted : Fin 3) (r : Fin 2) :
    OtherCoordinate pivot :=
  finSuccAboveEquiv pivot (omitted.succAbove r)

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
  ⟨dehomogenizedVariable pivot 0, dehomogenizedVariable pivot 1,
    dehomogenizedVariable pivot 2, dehomogenizedVariable pivot 3⟩

/-- A coordinate-indexed version of the projective two-by-two Jacobian
minor.  This is preferable to six separate fields during Euler transport. -/
def ambientJacobianMinor {K : Type*} [CommRing K]
    (P : Coordinates4 K) (a b : Fin 4) : K :=
  coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
      coordinates4ToFun (canonicalCubicGradient25CharTwo P) b -
    coordinates4ToFun (canonicalQuadricGradient25CharTwo P) b *
      coordinates4ToFun (canonicalCubicGradient25CharTwo P) a

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
projective gradient minor between the two retained ambient coordinates. -/
theorem chartSelectedMinor_eq_ambient
    (pivot : Fin 4) (omitted : Fin 3) :
    chartSelectedMinor pivot omitted =
      ambientJacobianMinor (chartUniversalPoint pivot)
        (selectedChartVariable pivot omitted 0).1
        (selectedChartVariable pivot omitted 1).1 := by
  fin_cases pivot <;> fin_cases omitted <;>
    simp [chartSelectedMinor, selectedChartVariable, chartAffineRelation,
      chartAffineQuadric, chartAffineCubic, ambientDehomogenize,
      dehomogenizedVariable, chartUniversalPoint, ambientJacobianMinor,
      canonicalQuadricPolynomial25Two, canonicalCubicPolynomial25Two,
      coordinates4ToFun, canonicalQuadricGradient25CharTwo,
      canonicalCubicGradient25CharTwo] <;>
    ring_nf

/-- The presentation Jacobian is the quotient image of its selected
projective minor. -/
theorem chartPreSubmersive_jacobian
    (pivot : Fin 4) (omitted : Fin 3) :
    (chartPreSubmersive pivot omitted).jacobian =
      algebraMap (AffineChart pivot) (ChartQuotient pivot)
        (ambientJacobianMinor (chartUniversalPoint pivot)
          (selectedChartVariable pivot omitted 0).1
          (selectedChartVariable pivot omitted 1).1) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  simp_rw [chartPreSubmersive_jacobiMatrix]
  rw [chartPreSubmersive_algebraMap]
  rw [← chartSelectedMinor_eq_ambient]
  rfl

/-! ## Euler transport of the projective minors -/

/-- Euler's identity for the homogeneous quadric in characteristic two.  Its
degree is zero in the coefficient ring, so the weighted gradient sum
vanishes identically. -/
theorem canonicalQuadric_euler
    {K : Type*} [CommRing K] [CharP K 2] (P : Coordinates4 K) :
    ∑ i : Fin 4, coordinates4ToFun P i *
      coordinates4ToFun (canonicalQuadricGradient25CharTwo P) i = 0 := by
  simp [Fin.sum_univ_succ, coordinates4ToFun,
    canonicalQuadricGradient25CharTwo]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- Euler's identity for the homogeneous cubic in characteristic two.  Its
degree three reduces to one, hence the weighted gradient sum is the cubic
itself. -/
theorem canonicalCubic_euler
    {K : Type*} [CommRing K] [CharP K 2] (P : Coordinates4 K) :
    ∑ i : Fin 4, coordinates4ToFun P i *
      coordinates4ToFun (canonicalCubicGradient25CharTwo P) i =
        canonicalCubic25CharTwo P := by
  simp [Fin.sum_univ_succ, coordinates4ToFun,
    canonicalCubicGradient25CharTwo, canonicalCubic25CharTwo]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

/-- The weighted sum of the four minors against one fixed column is the
quadric gradient in that column times the cubic.  This is the determinant
combination of the two Euler identities. -/
theorem ambientJacobianMinor_weighted_sum
    {K : Type*} [CommRing K] [CharP K 2]
    (P : Coordinates4 K) (a : Fin 4) :
    ∑ t : Fin 4, coordinates4ToFun P t * ambientJacobianMinor P t a =
      coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
        canonicalCubic25CharTwo P := by
  let X := coordinates4ToFun P
  let Q := coordinates4ToFun (canonicalQuadricGradient25CharTwo P)
  let C := coordinates4ToFun (canonicalCubicGradient25CharTwo P)
  calc
    ∑ t : Fin 4, X t * ambientJacobianMinor P t a =
        (∑ t : Fin 4, X t * Q t) * C a -
          Q a * (∑ t : Fin 4, X t * C t) := by
      simp only [ambientJacobianMinor, X, Q, C]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro t _
        ring
      · rw [← Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ = Q a * canonicalCubic25CharTwo P := by
      rw [canonicalQuadric_euler, canonicalCubic_euler]
      simp [CharTwo.neg_eq]

/-- On a normalized chart, a minor containing the pivot is a combination of
the three minors among the remaining coordinates, modulo the cubic.  This is
the structural step that avoids recomputing four affine Groebner
certificates. -/
theorem pivot_minor_reduction
    {K : Type*} [CommRing K] [CharP K 2]
    (P : Coordinates4 K) (pivot a : Fin 4)
    (hpivot : coordinates4ToFun P pivot = 1) :
    ambientJacobianMinor P pivot a =
      coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
          canonicalCubic25CharTwo P +
        ∑ t ∈ Finset.univ.erase pivot,
          coordinates4ToFun P t * ambientJacobianMinor P t a := by
  have hsum := ambientJacobianMinor_weighted_sum P a
  have hsplit :
      (∑ t ∈ Finset.univ.erase pivot,
          coordinates4ToFun P t * ambientJacobianMinor P t a) +
        coordinates4ToFun P pivot * ambientJacobianMinor P pivot a =
      coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
        canonicalCubic25CharTwo P := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
    exact hsum
  rw [hpivot, one_mul] at hsplit
  calc
    ambientJacobianMinor P pivot a =
        ((∑ t ∈ Finset.univ.erase pivot,
            coordinates4ToFun P t * ambientJacobianMinor P t a) +
          ambientJacobianMinor P pivot a) -
            (∑ t ∈ Finset.univ.erase pivot,
              coordinates4ToFun P t * ambientJacobianMinor P t a) := by ring
    _ = coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
          canonicalCubic25CharTwo P -
            (∑ t ∈ Finset.univ.erase pivot,
              coordinates4ToFun P t * ambientJacobianMinor P t a) := by
        rw [hsplit]
    _ = coordinates4ToFun (canonicalQuadricGradient25CharTwo P) a *
          canonicalCubic25CharTwo P +
            ∑ t ∈ Finset.univ.erase pivot,
              coordinates4ToFun P t * ambientJacobianMinor P t a := by
        rw [CharTwo.sub_eq_add]

/-! ## Passing the Euler identities to the affine quotients -/

/-- The universal normalized point evaluates the projective quadric to the
uniformly dehomogenized affine quadric. -/
theorem chartUniversalPoint_quadric (pivot : Fin 4) :
    canonicalQuadric25CharTwo (chartUniversalPoint pivot) =
      chartAffineQuadric pivot := by
  fin_cases pivot <;>
    simp [chartUniversalPoint, chartAffineQuadric, ambientDehomogenize,
      dehomogenizedVariable, canonicalQuadricPolynomial25Two,
      canonicalQuadric25CharTwo]

/-- The analogous evaluation identity for the projective cubic. -/
theorem chartUniversalPoint_cubic (pivot : Fin 4) :
    canonicalCubic25CharTwo (chartUniversalPoint pivot) =
      chartAffineCubic pivot := by
  fin_cases pivot <;>
    simp [chartUniversalPoint, chartAffineCubic, ambientDehomogenize,
      dehomogenizedVariable, canonicalCubicPolynomial25Two,
      canonicalCubic25CharTwo]

/-- The quotient class of either displayed affine relation is zero. -/
@[simp]
theorem chartQuotient_relation_zero (pivot : Fin 4) (r : Fin 2) :
    algebraMap (AffineChart pivot) (ChartQuotient pivot)
        (chartAffineRelation pivot r) = 0 := by
  change Ideal.Quotient.mk (chartAffineEquationIdeal pivot)
      (chartAffineRelation pivot r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨r, rfl⟩

/-- The universal normalized point after passing to the affine equation
quotient. -/
def chartQuotientPoint (pivot : Fin 4) : Coordinates4 (ChartQuotient pivot) :=
  let π := algebraMap (AffineChart pivot) (ChartQuotient pivot)
  ⟨π (dehomogenizedVariable pivot 0),
    π (dehomogenizedVariable pivot 1),
    π (dehomogenizedVariable pivot 2),
    π (dehomogenizedVariable pivot 3)⟩

/-- The distinguished coordinate of the universal quotient point is one. -/
@[simp]
theorem chartQuotientPoint_pivot (pivot : Fin 4) :
    coordinates4ToFun (chartQuotientPoint pivot) pivot = 1 := by
  fin_cases pivot <;>
    simp [chartQuotientPoint, coordinates4ToFun, dehomogenizedVariable]

/-- The first equation vanishes at the universal quotient point. -/
@[simp]
theorem chartQuotientPoint_quadric (pivot : Fin 4) :
    canonicalQuadric25CharTwo (chartQuotientPoint pivot) = 0 := by
  rw [← chartQuotient_relation_zero pivot 0]
  rw [chartAffineRelation_zero]
  rw [← chartUniversalPoint_quadric]
  fin_cases pivot <;>
    simp [chartQuotientPoint, chartUniversalPoint,
      canonicalQuadric25CharTwo, dehomogenizedVariable]

/-- The second equation vanishes at the universal quotient point. -/
@[simp]
theorem chartQuotientPoint_cubic (pivot : Fin 4) :
    canonicalCubic25CharTwo (chartQuotientPoint pivot) = 0 := by
  rw [← chartQuotient_relation_zero pivot 1]
  rw [chartAffineRelation_one]
  rw [← chartUniversalPoint_cubic]
  fin_cases pivot <;>
    simp [chartQuotientPoint, chartUniversalPoint,
      canonicalCubic25CharTwo, dehomogenizedVariable]

/-- Evaluating a universal affine minor in the quotient agrees with forming
the same projective minor at the quotient point. -/
theorem chartQuotientPoint_minor (pivot a b : Fin 4) :
    ambientJacobianMinor (chartQuotientPoint pivot) a b =
      algebraMap (AffineChart pivot) (ChartQuotient pivot)
        (ambientJacobianMinor (chartUniversalPoint pivot) a b) := by
  fin_cases a <;> fin_cases b <;>
    simp [ambientJacobianMinor, chartQuotientPoint, chartUniversalPoint,
      coordinates4ToFun, canonicalQuadricGradient25CharTwo,
      canonicalCubicGradient25CharTwo]

/-- In characteristic two the oriented two-by-two minor is symmetric in its
two column labels. -/
theorem ambientJacobianMinor_comm
    {K : Type*} [CommRing K] [CharP K 2]
    (P : Coordinates4 K) (a b : Fin 4) :
    ambientJacobianMinor P a b = ambientJacobianMinor P b a := by
  simp only [ambientJacobianMinor, CharTwo.sub_eq_add]
  ac_rfl

/-- The ideal generated by the three selected presentation Jacobians on one
standard chart. -/
def chartJacobianIdeal (pivot : Fin 4) : Ideal (ChartQuotient pivot) :=
  Ideal.span (Set.range fun omitted ↦
    (chartPreSubmersive pivot omitted).jacobian)

/-- Each of the three retained projective minors belongs to the selected
Jacobian ideal. -/
theorem selected_ambient_minor_mem (pivot : Fin 4) (omitted : Fin 3) :
    ambientJacobianMinor (chartQuotientPoint pivot)
        (selectedChartVariable pivot omitted 0).1
        (selectedChartVariable pivot omitted 1).1 ∈
      chartJacobianIdeal pivot := by
  rw [chartQuotientPoint_minor, ← chartPreSubmersive_jacobian]
  exact Ideal.subset_span ⟨omitted, rfl⟩

/-- Any minor whose two columns avoid the chart pivot belongs to the selected
Jacobian ideal.  The finite case split concerns only the six unordered pairs
of four coordinate labels; it does not enumerate field elements or points. -/
theorem free_ambient_minor_mem (pivot a b : Fin 4)
    (ha : a ≠ pivot) (hb : b ≠ pivot) :
    ambientJacobianMinor (chartQuotientPoint pivot) a b ∈
      chartJacobianIdeal pivot := by
  have h0 := selected_ambient_minor_mem pivot 0
  have h1 := selected_ambient_minor_mem pivot 1
  have h2 := selected_ambient_minor_mem pivot 2
  fin_cases pivot <;> fin_cases a <;> fin_cases b
  all_goals
    simp_all [selectedChartVariable, ambientJacobianMinor,
      CharTwo.sub_eq_add, add_comm]

/-- A minor containing the normalized pivot also belongs to the selected
Jacobian ideal.  Euler transport rewrites it as a sum of free-coordinate
minors because the cubic vanishes in the chart quotient. -/
theorem pivot_ambient_minor_mem (pivot a : Fin 4) :
    ambientJacobianMinor (chartQuotientPoint pivot) pivot a ∈
      chartJacobianIdeal pivot := by
  by_cases ha : a = pivot
  · subst a
    simp [ambientJacobianMinor]
  · rw [pivot_minor_reduction (chartQuotientPoint pivot) pivot a
      (chartQuotientPoint_pivot pivot)]
    rw [chartQuotientPoint_cubic, mul_zero, zero_add]
    apply Ideal.sum_mem
    intro t ht
    have htne : t ≠ pivot := (Finset.mem_erase.mp ht).1
    exact (chartJacobianIdeal pivot).mul_mem_left _
      (free_ambient_minor_mem pivot t a htne ha)

/-- Every projective Jacobian minor belongs to the selected Jacobian ideal on
the normalized chart: either both columns are free, or Euler transport
removes the pivot column. -/
theorem all_ambient_minors_mem (pivot a b : Fin 4) :
    ambientJacobianMinor (chartQuotientPoint pivot) a b ∈
      chartJacobianIdeal pivot := by
  by_cases ha : a = pivot
  · subst a
    exact pivot_ambient_minor_mem pivot b
  by_cases hb : b = pivot
  · subst b
    rw [ambientJacobianMinor_comm]
    exact pivot_ambient_minor_mem pivot a
  exact free_ambient_minor_mem pivot a b ha hb

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
      (⟨1, P.y, P.z, P.w⟩ : Coordinates4 (ChartQuotient 0)) = P := by
    ext <;> rfl
  have hcert := xChart_jacobian_certificate P.y P.z P.w
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
      (⟨P.x, 1, P.z, P.w⟩ : Coordinates4 (ChartQuotient 1)) = P := by
    ext <;> rfl
  have hcert := yChart_jacobian_certificate P.x P.z P.w
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
      (⟨P.x, P.y, 1, P.w⟩ : Coordinates4 (ChartQuotient 2)) = P := by
    ext <;> rfl
  have hcert := zChart_jacobian_certificate P.x P.y P.w
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
      (⟨P.x, P.y, P.z, 1⟩ : Coordinates4 (ChartQuotient 3)) = P := by
    ext <;> rfl
  have hcert := wChart_jacobian_certificate P.x P.y P.z
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

end MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
