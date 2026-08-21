import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChart

/-!
# Uniform polynomial coordinates on the N25 standard projective charts

The affine variables on `D₊(X i)` are indexed canonically by the three
ambient coordinates different from `i`.  This avoids choosing four unrelated
permutations of `Fin 3` and makes all monomial-fraction arguments independent
of the selected chart.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoAffineCharts

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoChartIdeal
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine coordinates on `D₊(X i)` are the ambient coordinates other
than the distinguished coordinate `i`. -/
abbrev OtherCoordinate (i : Fin 4) := {j : Fin 4 // j ≠ i}

/-- The degree-zero homogeneous localization describing the ambient standard
projective chart. -/
abbrev StandardChart (i : Fin 4) :=
  Away standardConePiece (MvPolynomial.X i)

/-- The ordinary three-variable polynomial ring, with variables canonically
indexed by the coordinates different from `i`. -/
abbrev AffineChart (i : Fin 4) := MvPolynomial (OtherCoordinate i) k

/-- The temporary ratio `X_j/X_i`, including the diagonal case `j=i`.
Retaining that case makes multiplication of monomial fractions uniform. -/
def fullRatio (i j : Fin 4) : StandardChart i :=
  Away.mk standardConePiece (coordinate_isHomogeneous i) 1
    (MvPolynomial.X j) (by simpa using coordinate_isHomogeneous j)

/-- The actual affine coordinate ratio, whose numerator coordinate is known
to differ from the denominator coordinate. -/
def coordinateRatio (i : Fin 4) (j : OtherCoordinate i) : StandardChart i :=
  fullRatio i j.1

/-- The diagonal temporary ratio is one in the localization.  The proof uses
only the localization relation and therefore needs no domain hypothesis. -/
theorem fullRatio_self (i : Fin 4) : fullRatio i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [fullRatio, Away.val_mk, HomogeneousLocalization.val_one, pow_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp

/-- A homogeneous monomial divided by `X_i` to its total degree equals the
product of all four temporary coordinate ratios. -/
theorem awayMk_prod_eq_prod_fullRatio
    (i : Fin 4) (a : ℕ) (ai : Fin 4 → ℕ)
    (hai : ∑ j, ai j = a)
    (hhom : (∏ j, MvPolynomial.X j ^ ai j : S) ∈ standardConePiece a) :
    Away.mk standardConePiece (coordinate_isHomogeneous i) a
        (∏ j, MvPolynomial.X j ^ ai j) (by simpa using hhom) =
      ∏ j, fullRatio i j ^ ai j := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  rw [show
    (∏ j : Fin 4, fullRatio i j ^ ai j).val =
        ∏ j : Fin 4, (fullRatio i j).val ^ ai j by
      rw [← HomogeneousLocalization.algebraMap_apply]
      simp only [map_prod, map_pow,
        HomogeneousLocalization.algebraMap_apply]]
  simp only [fullRatio, Away.val_mk, Localization.mk_pow,
    Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_pow, pow_one, one_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [hai]

/-- Erasing the diagonal factor converts the four-coordinate product into
the canonical product over coordinates different from `i`. -/
theorem prod_fullRatio_eq_prod_coordinateRatio
    (i : Fin 4) (ai : Fin 4 → ℕ) :
    (∏ j : Fin 4, fullRatio i j ^ ai j) =
      ∏ j : OtherCoordinate i, coordinateRatio i j ^ ai j.1 := by
  classical
  let f : Fin 4 → StandardChart i := fun j ↦ fullRatio i j ^ ai j
  have herase := Finset.mul_prod_erase (Finset.univ : Finset (Fin 4)) f
    (Finset.mem_univ i)
  have hwithout :
      (∏ j ∈ (Finset.univ.erase i), f j) = ∏ j, f j := by
    simpa [f, fullRatio_self] using herase
  calc
    (∏ j : Fin 4, fullRatio i j ^ ai j) =
        ∏ j ∈ (Finset.univ.erase i), fullRatio i j ^ ai j := by
      simpa [f] using hwithout.symm
    _ = ∏ j : OtherCoordinate i, fullRatio i j.1 ^ ai j.1 := by
      apply Finset.prod_subtype
      intro j
      simp
    _ = ∏ j : OtherCoordinate i, coordinateRatio i j ^ ai j.1 := rfl

/-- Final uniform monomial-fraction identity on `D₊(X i)`. -/
theorem awayMk_prod_eq_prod_coordinateRatio
    (i : Fin 4) (a : ℕ) (ai : Fin 4 → ℕ)
    (hai : ∑ j, ai j = a)
    (hhom : (∏ j, MvPolynomial.X j ^ ai j : S) ∈ standardConePiece a) :
    Away.mk standardConePiece (coordinate_isHomogeneous i) a
        (∏ j, MvPolynomial.X j ^ ai j) (by simpa using hhom) =
      ∏ j : OtherCoordinate i, coordinateRatio i j ^ ai j.1 := by
  rw [awayMk_prod_eq_prod_fullRatio i a ai hai hhom,
    prod_fullRatio_eq_prod_coordinateRatio i ai]

/-! ## Uniform polynomial substitution and surjectivity -/

/-- Constants first enter the degree-zero homogeneous piece and then the
selected homogeneous localization. -/
def chartCoefficientMap (i : Fin 4) : k →+* StandardChart i :=
  (HomogeneousLocalization.fromZeroRingHom standardConePiece _).comp
    xChartDegreeZeroCoefficientMap

/-- Substitute the canonical coordinate ratios into an affine polynomial. -/
def affineToStandardChart (i : Fin 4) :
    AffineChart i →+* StandardChart i :=
  MvPolynomial.eval₂Hom (chartCoefficientMap i) (coordinateRatio i)

@[simp]
theorem affineToStandardChart_X (i : Fin 4) (j : OtherCoordinate i) :
    affineToStandardChart i (MvPolynomial.X j) = coordinateRatio i j := by
  simp [affineToStandardChart]

/-- Every degree-zero homogeneous fraction is a polynomial in the three
canonical ratios.  Generation reduces to the uniform monomial identity above,
not to a chart-by-chart variable enumeration. -/
theorem affineToStandardChart_surjective (i : Fin 4) :
    Function.Surjective (affineToStandardChart i) := by
  have hadjoin :=
    Away.adjoin_mk_prod_pow_eq_top
      (𝒜 := standardConePiece) (coordinate_isHomogeneous i)
      (Fin 4) (MvPolynomial.X : Fin 4 → S)
      standardConePiece_adjoin_coordinates (fun _ ↦ 1)
      (fun j ↦ coordinate_isHomogeneous j)
  intro z
  change z ∈ (affineToStandardChart i).range
  have hz : z ∈ (⊤ : Subalgebra (standardConePiece 0) (StandardChart i)) := by
    trivial
  rw [← hadjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      rcases hz with ⟨a, ai, hai, _hbound, rfl⟩
      have hai' : ∑ j, ai j = a := by simpa using hai
      have hhom :
          (∏ j : Fin 4, MvPolynomial.X j ^ ai j : S) ∈
            standardConePiece a := by
        have hhom' :
            (∏ j : Fin 4, MvPolynomial.X j ^ ai j : S) ∈
              standardConePiece (∑ j : Fin 4, ai j • (1 : ℕ)) :=
          SetLike.prod_pow_mem_graded standardConePiece (fun _ ↦ 1)
            (MvPolynomial.X : Fin 4 → S) ai
            (fun j _ ↦ coordinate_isHomogeneous j)
        simpa [hai'] using hhom'
      refine ⟨∏ j : OtherCoordinate i, MvPolynomial.X j ^ ai j.1, ?_⟩
      simp only [map_prod, map_pow, affineToStandardChart_X]
      exact (awayMk_prod_eq_prod_coordinateRatio i a ai hai' hhom).symm
  | algebraMap r =>
      have hrDegree : (r : S).totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).2 r.2
      have hrConstant : (r : S) = MvPolynomial.C ((r : S).coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hrDegree
      have hrSubtype :
          r = ⟨MvPolynomial.C ((r : S).coeff 0),
            MvPolynomial.isHomogeneous_C (Fin 4) ((r : S).coeff 0)⟩ :=
        Subtype.ext hrConstant
      refine ⟨MvPolynomial.C ((r : S).coeff 0), ?_⟩
      rw [hrSubtype]
      simp only [affineToStandardChart, MvPolynomial.eval₂Hom_C]
      simp only [MvPolynomial.coeff_C]
      rfl
  | add x y hx hy hxRange hyRange =>
      exact (affineToStandardChart i).range.add_mem hxRange hyRange
  | mul x y hx hy hxRange hyRange =>
      exact (affineToStandardChart i).range.mul_mem hxRange hyRange

/-! ## Uniform dehomogenization and the inverse map -/

/-- Dehomogenized value of an ambient coordinate: the distinguished
coordinate becomes one and every other coordinate becomes its canonical
affine variable. -/
def dehomogenizedVariable (i j : Fin 4) : AffineChart i :=
  if h : j ≠ i then MvPolynomial.X ⟨j, h⟩ else 1

/-- Set `X_i=1` in an ambient four-variable polynomial, retaining the other
three variables under their subtype indices. -/
def ambientDehomogenize (i : Fin 4) : S →+* AffineChart i :=
  MvPolynomial.eval₂Hom MvPolynomial.C (dehomogenizedVariable i)

@[simp]
theorem ambientDehomogenize_X_self (i : Fin 4) :
    ambientDehomogenize i (MvPolynomial.X i) = 1 := by
  simp [ambientDehomogenize, dehomogenizedVariable]

@[simp]
theorem ambientDehomogenize_X_other (i : Fin 4) (j : OtherCoordinate i) :
    ambientDehomogenize i (MvPolynomial.X j.1) = MvPolynomial.X j := by
  simp [ambientDehomogenize, dehomogenizedVariable, j.2]

/-- Extend dehomogenization to the ordinary localization at `X_i`; the
denominator maps to the unit one. -/
noncomputable def localizationToAffineChart (i : Fin 4) :
    Localization.Away (MvPolynomial.X i : S) →+* AffineChart i :=
  IsLocalization.Away.lift
    (S := Localization.Away (MvPolynomial.X i : S))
    (g := ambientDehomogenize i) (MvPolynomial.X i) (by simp)

/-- Restrict ordinary localization dehomogenization to its degree-zero
homogeneous subring. -/
noncomputable def standardChartToAffine (i : Fin 4) :
    StandardChart i →+* AffineChart i :=
  (localizationToAffineChart i).comp
    (algebraMap (StandardChart i)
      (Localization.Away (MvPolynomial.X i : S)))

/-- Dehomogenization sends `X_j/X_i` to the affine variable indexed by
`j ≠ i`. -/
@[simp]
theorem standardChartToAffine_coordinateRatio
    (i : Fin 4) (j : OtherCoordinate i) :
    standardChartToAffine i (coordinateRatio i j) = MvPolynomial.X j := by
  simp [standardChartToAffine, localizationToAffineChart,
    coordinateRatio, fullRatio,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [ambientDehomogenize, dehomogenizedVariable, j.2]

/-- Dehomogenization is a left inverse to polynomial substitution of the
three canonical coordinate ratios. -/
@[simp]
theorem standardChartToAffine_affineToStandard
    (i : Fin 4) (p : AffineChart i) :
    standardChartToAffine i (affineToStandardChart i p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [affineToStandardChart, MvPolynomial.eval₂Hom_C]
      simp [standardChartToAffine, localizationToAffineChart,
        chartCoefficientMap, xChartDegreeZeroCoefficientMap,
        HomogeneousLocalization.fromZeroRingHom,
        HomogeneousLocalization.algebraMap_apply,
        Localization.mk_eq_mk', IsLocalization.Away.lift]
      rw [IsLocalization.lift_mk'_spec]
      simp [ambientDehomogenize]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, affineToStandardChart_X,
        standardChartToAffine_coordinateRatio]

/-- Polynomial substitution into the coordinate ratios is injective. -/
theorem affineToStandardChart_injective (i : Fin 4) :
    Function.Injective (affineToStandardChart i) := by
  intro p q hpq
  calc
    p = standardChartToAffine i (affineToStandardChart i p) :=
      (standardChartToAffine_affineToStandard i p).symm
    _ = standardChartToAffine i (affineToStandardChart i q) :=
      congrArg (standardChartToAffine i) hpq
    _ = q := standardChartToAffine_affineToStandard i q

/-- Uniform ordinary polynomial coordinates on every ambient standard
projective chart. -/
noncomputable def standardChartEquiv (i : Fin 4) :
    AffineChart i ≃+* StandardChart i :=
  RingEquiv.ofBijective (affineToStandardChart i)
    ⟨affineToStandardChart_injective i,
      affineToStandardChart_surjective i⟩

@[simp]
theorem standardChartEquiv_apply (i : Fin 4) (p : AffineChart i) :
    standardChartEquiv i p = affineToStandardChart i p := rfl

/-- Dehomogenizing a homogeneous fraction amounts to setting `X_i=1` in
its numerator, because its denominator then becomes one. -/
@[simp]
theorem standardChartToAffine_mk (i : Fin 4) (n : ℕ) (p : S)
    (hp : p ∈ standardConePiece (n • (1 : ℕ))) :
    standardChartToAffine i
        (Away.mk standardConePiece (coordinate_isHomogeneous i) n p hp) =
      ambientDehomogenize i p := by
  simp [standardChartToAffine, localizationToAffineChart,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [ambientDehomogenize, dehomogenizedVariable]

/-- Surjectivity and the proved left inverse imply the inverse identity in
the other direction. -/
@[simp]
theorem affineToStandardChart_standardChartToAffine
    (i : Fin 4) (z : StandardChart i) :
    affineToStandardChart i (standardChartToAffine i z) = z := by
  obtain ⟨p, rfl⟩ := affineToStandardChart_surjective i z
  rw [standardChartToAffine_affineToStandard]

@[simp]
theorem standardChartEquiv_symm_apply (i : Fin 4) (z : StandardChart i) :
    (standardChartEquiv i).symm z = standardChartToAffine i z := by
  obtain ⟨p, rfl⟩ := affineToStandardChart_surjective i z
  calc
    (standardChartEquiv i).symm (affineToStandardChart i p) = p := by
      rw [← standardChartEquiv_apply]
      exact (standardChartEquiv i).symm_apply_apply p
    _ = standardChartToAffine i (affineToStandardChart i p) :=
      (standardChartToAffine_affineToStandard i p).symm

/-- Rehomogenizing the dehomogenization of a homogeneous polynomial recovers
its standard-chart fraction. -/
theorem standardChartEquiv_ambientDehomogenize
    (i : Fin 4) (n : ℕ) (p : S)
    (hp : p ∈ standardConePiece (n • (1 : ℕ))) :
    standardChartEquiv i (ambientDehomogenize i p) =
      Away.mk standardConePiece (coordinate_isHomogeneous i) n p hp := by
  rw [← standardChartToAffine_mk i n p hp]
  rw [← standardChartEquiv_symm_apply]
  exact (standardChartEquiv i).apply_symm_apply _

/-! ## Uniform affine equations and quotient chart rings -/

/-- The canonical quadric after setting the distinguished chart coordinate
to one. -/
def chartAffineQuadric (i : Fin 4) : AffineChart i :=
  ambientDehomogenize i canonicalQuadricPolynomial25Two

/-- The canonical cubic after setting the distinguished chart coordinate to
one. -/
def chartAffineCubic (i : Fin 4) : AffineChart i :=
  ambientDehomogenize i canonicalCubicPolynomial25Two

@[simp]
theorem standardChartToAffine_dehomogenizedQuadric (i : Fin 4) :
    standardChartToAffine i (dehomogenizedQuadric i) =
      chartAffineQuadric i := by
  rw [dehomogenizedQuadric, standardChartToAffine_mk]
  rfl

@[simp]
theorem standardChartToAffine_dehomogenizedCubic (i : Fin 4) :
    standardChartToAffine i (dehomogenizedCubic i) =
      chartAffineCubic i := by
  rw [dehomogenizedCubic, standardChartToAffine_mk]
  rfl

@[simp]
theorem standardChartEquiv_quadric (i : Fin 4) :
    standardChartEquiv i (chartAffineQuadric i) =
      dehomogenizedQuadric i := by
  rw [← standardChartToAffine_dehomogenizedQuadric,
    standardChartEquiv_apply,
    affineToStandardChart_standardChartToAffine]

@[simp]
theorem standardChartEquiv_cubic (i : Fin 4) :
    standardChartEquiv i (chartAffineCubic i) =
      dehomogenizedCubic i := by
  rw [← standardChartToAffine_dehomogenizedCubic,
    standardChartEquiv_apply,
    affineToStandardChart_standardChartToAffine]

/-- The two dehomogenized equations as a finite relation family, suitable
definitionally for Mathlib's naive presentation constructor. -/
def chartAffineRelation (i : Fin 4) : Fin 2 → AffineChart i :=
  Fin.cases (chartAffineQuadric i) (fun _ ↦ chartAffineCubic i)

@[simp]
theorem chartAffineRelation_zero (i : Fin 4) :
    chartAffineRelation i 0 = chartAffineQuadric i := rfl

@[simp]
theorem chartAffineRelation_one (i : Fin 4) :
    chartAffineRelation i 1 = chartAffineCubic i := rfl

/-- The range of the two-relation family is the expected pair of equations. -/
theorem chartAffineRelation_range (i : Fin 4) :
    Set.range (chartAffineRelation i) =
      ({chartAffineQuadric i, chartAffineCubic i} : Set (AffineChart i)) := by
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · intro hp
    rcases hp with hp | hp
    · exact ⟨0, hp.symm⟩
    · exact ⟨1, hp.symm⟩

/-- The affine complete-intersection ideal on the standard chart. -/
def chartAffineEquationIdeal (i : Fin 4) : Ideal (AffineChart i) :=
  Ideal.span (Set.range (chartAffineRelation i))

/-- The uniform coordinate equivalence carries the ordinary affine equation
ideal to the already proved homogeneous chart equation ideal. -/
theorem chartAffineEquationIdeal_map (i : Fin 4) :
    (chartAffineEquationIdeal i).map (standardChartEquiv i).toRingHom =
      chartEquationIdeal i := by
  have hq : affineToStandardChart i (chartAffineQuadric i) =
      dehomogenizedQuadric i := by
    simpa only [standardChartEquiv_apply] using standardChartEquiv_quadric i
  have hc : affineToStandardChart i (chartAffineCubic i) =
      dehomogenizedCubic i := by
    simpa only [standardChartEquiv_apply] using standardChartEquiv_cubic i
  rw [chartAffineEquationIdeal, chartAffineRelation_range,
    chartEquationIdeal, Ideal.map_span]
  congr 1
  ext z
  simp [hq, hc, eq_comm]

/-- Uniform ordinary quotient presentation of every actual standard chart of
the N25 projective canonical curve. -/
noncomputable def chartCoordinateRingEquivAffine (i : Fin 4) :
    (AffineChart i ⧸ chartAffineEquationIdeal i) ≃+*
      Away literalConePiece
        (canonicalConeGradedProjection (MvPolynomial.X i)) :=
  (Ideal.quotientEquiv (chartAffineEquationIdeal i) (chartEquationIdeal i)
      (standardChartEquiv i) (chartAffineEquationIdeal_map i).symm).trans
    (chartCoordinateRingEquiv i)

/-- The affine chart equivalence is induced by polynomial substitution into
the standard chart followed by the canonical quotient chart map. -/
@[simp]
theorem chartCoordinateRingEquivAffine_mk (i : Fin 4) (p : AffineChart i) :
    chartCoordinateRingEquivAffine i
        (Ideal.Quotient.mk (chartAffineEquationIdeal i) p) =
      canonicalConeChartMap i (standardChartEquiv i p) := by
  rw [chartCoordinateRingEquivAffine, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk, chartCoordinateRingEquiv_mk]

end MazurProof.RationalPointsN25QuotientTwoAffineCharts
