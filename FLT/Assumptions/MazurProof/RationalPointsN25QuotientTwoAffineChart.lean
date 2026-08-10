import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoChartIdeal

/-!
# Affine coordinates on the first N25 projective chart

This file identifies the degree-zero homogeneous localization of
`k[X₀,X₁,X₂,X₃]` at `X₀` with the ordinary polynomial ring
`k[X₁/X₀,X₂/X₀,X₃/X₀]`.

The proof is structural.  Dehomogenization supplies one inverse.  For
surjectivity, the homogeneous-localization generation theorem reduces to a
single monomial identity: a degree-`a` coordinate monomial divided by
`X₀^a` is the product of the three coordinate ratios.  No enumeration of
field elements or polynomial coefficients is used.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoChartIdeal

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ordinary three-variable affine polynomial ring on the chart `x=1`. -/
abbrev xChartAffineRing := MvPolynomial (Fin 3) k

/-- The affine variable indexed by `j` represents `X_(j+1)/X_0`. -/
def xChartRatio (j : Fin 3) : Away standardConePiece (MvPolynomial.X 0) :=
  Away.mk standardConePiece (coordinate_isHomogeneous 0) 1
    (MvPolynomial.X j.succ) (by
      simpa using MvPolynomial.isHomogeneous_X k j.succ)

/-- Embed coefficients as constant homogeneous polynomials of degree zero. -/
def xChartDegreeZeroCoefficientMap : k →+* standardConePiece 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin 4) r⟩
  map_one' := Subtype.ext (map_one (MvPolynomial.C : k →+* S))
  map_mul' r s := Subtype.ext (map_mul (MvPolynomial.C : k →+* S) r s)
  map_zero' := Subtype.ext (map_zero (MvPolynomial.C : k →+* S))
  map_add' r s := Subtype.ext (map_add (MvPolynomial.C : k →+* S) r s)

/-- Constants first enter the degree-zero piece and then the homogeneous
localization.  `Away` is naturally an algebra over that piece, not directly
over the coefficient field. -/
def xChartCoefficientMap :
    k →+* Away standardConePiece (MvPolynomial.X 0) :=
  (HomogeneousLocalization.fromZeroRingHom standardConePiece _).comp
    xChartDegreeZeroCoefficientMap

/-- Substitute the three coordinate ratios into an affine polynomial. -/
def xChartAffineToAway :
    xChartAffineRing →+* Away standardConePiece (MvPolynomial.X 0) :=
  MvPolynomial.eval₂Hom xChartCoefficientMap xChartRatio

/-- Dehomogenize a four-variable polynomial by setting `X_0=1` and shifting
the remaining variable indices down by one. -/
def xChartDehomogenize : S →+* xChartAffineRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

@[simp]
theorem xChartAffineToAway_X (j : Fin 3) :
    xChartAffineToAway (MvPolynomial.X j) = xChartRatio j := by
  simp [xChartAffineToAway]

@[simp]
theorem xChartDehomogenize_X_zero :
    xChartDehomogenize (MvPolynomial.X 0) = 1 := by
  simp [xChartDehomogenize]

@[simp]
theorem xChartDehomogenize_X_succ (j : Fin 3) :
    xChartDehomogenize (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [xChartDehomogenize]

@[simp]
theorem xChartDehomogenize_X_one :
    xChartDehomogenize (MvPolynomial.X 1) = MvPolynomial.X 0 := by
  simpa using xChartDehomogenize_X_succ (0 : Fin 3)

@[simp]
theorem xChartDehomogenize_X_two :
    xChartDehomogenize (MvPolynomial.X 2) = MvPolynomial.X 1 := by
  simpa using xChartDehomogenize_X_succ (1 : Fin 3)

@[simp]
theorem xChartDehomogenize_X_three :
    xChartDehomogenize (MvPolynomial.X 3) = MvPolynomial.X 2 := by
  simpa using xChartDehomogenize_X_succ (2 : Fin 3)

/-- Evaluate an ordinary localization at `X_0` after setting `X_0=1`.
The universal property applies because the denominator becomes the unit one. -/
noncomputable def xChartLocalizationToAffine :
    Localization.Away (MvPolynomial.X 0 : S) →+* xChartAffineRing :=
  IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X 0 : S))
    (g := xChartDehomogenize) (MvPolynomial.X 0) (by simp)

/-- Restrict dehomogenization from the ordinary localization to its
degree-zero homogeneous subring. -/
noncomputable def xChartAwayToAffine :
    Away standardConePiece (MvPolynomial.X 0) →+* xChartAffineRing :=
  xChartLocalizationToAffine.comp
    (algebraMap (Away standardConePiece (MvPolynomial.X 0))
      (Localization.Away (MvPolynomial.X 0 : S)))

/-- Dehomogenization sends the projective ratio `X_(j+1)/X_0` to the
corresponding affine variable. -/
@[simp]
theorem xChartAwayToAffine_ratio (j : Fin 3) :
    xChartAwayToAffine (xChartRatio j) = MvPolynomial.X j := by
  simp [xChartAwayToAffine, xChartLocalizationToAffine, xChartRatio,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [xChartDehomogenize]

/-- Dehomogenizing a homogeneous fraction amounts to setting `X₀=1` in
its numerator; the power of `X₀` in the denominator then becomes one. -/
@[simp]
theorem xChartAwayToAffine_mk (n : ℕ) (p : S)
    (hp : p ∈ standardConePiece (n • (1 : ℕ))) :
    xChartAwayToAffine
        (Away.mk standardConePiece (coordinate_isHomogeneous 0) n p hp) =
      xChartDehomogenize p := by
  simp [xChartAwayToAffine, xChartLocalizationToAffine,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  simp [xChartDehomogenize]

/-- A homogeneous coordinate monomial divided by the matching power of
`X_0` is the product of its three affine coordinate ratios. -/
theorem xChart_homogeneousMonomialFraction_eq
    (a : ℕ) (ai : Fin 4 → ℕ) (hai : ∑ i, ai i = a)
    (hp : (∏ i, MvPolynomial.X i ^ ai i : S) ∈ standardConePiece a) :
    Away.mk standardConePiece (coordinate_isHomogeneous 0) a
        (∏ i, MvPolynomial.X i ^ ai i) (by simpa using hp) =
      ∏ j : Fin 3, xChartRatio j ^ ai j.succ := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  rw [show
    (∏ j : Fin 3, xChartRatio j ^ ai j.succ).val =
        ∏ j : Fin 3, (xChartRatio j).val ^ ai j.succ by
      rw [← HomogeneousLocalization.algebraMap_apply]
      simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply]]
  simp only [xChartRatio, Away.val_mk, Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  have hsum : ai 0 + ∑ j : Fin 3, ai j.succ = a := by
    simpa only [Fin.sum_univ_succ] using hai
  have hprod :
      (∏ i : Fin 4, MvPolynomial.X i ^ ai i : S) =
        MvPolynomial.X 0 ^ ai 0 *
          ∏ j : Fin 3, MvPolynomial.X j.succ ^ ai j.succ := by
    exact Fin.prod_univ_succ _
  rw [hprod]
  simp only [Submonoid.coe_one, SubmonoidClass.coe_pow, pow_one, one_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [← mul_assoc, ← pow_add]
  have hsum' : (∑ j : Fin 3, ai j.succ) + ai 0 = a := by omega
  rw [hsum']

/-- The four homogeneous variables generate the polynomial ring over its
degree-zero part.  The proof is the structural polynomial induction by
constants, addition, and multiplication by one variable. -/
theorem standardConePiece_adjoin_coordinates :
    Algebra.adjoin (standardConePiece 0)
        (Set.range (MvPolynomial.X : Fin 4 → S)) = ⊤ := by
  let T := Algebra.adjoin (standardConePiece 0)
    (Set.range (MvPolynomial.X : Fin 4 → S))
  refine top_unique fun p hpTop ↦ ?_
  clear hpTop
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa only [SetLike.GradeZero.algebraMap_apply] using
        T.algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin 4) r⟩
  | add p q hp hq =>
      exact T.add_mem hp hq
  | mul_X p i hp =>
      exact T.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- Every degree-zero homogeneous fraction is a polynomial in the three
ratios `X_1/X_0`, `X_2/X_0`, and `X_3/X_0`. -/
theorem xChartAffineToAway_surjective :
    Function.Surjective xChartAffineToAway := by
  have hadjoin :=
    Away.adjoin_mk_prod_pow_eq_top
      (𝒜 := standardConePiece) (coordinate_isHomogeneous 0)
      (Fin 4) (MvPolynomial.X : Fin 4 → S)
      standardConePiece_adjoin_coordinates (fun _ ↦ 1)
      (fun i ↦ coordinate_isHomogeneous i)
  intro z
  change z ∈ xChartAffineToAway.range
  have hz : z ∈ (⊤ : Subalgebra (standardConePiece 0)
      (Away standardConePiece (MvPolynomial.X 0))) := by trivial
  rw [← hadjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      rcases hz with ⟨a, ai, hai, _hbound, rfl⟩
      have hai' : ∑ i, ai i = a := by simpa using hai
      have hp :
          (∏ i : Fin 4, MvPolynomial.X i ^ ai i : S) ∈
            standardConePiece a := by
        have hp' :
            (∏ i : Fin 4, MvPolynomial.X i ^ ai i : S) ∈
              standardConePiece (∑ i : Fin 4, ai i • (1 : ℕ)) :=
          SetLike.prod_pow_mem_graded standardConePiece (fun _ ↦ 1)
            (MvPolynomial.X : Fin 4 → S) ai
            (fun i _ ↦ coordinate_isHomogeneous i)
        simpa [hai'] using hp'
      refine ⟨∏ j : Fin 3, MvPolynomial.X j ^ ai j.succ, ?_⟩
      simp only [map_prod, map_pow, xChartAffineToAway_X]
      exact (xChart_homogeneousMonomialFraction_eq a ai hai' hp).symm
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
      simp only [xChartAffineToAway, MvPolynomial.eval₂Hom_C]
      simp only [MvPolynomial.coeff_C]
      rfl
  | add x y hx hy hxRange hyRange =>
      exact xChartAffineToAway.range.add_mem hxRange hyRange
  | mul x y hx hy hxRange hyRange =>
      exact xChartAffineToAway.range.mul_mem hxRange hyRange

/-- Dehomogenization is a left inverse to substitution of the three affine
coordinate ratios. -/
@[simp]
theorem xChartAwayToAffine_affineToAway (p : xChartAffineRing) :
    xChartAwayToAffine (xChartAffineToAway p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [xChartAffineToAway, MvPolynomial.eval₂Hom_C]
      simp [xChartAwayToAffine, xChartLocalizationToAffine,
        xChartCoefficientMap, xChartDegreeZeroCoefficientMap,
        HomogeneousLocalization.fromZeroRingHom,
        HomogeneousLocalization.algebraMap_apply,
        Localization.mk_eq_mk', IsLocalization.Away.lift]
      rw [IsLocalization.lift_mk'_spec]
      simp [xChartDehomogenize]
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp, xChartAffineToAway_X,
        xChartAwayToAffine_ratio]

/-- Substitution into the projective coordinate ratios is injective. -/
theorem xChartAffineToAway_injective :
    Function.Injective xChartAffineToAway := by
  intro p q hpq
  calc
    p = xChartAwayToAffine (xChartAffineToAway p) :=
      (xChartAwayToAffine_affineToAway p).symm
    _ = xChartAwayToAffine (xChartAffineToAway q) := congrArg xChartAwayToAffine hpq
    _ = q := xChartAwayToAffine_affineToAway q

/-- The standard projective chart `D₊(X₀)` is affine three-space, with
coordinates `X₁/X₀`, `X₂/X₀`, and `X₃/X₀`. -/
noncomputable def xChartAffineEquivAway :
    xChartAffineRing ≃+* Away standardConePiece (MvPolynomial.X 0) :=
  RingEquiv.ofBijective xChartAffineToAway
    ⟨xChartAffineToAway_injective, xChartAffineToAway_surjective⟩

@[simp]
theorem xChartAffineEquivAway_apply (p : xChartAffineRing) :
    xChartAffineEquivAway p = xChartAffineToAway p := rfl

@[simp]
theorem xChartAffineEquivAway_symm_apply
    (z : Away standardConePiece (MvPolynomial.X 0)) :
    xChartAffineEquivAway.symm z = xChartAwayToAffine z := by
  obtain ⟨p, rfl⟩ := xChartAffineToAway_surjective z
  calc
    xChartAffineEquivAway.symm (xChartAffineToAway p) = p := by
      rw [← xChartAffineEquivAway_apply]
      exact xChartAffineEquivAway.symm_apply_apply p
    _ = xChartAwayToAffine (xChartAffineToAway p) :=
      (xChartAwayToAffine_affineToAway p).symm

/-! ## The two equations in ordinary affine coordinates -/

/-- The canonical quadric on the chart `X₀=1`, with affine variables in
the order `(X₁/X₀, X₂/X₀, X₃/X₀)`. -/
def xChartAffineQuadric : xChartAffineRing :=
  MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 0 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 1 * MvPolynomial.X 2

/-- The canonical cubic on the chart `X₀=1`. -/
def xChartAffineCubic : xChartAffineRing :=
  MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2

/-- Setting `X₀=1` in the homogeneous quadric gives the displayed affine
quadric. -/
theorem xChartDehomogenize_quadric :
    xChartDehomogenize canonicalQuadricPolynomial25Two =
      xChartAffineQuadric := by
  simp [canonicalQuadricPolynomial25Two, xChartAffineQuadric]

/-- Setting `X₀=1` in the homogeneous cubic gives the displayed affine
cubic. -/
theorem xChartDehomogenize_cubic :
    xChartDehomogenize canonicalCubicPolynomial25Two =
      xChartAffineCubic := by
  simp [canonicalCubicPolynomial25Two, xChartAffineCubic]

@[simp]
theorem xChartAwayToAffine_dehomogenizedQuadric :
    xChartAwayToAffine (dehomogenizedQuadric 0) =
      xChartAffineQuadric := by
  rw [dehomogenizedQuadric, xChartAwayToAffine_mk,
    xChartDehomogenize_quadric]

@[simp]
theorem xChartAwayToAffine_dehomogenizedCubic :
    xChartAwayToAffine (dehomogenizedCubic 0) =
      xChartAffineCubic := by
  rw [dehomogenizedCubic, xChartAwayToAffine_mk,
    xChartDehomogenize_cubic]

/-- Substitution and dehomogenization are inverse in the other order as
well; surjectivity reduces this statement to the proved left inverse. -/
@[simp]
theorem xChartAffineToAway_awayToAffine
    (z : Away standardConePiece (MvPolynomial.X 0)) :
    xChartAffineToAway (xChartAwayToAffine z) = z := by
  obtain ⟨p, rfl⟩ := xChartAffineToAway_surjective z
  rw [xChartAwayToAffine_affineToAway]

@[simp]
theorem xChartAffineToAway_quadric :
    xChartAffineToAway xChartAffineQuadric =
      dehomogenizedQuadric 0 := by
  rw [← xChartAwayToAffine_dehomogenizedQuadric,
    xChartAffineToAway_awayToAffine]

@[simp]
theorem xChartAffineToAway_cubic :
    xChartAffineToAway xChartAffineCubic =
      dehomogenizedCubic 0 := by
  rw [← xChartAwayToAffine_dehomogenizedCubic,
    xChartAffineToAway_awayToAffine]

/-- The two ordinary affine equations cutting out the N25 curve on
`D₊(X₀)`. -/
def xChartAffineRelation : Fin 2 → xChartAffineRing :=
  Fin.cases xChartAffineQuadric (fun _ ↦ xChartAffineCubic)

@[simp]
theorem xChartAffineRelation_zero :
    xChartAffineRelation 0 = xChartAffineQuadric := rfl

@[simp]
theorem xChartAffineRelation_one :
    xChartAffineRelation 1 = xChartAffineCubic := rfl

/-- The two-element relation family has exactly the expected range. -/
theorem xChartAffineRelation_range :
    Set.range xChartAffineRelation =
      ({xChartAffineQuadric, xChartAffineCubic} : Set xChartAffineRing) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hp
    rcases hp with hp | hp
    · exact ⟨0, hp.symm⟩
    · exact ⟨1, hp.symm⟩

/-- The two ordinary affine equations cutting out the N25 curve on
`D₊(X₀)`.  Using a relation family makes this ideal definitionally suitable
for Mathlib's naive presentation constructor. -/
def xChartAffineEquationIdeal : Ideal xChartAffineRing :=
  Ideal.span (Set.range xChartAffineRelation)

/-- The affine coordinate equivalence carries the ordinary two-equation
ideal exactly to the homogeneous chart ideal. -/
theorem xChartAffineEquationIdeal_map :
    xChartAffineEquationIdeal.map xChartAffineEquivAway.toRingHom =
      chartEquationIdeal 0 := by
  rw [xChartAffineEquationIdeal, xChartAffineRelation_range,
    chartEquationIdeal, Ideal.map_span]
  congr 1
  ext z
  simp [xChartAffineEquivAway_apply, eq_comm]

/-- The actual N25 chart is the spectrum of the ordinary three-variable
polynomial ring modulo its dehomogenized quadric and cubic. -/
noncomputable def xChartCoordinateRingEquiv :
    (xChartAffineRing ⧸ xChartAffineEquationIdeal) ≃+*
      Away literalConePiece
        (canonicalConeGradedProjection (MvPolynomial.X 0)) :=
  (Ideal.quotientEquiv xChartAffineEquationIdeal (chartEquationIdeal 0)
      xChartAffineEquivAway xChartAffineEquationIdeal_map.symm).trans
    (chartCoordinateRingEquiv 0)

end MazurProof.RationalPointsN25QuotientTwoChartIdeal
