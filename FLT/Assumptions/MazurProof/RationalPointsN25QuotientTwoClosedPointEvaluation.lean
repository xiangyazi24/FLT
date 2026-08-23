import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointChart
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Evaluation of canonical binary curve points on affine charts

A normalized projective point whose pivot is `i` determines evaluation on
the ordinary coordinate ring of `D₊(X_i)`.  The first nonzero coordinate is
one, so this evaluation is compatible with homogeneous dehomogenization.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoClosedPointEvaluation

open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoClosedPointChart
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoStructuralJacobian

/-- Canonical binary curve points whose normalized representative has pivot
`i`. -/
def CurvePointOnChart (i : Fin 4) (K : Type) [Field K] :=
  {P : CurvePointTwo K // normalizedPivot P.1 = i}

/-- The pivot coordinate of a normalized representative is one. -/
@[simp]
theorem normalizedCoordinates25_pivot
    {K : Type} [Field K] (P : NormalizedProjective4 K) :
    coordinates4ToFun (normalizedCoordinates25 P) (normalizedPivot P) = 1 := by
  cases P <;> rfl

/-- Coordinate lookup commutes with coordinatewise scalar maps. -/
theorem coordinates4ToFun_map
    {K L : Type} [Semiring K] [Semiring L]
    (f : K →+* L) (P : Coordinates4 K) (j : Fin 4) :
    coordinates4ToFun
        (RationalPointsN25QuotientBaseChange.Coordinates4.map f P) j =
      f (coordinates4ToFun P j) := by
  fin_cases j <;> rfl

/-- Evaluation of homogeneous binary polynomials at a normalized curve
point. -/
def normalizedPointEval
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    BinaryHomogeneousRing →+* K :=
  MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K)
    (fun j => coordinates4ToFun (normalizedCoordinates25 P.1) j)

/-- Evaluation of the three ordinary affine variables at a point on the
selected chart. -/
def chartPointAffineEval
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    AffineChart i →+* K :=
  MvPolynomial.eval₂Hom (algebraMap (ZMod 2) K)
    (fun j => coordinates4ToFun (normalizedCoordinates25 P.1.1) j.1)

@[simp]
theorem normalizedPointEval_X
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) (j : Fin 4) :
    normalizedPointEval P (MvPolynomial.X j) =
      coordinates4ToFun (normalizedCoordinates25 P.1) j := by
  simp [normalizedPointEval]

@[simp]
theorem chartPointAffineEval_X
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) (j : OtherCoordinate i) :
    chartPointAffineEval i P (MvPolynomial.X j) =
      coordinates4ToFun (normalizedCoordinates25 P.1.1) j.1 := by
  simp [chartPointAffineEval]

/-- Affine evaluation after dehomogenization is homogeneous evaluation at
the same normalized point. -/
theorem chartPointAffineEval_comp_ambientDehomogenize
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    (chartPointAffineEval i P).comp (ambientDehomogenize i) =
      normalizedPointEval P.1 := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [chartPointAffineEval, normalizedPointEval, ambientDehomogenize]
  · intro j
    by_cases hji : j = i
    · subst j
      rw [RingHom.comp_apply, ambientDehomogenize_X_self, map_one,
        normalizedPointEval_X]
      simpa [P.2] using (normalizedCoordinates25_pivot P.1.1).symm
    · let j' : OtherCoordinate i := ⟨j, hji⟩
      rw [RingHom.comp_apply,
        show MvPolynomial.X j = MvPolynomial.X j'.1 from rfl,
        ambientDehomogenize_X_other, chartPointAffineEval_X,
        normalizedPointEval_X]

/-- The four coordinates induced by homogeneous evaluation are exactly the
coordinates of the normalized point. -/
theorem mappedAmbientPoint_normalizedPointEval
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    mappedAmbientPoint (normalizedPointEval P) =
      normalizedCoordinates25 P.1 := by
  cases hP : P.1 <;>
    simp [mappedAmbientPoint, normalizedPointEval, normalizedCoordinates25,
      NormalizedProjective4.coordinates, fieldBinaryOperations, hP,
      coordinates4ToFun]

/-- Homogeneous evaluation at a canonical binary curve point kills the
canonical quadric. -/
@[simp]
theorem normalizedPointEval_quadric_zero
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    normalizedPointEval P canonicalQuadricPolynomial25Two = 0 := by
  rw [map_canonicalQuadric, mappedAmbientPoint_normalizedPointEval]
  have hP : IsCanonicalNormalizedTwo P.1 := P.2
  unfold IsCanonicalNormalizedTwo at hP
  simpa [canonicalQuadric25Binary, fieldBinaryOperations,
    canonicalQuadric25CharTwo, pow_two, add_assoc] using hP.1

/-- Homogeneous evaluation at a canonical binary curve point kills the
canonical cubic. -/
@[simp]
theorem normalizedPointEval_cubic_zero
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    normalizedPointEval P canonicalCubicPolynomial25Two = 0 := by
  rw [map_canonicalCubic, mappedAmbientPoint_normalizedPointEval]
  have hP : IsCanonicalNormalizedTwo P.1 := P.2
  unfold IsCanonicalNormalizedTwo at hP
  simpa [canonicalCubic25Binary, fieldBinaryOperations,
    canonicalCubic25CharTwo, pow_two, add_assoc, mul_assoc] using hP.2

/-- Affine point evaluation kills both dehomogenized chart equations. -/
@[simp]
theorem chartPointAffineEval_relation_zero
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) (r : Fin 2) :
    chartPointAffineEval i P (chartAffineRelation i r) = 0 := by
  refine Fin.cases ?_ (fun s => ?_) r
  · change chartPointAffineEval i P (chartAffineQuadric i) = 0
    rw [chartAffineQuadric]
    change ((chartPointAffineEval i P).comp (ambientDehomogenize i))
      canonicalQuadricPolynomial25Two = 0
    rw [chartPointAffineEval_comp_ambientDehomogenize,
      normalizedPointEval_quadric_zero]
  · have hs : s = 0 := Fin.eq_zero s
    subst s
    change chartPointAffineEval i P (chartAffineCubic i) = 0
    rw [chartAffineCubic]
    change ((chartPointAffineEval i P).comp (ambientDehomogenize i))
      canonicalCubicPolynomial25Two = 0
    rw [chartPointAffineEval_comp_ambientDehomogenize,
      normalizedPointEval_cubic_zero]

/-- The two affine chart equations lie in the kernel of point evaluation. -/
theorem chartAffineEquationIdeal_le_evalKernel
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    chartAffineEquationIdeal i ≤ RingHom.ker (chartPointAffineEval i P) := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro f ⟨r, rfl⟩
  exact chartPointAffineEval_relation_zero i P r

/-- Evaluation of a canonical curve point on the ordinary affine chart
descends through the two-equation chart quotient. -/
def chartQuotientEval
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    ChartQuotient i →+* K :=
  Ideal.Quotient.lift (chartAffineEquationIdeal i)
    (chartPointAffineEval i P)
    (chartAffineEquationIdeal_le_evalKernel i P)

@[simp]
theorem chartQuotientEval_mk
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) (f : AffineChart i) :
    chartQuotientEval i P
        (Ideal.Quotient.mk (chartAffineEquationIdeal i) f) =
      chartPointAffineEval i P f := by
  rfl

/-- Chart evaluation as an algebra homomorphism over the binary prime
field. -/
def chartQuotientEvalAlgHom
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    ChartQuotient i →ₐ[ZMod 2] K where
  __ := chartQuotientEval i P
  commutes' r := by
    change chartPointAffineEval i P (MvPolynomial.C r) =
      algebraMap (ZMod 2) K r
    simp [chartPointAffineEval]

/-! ## Frobenius compatibility -/

/-- Arithmetic Frobenius preserves the selected affine chart. -/
def chartPointFrobenius
    (d : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    CurvePointOnChart i (CommonField 2 d) :=
  ⟨pointFrobenius canonicalTwoModel 2 d P.1, by
    simpa using
      (normalizedPivot_pointFrobenius canonicalTwoModel 2 d P.1).trans P.2⟩

/-- Forgetting the chart proof commutes with every Frobenius iterate. -/
theorem chartPointFrobenius_iterate_val
    (d n : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    ((((chartPointFrobenius d i : _ → _)^[n]) P).1) =
      (((pointFrobenius canonicalTwoModel 2 d : _ → _)^[n]) P.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change pointFrobenius canonicalTwoModel 2 d
          ((((chartPointFrobenius d i : _ → _)^[n]) P).1) =
        pointFrobenius canonicalTwoModel 2 d
          (((pointFrobenius canonicalTwoModel 2 d : _ → _)^[n]) P.1)
      rw [ih]

/-- Affine point evaluation after Frobenius is postcomposition by the
field Frobenius. -/
theorem chartPointAffineEval_frobenius
    (d : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    chartPointAffineEval i (chartPointFrobenius d i P) =
      (commonFrobenius 2 d).toRingEquiv.toRingHom.comp
        (chartPointAffineEval i P) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [chartPointAffineEval]
  · intro j
    rw [chartPointAffineEval_X, RingHom.comp_apply,
      chartPointAffineEval_X]
    change coordinates4ToFun
        (normalizedCoordinates25
          ((pointFrobenius canonicalTwoModel 2 d P.1).1)) j.1 =
      (commonFrobenius 2 d)
        (coordinates4ToFun (normalizedCoordinates25 P.1.1) j.1)
    rw [pointFrobenius_apply_val, ← coordinates_map_two]
    exact coordinates4ToFun_map
      (commonFrobenius 2 d).toRingEquiv.toRingHom
      (normalizedCoordinates25 P.1.1) j.1

/-- Quotient-chart evaluation is equivariant for arithmetic Frobenius. -/
theorem chartQuotientEval_frobenius
    (d : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    chartQuotientEval i (chartPointFrobenius d i P) =
      (commonFrobenius 2 d).toRingEquiv.toRingHom.comp
        (chartQuotientEval i P) := by
  apply Ideal.Quotient.ringHom_ext
  change chartPointAffineEval i (chartPointFrobenius d i P) =
    (commonFrobenius 2 d).toRingEquiv.toRingHom.comp
      (chartPointAffineEval i P)
  exact chartPointAffineEval_frobenius d i P

/-- Frobenius-conjugate points define the same prime kernel on the affine
chart quotient. -/
theorem chartQuotientEval_frobenius_ker
    (d : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    RingHom.ker (chartQuotientEval i (chartPointFrobenius d i P)) =
      RingHom.ker (chartQuotientEval i P) := by
  rw [chartQuotientEval_frobenius]
  ext f
  simp

/-- The affine evaluation kernel regarded as a point of the prime spectrum
of the selected chart quotient. -/
def chartPointPrime
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    PrimeSpectrum (ChartQuotient i) :=
  ⟨RingHom.ker (chartQuotientEval i P),
    RingHom.ker_isPrime (chartQuotientEval i P)⟩

/-- The residue ring cut out by a point-evaluation kernel on its affine
chart. -/
abbrev ChartPointResidue
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :=
  ChartQuotient i ⧸ RingHom.ker (chartQuotientEval i P)

/-- The residue ring is canonically the subring of the coordinate field
generated by the affine coordinates of the point. -/
def chartPointResidueEquivRange
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    ChartPointResidue i P ≃+* (chartQuotientEval i P).range :=
  RingHom.quotientKerEquivRange (chartQuotientEval i P)

/-- Over a finite coordinate field, the point residue ring is finite. -/
noncomputable instance chartPointResidueFinite
    {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    Finite (ChartPointResidue i P) := by
  letI : Finite (chartQuotientEval i P).range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Finite.of_equiv (chartQuotientEval i P).range
    (chartPointResidueEquivRange i P).symm.toEquiv

/-- A finite point residue domain is a field. -/
theorem chartPointResidue_isField
    {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    IsField (ChartPointResidue i P) := by
  letI : (RingHom.ker (chartQuotientEval i P)).IsPrime :=
    RingHom.ker_isPrime (chartQuotientEval i P)
  exact Finite.isField_of_domain (ChartPointResidue i P)

/-- Evaluation at a point over a finite field cuts out a maximal ideal on
its affine chart. -/
theorem chartPointPrime_isMaximal
    {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K]
    (i : Fin 4) (P : CurvePointOnChart i K) :
    (chartPointPrime i P).asIdeal.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    (chartPointResidue_isField i P)

/-- Frobenius-conjugate points induce the same affine prime. -/
@[simp]
theorem chartPointPrime_frobenius
    (d : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    chartPointPrime i (chartPointFrobenius d i P) =
      chartPointPrime i P := by
  apply PrimeSpectrum.ext
  exact chartQuotientEval_frobenius_ker d i P

/-- Every Frobenius iterate induces the same affine prime. -/
theorem chartPointPrime_frobenius_iterate
    (d n : ℕ) (i : Fin 4)
    (P : CurvePointOnChart i (CommonField 2 d)) :
    chartPointPrime i (((chartPointFrobenius d i)^[n]) P) =
      chartPointPrime i P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', chartPointPrime_frobenius, ih]

end MazurProof.RationalPointsN25QuotientTwoClosedPointEvaluation
