import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineChartsSmooth
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoBaseChange

/-!
# Evaluation on the canonical binary curve's `W != 0` open

The existing canonical chart attached to a normalized projective point is
selected by its first nonzero coordinate.  That notion does not identify all
points of the geometric open `W != 0`.  Here a point on that open is divided
by its canonical representative's `W` coordinate and evaluated on the fixed
`w = 1` chart quotient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientTwoBaseChange
open NormalizedProjectiveCurveFrobenius

/-- A canonical curve point on the projective open where its fourth
homogeneous coordinate is nonzero. -/
structure CurvePointOnWOpen (K : Type) [Field K] where
  point : CurvePoint canonicalTwoModel K
  w_ne_zero : (normalizedCoordinates25 point.1).w ≠ 0

/-- The fixed affine coordinate ring used for the `W != 0` open. -/
abbrev WChartQuotient := ChartQuotient (3 : Fin 4)

/-- Scalar multiplication of a four-coordinate vector. -/
def scaleCoordinates4 {K : Type*} [Mul K]
    (a : K) (C : Coordinates4 K) : Coordinates4 K :=
  ⟨a * C.x, a * C.y, a * C.z, a * C.w⟩

/-- Divide a four-coordinate vector by its fourth coordinate. -/
def normalizeAtW {K : Type*} [Field K]
    (C : Coordinates4 K) : Coordinates4 K :=
  scaleCoordinates4 C.w⁻¹ C

/-- The canonical `w = 1` representative of a point on the `W != 0` open. -/
def wOpenCoordinates {K : Type} [Field K]
    (P : CurvePointOnWOpen K) : Coordinates4 K :=
  normalizeAtW (normalizedCoordinates25 P.point.1)

@[simp]
theorem normalizeAtW_x {K : Type*} [Field K] (C : Coordinates4 K) :
    (normalizeAtW C).x = C.x / C.w := by
  simp [normalizeAtW, scaleCoordinates4, div_eq_mul_inv, mul_comm]

@[simp]
theorem normalizeAtW_y {K : Type*} [Field K] (C : Coordinates4 K) :
    (normalizeAtW C).y = C.y / C.w := by
  simp [normalizeAtW, scaleCoordinates4, div_eq_mul_inv, mul_comm]

@[simp]
theorem normalizeAtW_z {K : Type*} [Field K] (C : Coordinates4 K) :
    (normalizeAtW C).z = C.z / C.w := by
  simp [normalizeAtW, scaleCoordinates4, div_eq_mul_inv, mul_comm]

@[simp]
theorem wOpenCoordinates_w
    {K : Type} [Field K] (P : CurvePointOnWOpen K) :
    (wOpenCoordinates P).w = 1 := by
  simp [wOpenCoordinates, normalizeAtW, scaleCoordinates4, P.w_ne_zero]

/-- The canonical characteristic-two quadric is homogeneous of degree two. -/
theorem canonicalQuadric25CharTwo_scale
    {K : Type*} [CommRing K] (a : K) (C : Coordinates4 K) :
    canonicalQuadric25CharTwo (scaleCoordinates4 a C) =
      a ^ 2 * canonicalQuadric25CharTwo C := by
  simp [scaleCoordinates4, canonicalQuadric25CharTwo]
  ring

/-- The canonical characteristic-two cubic is homogeneous of degree three. -/
theorem canonicalCubic25CharTwo_scale
    {K : Type*} [CommRing K] (a : K) (C : Coordinates4 K) :
    canonicalCubic25CharTwo (scaleCoordinates4 a C) =
      a ^ 3 * canonicalCubic25CharTwo C := by
  simp [scaleCoordinates4, canonicalCubic25CharTwo]
  ring

private theorem canonicalPoint_quadric_zero
    {K : Type} [Field K] (P : CurvePoint canonicalTwoModel K) :
    canonicalQuadric25CharTwo (normalizedCoordinates25 P.1) = 0 := by
  have hP : IsCanonicalNormalizedTwo P.1 := P.2
  rcases hP with ⟨hq, _⟩
  simpa [fieldBinaryOperations, canonicalQuadric25Binary,
    canonicalQuadric25CharTwo, pow_two, add_assoc] using hq

private theorem canonicalPoint_cubic_zero
    {K : Type} [Field K] (P : CurvePoint canonicalTwoModel K) :
    canonicalCubic25CharTwo (normalizedCoordinates25 P.1) = 0 := by
  have hP : IsCanonicalNormalizedTwo P.1 := P.2
  rcases hP with ⟨_, hc⟩
  simpa [fieldBinaryOperations, canonicalCubic25Binary,
    canonicalCubic25CharTwo, pow_two] using hc

@[simp]
theorem wOpenCoordinates_quadric
    {K : Type} [Field K] (P : CurvePointOnWOpen K) :
    canonicalQuadric25CharTwo (wOpenCoordinates P) = 0 := by
  rw [wOpenCoordinates, normalizeAtW,
    canonicalQuadric25CharTwo_scale,
    canonicalPoint_quadric_zero P.point, mul_zero]

@[simp]
theorem wOpenCoordinates_cubic
    {K : Type} [Field K] (P : CurvePointOnWOpen K) :
    canonicalCubic25CharTwo (wOpenCoordinates P) = 0 := by
  rw [wOpenCoordinates, normalizeAtW,
    canonicalCubic25CharTwo_scale,
    canonicalPoint_cubic_zero P.point, mul_zero]

/-- The canonical coefficient homomorphism from the binary prime field. -/
def charTwoCoefficientHom
    {K : Type*} [Ring K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

/-- Evaluation of homogeneous polynomials at the `w = 1` representative. -/
def wOpenAmbientEval
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) : BinaryHomogeneousRing →+* K :=
  MvPolynomial.eval₂Hom (charTwoCoefficientHom (K := K))
    (coordinates4ToFun (wOpenCoordinates P))

@[simp]
theorem wOpenAmbientEval_X
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) (j : Fin 4) :
    wOpenAmbientEval P (MvPolynomial.X j) =
      coordinates4ToFun (wOpenCoordinates P) j := by
  simp [wOpenAmbientEval]

@[simp]
theorem mappedAmbientPoint_wOpenAmbientEval
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    mappedAmbientPoint (wOpenAmbientEval P) = wOpenCoordinates P := by
  cases hC : wOpenCoordinates P with
  | mk x y z w =>
      simp [mappedAmbientPoint, wOpenAmbientEval, coordinates4ToFun, hC]

@[simp]
theorem wOpenAmbientEval_quadric
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    wOpenAmbientEval P canonicalQuadricPolynomial25Two = 0 := by
  rw [map_canonicalQuadric, mappedAmbientPoint_wOpenAmbientEval]
  exact wOpenCoordinates_quadric P

@[simp]
theorem wOpenAmbientEval_cubic
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    wOpenAmbientEval P canonicalCubicPolynomial25Two = 0 := by
  rw [map_canonicalCubic, mappedAmbientPoint_wOpenAmbientEval]
  exact wOpenCoordinates_cubic P

/-- Evaluation of ordinary affine polynomials on the fixed `w = 1` chart. -/
def wOpenAffineEval
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) : AffineChart (3 : Fin 4) →+* K :=
  MvPolynomial.eval₂Hom (charTwoCoefficientHom (K := K))
    (fun j : OtherCoordinate (3 : Fin 4) =>
      coordinates4ToFun (wOpenCoordinates P) j.1)

/-- Affine evaluation after dehomogenization equals homogeneous evaluation
at the `w = 1` representative. -/
theorem wOpenAffineEval_comp_ambientDehomogenize
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    (wOpenAffineEval P).comp (ambientDehomogenize (3 : Fin 4)) =
      wOpenAmbientEval P := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [wOpenAffineEval, wOpenAmbientEval,
      ambientDehomogenize, charTwoCoefficientHom]
  · intro j
    fin_cases j <;>
      simp [wOpenAffineEval, wOpenAmbientEval,
        ambientDehomogenize, dehomogenizedVariable,
        coordinates4ToFun, wOpenCoordinates,
        normalizeAtW, scaleCoordinates4, P.w_ne_zero]

@[simp]
theorem wOpenAffineEval_quadric
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    wOpenAffineEval P (chartAffineQuadric (3 : Fin 4)) = 0 := by
  change ((wOpenAffineEval P).comp (ambientDehomogenize (3 : Fin 4)))
      canonicalQuadricPolynomial25Two = 0
  rw [wOpenAffineEval_comp_ambientDehomogenize]
  exact wOpenAmbientEval_quadric P

@[simp]
theorem wOpenAffineEval_cubic
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    wOpenAffineEval P (chartAffineCubic (3 : Fin 4)) = 0 := by
  change ((wOpenAffineEval P).comp (ambientDehomogenize (3 : Fin 4)))
      canonicalCubicPolynomial25Two = 0
  rw [wOpenAffineEval_comp_ambientDehomogenize]
  exact wOpenAmbientEval_cubic P

/-- Both affine chart equations vanish under evaluation on the `W != 0`
open. -/
theorem chartAffineEquationIdeal_three_le_ker
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) :
    chartAffineEquationIdeal (3 : Fin 4) ≤ RingHom.ker (wOpenAffineEval P) := by
  rw [chartAffineEquationIdeal, Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  fin_cases r
  · change wOpenAffineEval P (chartAffineQuadric 3) = 0
    exact wOpenAffineEval_quadric P
  · change wOpenAffineEval P (chartAffineCubic 3) = 0
    exact wOpenAffineEval_cubic P

/-- Evaluation of the fixed `w = 1` chart quotient at an arbitrary
projective curve point with nonzero fourth coordinate. -/
def wOpenChartQuotientEval
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) : WChartQuotient →+* K :=
  Ideal.Quotient.lift (chartAffineEquationIdeal (3 : Fin 4))
    (wOpenAffineEval P)
    (fun _ ha => RingHom.mem_ker.mp
      (chartAffineEquationIdeal_three_le_ker P ha))

@[simp]
theorem wOpenChartQuotientEval_mk
    {K : Type} [Field K] [CharP K 2]
    (P : CurvePointOnWOpen K) (f : AffineChart (3 : Fin 4)) :
    wOpenChartQuotientEval P
        (Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4)) f) =
      wOpenAffineEval P f := by
  rfl

/-- Evaluation on the fixed `W` chart as an algebra homomorphism over the
binary prime field. -/
def wOpenChartQuotientEvalAlgHom
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (P : CurvePointOnWOpen K) : WChartQuotient →ₐ[ZMod 2] K where
  __ := wOpenChartQuotientEval P
  commutes' r := by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    simp [wOpenChartQuotientEval, wOpenAffineEval,
      charTwoCoefficientHom]

/-! ## Compatibility with coefficient-field equivalences -/

@[simp]
theorem map_scaleCoordinates4
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (a : K) (C : Coordinates4 K) :
    Coordinates4.map f (scaleCoordinates4 a C) =
      scaleCoordinates4 (f a) (Coordinates4.map f C) := by
  cases C
  simp [Coordinates4.map, scaleCoordinates4]

@[simp]
theorem map_normalizeAtW
    {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (C : Coordinates4 K) :
    Coordinates4.map e.toRingHom (normalizeAtW C) =
      normalizeAtW (Coordinates4.map e.toRingHom C) := by
  cases C
  simp [Coordinates4.map, normalizeAtW, scaleCoordinates4]

/-- Transport a point of the `W != 0` open through a coefficient-field
equivalence. -/
noncomputable def CurvePointOnWOpen.map
    {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (P : CurvePointOnWOpen K) : CurvePointOnWOpen L where
  point := curvePointEquiv canonicalTwoModel e P.point
  w_ne_zero := by
    change (normalizedCoordinates25
      (NormalizedProjective4.map e.toRingHom P.point.1)).w ≠ 0
    have hw := congrArg Coordinates4.w
      (coordinates_map_two e.toRingHom P.point.1)
    rw [← hw]
    exact (map_ne_zero e).2 P.w_ne_zero

@[simp]
theorem wOpenCoordinates_map
    {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (P : CurvePointOnWOpen K) :
    Coordinates4.map e.toRingHom (wOpenCoordinates P) =
      wOpenCoordinates (P.map e) := by
  change Coordinates4.map e.toRingHom
      (normalizeAtW (normalizedCoordinates25 P.point.1)) =
    normalizeAtW
      (normalizedCoordinates25
        (NormalizedProjective4.map e.toRingHom P.point.1))
  rw [map_normalizeAtW, coordinates_map_two]

/-- Affine `W`-chart evaluation commutes with every characteristic-two
coefficient-field equivalence. -/
theorem wOpenAffineEval_map
    {K L : Type} [Field K] [Field L] [CharP K 2] [CharP L 2]
    (e : K ≃+* L) (P : CurvePointOnWOpen K) :
    e.toRingHom.comp (wOpenAffineEval P) =
      wOpenAffineEval (P.map e) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    simp [wOpenAffineEval, charTwoCoefficientHom]
  · rintro ⟨j, hj⟩
    have hmap := wOpenCoordinates_map e P
    fin_cases j
    · simpa [wOpenAffineEval, Coordinates4.map, coordinates4ToFun] using
        congrArg Coordinates4.x hmap
    · simpa [wOpenAffineEval, Coordinates4.map, coordinates4ToFun] using
        congrArg Coordinates4.y hmap
    · simpa [wOpenAffineEval, Coordinates4.map, coordinates4ToFun] using
        congrArg Coordinates4.z hmap
    · exact (hj rfl).elim

/-- Quotient evaluation on the fixed `W` chart commutes with coefficient
field equivalences. -/
theorem wOpenChartQuotientEval_map
    {K L : Type} [Field K] [Field L] [CharP K 2] [CharP L 2]
    (e : K ≃+* L) (P : CurvePointOnWOpen K) :
    e.toRingHom.comp (wOpenChartQuotientEval P) =
      wOpenChartQuotientEval (P.map e) := by
  apply Ideal.Quotient.ringHom_ext
  exact wOpenAffineEval_map e P

/-- Coefficient-field equivalences preserve the evaluation kernel on the
fixed `W` chart. -/
theorem wOpenChartQuotientEval_ker_map
    {K L : Type} [Field K] [Field L] [CharP K 2] [CharP L 2]
    (e : K ≃+* L) (P : CurvePointOnWOpen K) :
    RingHom.ker (wOpenChartQuotientEval (P.map e)) =
      RingHom.ker (wOpenChartQuotientEval P) := by
  rw [← wOpenChartQuotientEval_map e P]
  ext q
  simp

end MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
