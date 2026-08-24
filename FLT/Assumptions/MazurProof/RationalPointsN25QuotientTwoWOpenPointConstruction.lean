import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField

/-!
# Constructing points on the canonical W chart

An affine solution of the two dehomogenized curve equations determines a
point on the projective curve with fourth coordinate one.  The canonical
normalized representative may lie in any of the four first-nonzero charts,
so the construction explicitly selects that chart and proves that
normalization at `W` recovers the original affine coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWOpenPointConstruction

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoPlaneFunctionField

/-- The canonical first-nonzero representative of `[x:y:z:1]`. -/
noncomputable def normalizedWPoint {K : Type} [Field K] (x y z : K) :
    NormalizedProjective4 K := by
  classical
  exact if hx : x = 0 then
      if hy : y = 0 then
        if hz : z = 0 then .wChart else .zChart z⁻¹
      else .yChart (z / y) y⁻¹
    else .xChart (y / x) (z / x) x⁻¹

/-- The fourth coordinate of the canonical representative is nonzero. -/
theorem normalizedWPoint_w_ne_zero
    {K : Type} [Field K] (x y z : K) :
    (normalizedCoordinates25 (normalizedWPoint x y z)).w ≠ 0 := by
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · by_cases hz : z = 0
      · simp [normalizedWPoint, hx, hy, hz, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations]
      · simp [normalizedWPoint, hx, hy, hz, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations]
    · simp [normalizedWPoint, hx, hy, normalizedCoordinates25,
        NormalizedProjective4.coordinates, fieldBinaryOperations]
  · simp [normalizedWPoint, hx, normalizedCoordinates25,
      NormalizedProjective4.coordinates, fieldBinaryOperations]

/-- Normalizing the canonical representative at `W` recovers
`[x:y:z:1]`. -/
theorem normalizeAtW_normalizedWPoint
    {K : Type} [Field K] (x y z : K) :
    normalizeAtW (normalizedCoordinates25 (normalizedWPoint x y z)) =
      wChartPoint x y z := by
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · by_cases hz : z = 0
      · simp [normalizedWPoint, hx, hy, hz, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations,
          normalizeAtW, scaleCoordinates4, wChartPoint]
      · simp [normalizedWPoint, hx, hy, hz, normalizedCoordinates25,
          NormalizedProjective4.coordinates, fieldBinaryOperations,
          normalizeAtW, scaleCoordinates4, wChartPoint]
    ·
      simp [normalizedWPoint, hx, hy, normalizedCoordinates25,
        NormalizedProjective4.coordinates, fieldBinaryOperations,
        normalizeAtW, scaleCoordinates4, wChartPoint, div_eq_mul_inv]
      field_simp
  · simp [normalizedWPoint, hx, normalizedCoordinates25,
      NormalizedProjective4.coordinates, fieldBinaryOperations,
      normalizeAtW, scaleCoordinates4, wChartPoint, div_eq_mul_inv]
    constructor <;> field_simp

/-- Affine solutions of the two chart equations give canonical normalized
projective solutions. -/
theorem normalizedWPoint_isCanonical
    {K : Type} [Field K] [CharP K 2] (x y z : K)
    (hq : canonicalQuadric25CharTwo (wChartPoint x y z) = 0)
    (hc : canonicalCubic25CharTwo (wChartPoint x y z) = 0) :
    IsCanonicalNormalizedTwo (normalizedWPoint x y z) := by
  let C := normalizedCoordinates25 (normalizedWPoint x y z)
  have hw : C.w ≠ 0 := normalizedWPoint_w_ne_zero x y z
  have hcoords : normalizeAtW C = wChartPoint x y z :=
    normalizeAtW_normalizedWPoint x y z
  have hqC : canonicalQuadric25CharTwo C = 0 := by
    have hs := canonicalQuadric25CharTwo_scale C.w⁻¹ C
    rw [← hcoords, normalizeAtW] at hq
    rw [hq] at hs
    exact (mul_eq_zero.mp hs.symm).resolve_left (pow_ne_zero 2 (inv_ne_zero hw))
  have hcC : canonicalCubic25CharTwo C = 0 := by
    have hs := canonicalCubic25CharTwo_scale C.w⁻¹ C
    rw [← hcoords, normalizeAtW] at hc
    rw [hc] at hs
    exact (mul_eq_zero.mp hs.symm).resolve_left (pow_ne_zero 3 (inv_ne_zero hw))
  unfold IsCanonicalNormalizedTwo
  exact ⟨by
    simpa [C, fieldBinaryOperations, canonicalQuadric25Binary,
      canonicalQuadric25CharTwo, pow_two, add_assoc] using hqC,
    by
      simpa [C, fieldBinaryOperations, canonicalCubic25Binary,
        canonicalCubic25CharTwo, pow_two] using hcC⟩

/-- Construct a point on the projective `W` open from affine coordinates
satisfying both chart equations. -/
noncomputable def curvePointOnWOpenOfCoordinates
    {K : Type} [Field K] [CharP K 2] (x y z : K)
    (hq : canonicalQuadric25CharTwo (wChartPoint x y z) = 0)
    (hc : canonicalCubic25CharTwo (wChartPoint x y z) = 0) :
    CurvePointOnWOpen K :=
  ⟨⟨normalizedWPoint x y z,
      normalizedWPoint_isCanonical x y z hq hc⟩,
    normalizedWPoint_w_ne_zero x y z⟩

/-- The constructed point has the prescribed fixed-chart coordinates. -/
@[simp] theorem curvePointOnWOpenOfCoordinates_coordinates
    {K : Type} [Field K] [CharP K 2] (x y z : K)
    (hq : canonicalQuadric25CharTwo (wChartPoint x y z) = 0)
    (hc : canonicalCubic25CharTwo (wChartPoint x y z) = 0) :
    wOpenCoordinates (curvePointOnWOpenOfCoordinates x y z hq hc) =
      wChartPoint x y z :=
  normalizeAtW_normalizedWPoint x y z

end MazurProof.RationalPointsN25QuotientTwoWOpenPointConstruction
