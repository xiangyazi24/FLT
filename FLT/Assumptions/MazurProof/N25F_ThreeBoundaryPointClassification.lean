import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThreeProjective

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N25F_ThreeBoundaryPointClassification

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective

/-- A canonical normalized point on the hyperplane `w = 0` is one of the
three explicit boundary points.

This is characteristic-independent: it uses only the signed quadric and
cubic equations over a field. -/
theorem boundary_point_eq_three_cases
    {K : Type*} [Field K] (P : NormalizedProjective4 K)
    (hcurve : IsCanonicalNormalizedThree P)
    (hw : (normalizedCoordinatesThree P).w = 0) :
    P = .xChart 0 0 0 ∨
      P = .yChart (-1) 0 ∨
        P = .zChart 0 := by
  cases P with
  | xChart y z w =>
      change w = 0 at hw
      subst w
      unfold IsCanonicalNormalizedThree at hcurve
      rcases hcurve with ⟨hq, hc⟩
      have hyz : y * z = 0 := by
        simpa [normalizedCoordinatesThree, canonicalCubic25Three] using hc
      rcases mul_eq_zero.mp hyz with hy | hz
      · subst y
        have hz0 : z = 0 := by
          simpa [normalizedCoordinatesThree, canonicalQuadric25Three] using hq
        subst z
        exact Or.inl rfl
      · subst z
        have hy2 : y ^ 2 = 0 := by
          simpa [normalizedCoordinatesThree, canonicalQuadric25Three] using hq
        have hy0 : y = 0 := eq_zero_of_pow_eq_zero hy2
        subst y
        exact Or.inl rfl
  | yChart z w =>
      change w = 0 at hw
      subst w
      unfold IsCanonicalNormalizedThree at hcurve
      rcases hcurve with ⟨hq, _hc⟩
      have hq' : (1 : K) + z = 0 := by
        simpa [normalizedCoordinatesThree, canonicalQuadric25Three] using hq
      have hz : z = -1 := eq_neg_of_add_eq_zero_right hq'
      subst z
      exact Or.inr (Or.inl rfl)
  | zChart w =>
      change w = 0 at hw
      subst w
      exact Or.inr (Or.inr rfl)
  | wChart =>
      change (1 : K) = 0 at hw
      exfalso
      exact one_ne_zero hw

end MazurProof.N25F_ThreeBoundaryPointClassification
