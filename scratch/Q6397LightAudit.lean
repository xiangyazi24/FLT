import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF2

namespace Q6397LightAudit

open MazurProof.RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction

/-- The sole missing rational-point seam after the proved coordinate-boundary classification. -/
def NoDenseTorusCanonicalPoint25 : Prop :=
  ∀ p : Coordinates25,
    OnCanonical25 p →
    NonzeroQuadruple p.x p.y p.z p.w →
    p.x ≠ 0 → p.y ≠ 0 → p.z ≠ 0 → p.w ≠ 0 → False

/-- Boundary classification plus the dense-torus seam gives the full classifier. -/
theorem canonical_classification_of_no_dense_torus
    (hDense : NoDenseTorusCanonicalPoint25) :
    ∀ p : Coordinates25,
      OnCanonical25 p →
      NonzeroQuadruple p.x p.y p.z p.w →
      IsCusp25 p := by
  intro p hp hnz
  change IsCanonicalCusp25 p.x p.y p.z p.w
  by_cases hx : p.x = 0
  · exact canonical_point_with_zero_coordinate_is_cusp hnz hp.1 hp.2
      (Or.inl hx)
  by_cases hy : p.y = 0
  · exact canonical_point_with_zero_coordinate_is_cusp hnz hp.1 hp.2
      (Or.inr (Or.inl hy))
  by_cases hz : p.z = 0
  · exact canonical_point_with_zero_coordinate_is_cusp hnz hp.1 hp.2
      (Or.inr (Or.inr (Or.inl hz)))
  by_cases hw : p.w = 0
  · exact canonical_point_with_zero_coordinate_is_cusp hnz hp.1 hp.2
      (Or.inr (Or.inr (Or.inr hw)))
  exact False.elim (hDense p hp hnz hx hy hz hw)

end Q6397LightAudit

#print axioms MazurProof.RationalPointsN25CanonicalPoints.canonical_point_with_zero_coordinate_is_cusp
#print axioms MazurProof.RationalPointsN25CanonicalPoints.all_coordinates_ne_zero_of_not_cusp
#print axioms MazurProof.RationalPointsN25CanonicalPoints.noncuspidal_point_to_plane_sextic
#print axioms MazurProof.RationalPointsN25QuotientF2.canonical_point25F2_iff_cusp
#print axioms Q6397LightAudit.canonical_classification_of_no_dense_torus
