import FLT.Assumptions.MazurProof.RationalPointsN25CanonicalSourceBridge
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF2
import FLT.Assumptions.MazurProof.RationalPointsN25DegreeTwoPullback
import FLT.Assumptions.MazurProof.CyclicExclusion25

namespace Q6397Audit

open MazurProof
open MazurProof.TateOrder25Factor
open MazurProof.RationalPointsN25CanonicalPoints
open MazurProof.RationalPointsN25QuotientAction
open MazurProof.RationalPointsN25CanonicalSourceBridge

/-- The exact arithmetic seam: rule out a noncuspidal point in the dense torus. -/
def NoDenseTorusCanonicalPoint25 : Prop :=
  ∀ p : Coordinates25,
    OnCanonical25 p →
    NonzeroQuadruple p.x p.y p.z p.w →
    p.x ≠ 0 → p.y ≠ 0 → p.z ≠ 0 → p.w ≠ 0 → False

/-- Existing boundary classification plus the dense-torus seam gives the full
rational-point classification needed by the order-25 endpoint. -/
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

/-- Once the full canonical classification exists, the explicit primitive
Tate obstruction is discharged by the already checked source bridge. -/
theorem no_explicit_order25_obstruction_of_canonical_classification
    (hclass :
      ∀ p : Coordinates25,
        OnCanonical25 p →
        NonzeroQuadruple p.x p.y p.z p.w →
        IsCusp25 p) :
    ¬ ExplicitOrder25Obstruction := by
  rintro ⟨b, c, _hEll, hb, h5, hF⟩
  let p := tateCanonicalCoordinates25 b c
  have hpOn : OnCanonical25 p := by
    simpa [p] using tateCanonicalCoordinates25_onCanonical hb h5 hF
  have hpNz : NonzeroQuadruple p.x p.y p.z p.w := by
    simpa [p] using tateCanonicalCoordinates25_nonzero hb h5 hF
  have hpNot : ¬ IsCusp25 p := by
    simpa [p] using tateCanonicalCoordinates25_not_isCusp hb h5 hF
  exact hpNot (hclass p hpOn hpNz)

/-- Exact endpoint wiring from only the dense-torus theorem. -/
theorem no_explicit_order25_obstruction_of_no_dense_torus
    (hDense : NoDenseTorusCanonicalPoint25) :
    ¬ ExplicitOrder25Obstruction :=
  no_explicit_order25_obstruction_of_canonical_classification
    (canonical_classification_of_no_dense_torus hDense)

end Q6397Audit

#print axioms MazurProof.RationalPointsN25CanonicalPoints.canonical_point_with_zero_coordinate_is_cusp
#print axioms MazurProof.RationalPointsN25CanonicalPoints.all_coordinates_ne_zero_of_not_cusp
#print axioms MazurProof.RationalPointsN25CanonicalPoints.noncuspidal_point_to_plane_sextic
#print axioms MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_nonzero
#print axioms MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_onCanonical
#print axioms MazurProof.RationalPointsN25CanonicalSourceBridge.tateCanonicalCoordinates25_not_isCusp
#print axioms MazurProof.RationalPointsN25QuotientF2.canonical_point25F2_iff_cusp
#print axioms MazurProof.RationalPointsN25ReductionCardinality.natCard_dvd_seventy_one_of_two_reductions
#print axioms MazurProof.RationalPointsN25DegreeTwoPullback.pull_injective_of_two_reductions_and_norm_comp_eq_two
#print axioms Q6397Audit.canonical_classification_of_no_dense_torus
#print axioms Q6397Audit.no_explicit_order25_obstruction_of_canonical_classification
#print axioms Q6397Audit.no_explicit_order25_obstruction_of_no_dense_torus
#print axioms MazurProof.CyclicExclusion25.no_explicit_order25_obstruction
#print axioms MazurProof.CyclicExclusion25.no_rational_point_of_order_25
