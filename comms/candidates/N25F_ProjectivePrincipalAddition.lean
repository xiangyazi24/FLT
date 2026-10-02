import FLT.Assumptions.MazurProof.N25F_PrincipalOrderAddition
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalCoefficients

/-! Each coefficient of the existing actual projective principal divisor
satisfies the minimum inequality for addition of nonzero functions. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_ProjectivePrincipalAddition
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_PrincipalOrderAddition
open N25F_NonBoundaryPrincipalDivisor
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

private theorem x_boundary_add_ge_min (f g h : Additive CurveFieldˣ)
    (hadd : (h.toMul : CurveField) = (f.toMul : CurveField) + (g.toMul : CurveField)) :
    min (xBoundaryOrder f) (xBoundaryOrder g) ≤ xBoundaryOrder h := by
  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
  change min (WithZero.log (Ring.ordFrac XLocalRing (f.toMul : CurveField)))
    (WithZero.log (Ring.ordFrac XLocalRing (g.toMul : CurveField))) ≤
      WithZero.log (Ring.ordFrac XLocalRing (h.toMul : CurveField))
  rw [hadd]
  exact log_ordFrac_add_ge_min _ _ f.toMul.ne_zero g.toMul.ne_zero
    (by rw [← hadd]; exact h.toMul.ne_zero)

private theorem yz_boundary_add_ge_min (f g h : Additive CurveFieldˣ)
    (hadd : (h.toMul : CurveField) = (f.toMul : CurveField) + (g.toMul : CurveField)) :
    min (yzBoundaryOrder f) (yzBoundaryOrder g) ≤ yzBoundaryOrder h := by
  letI : Algebra YZLocalRing CurveField := yzLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing YZLocalRing CurveField := yzLocalToFraction_isFractionRing
  change min (WithZero.log (Ring.ordFrac YZLocalRing (f.toMul : CurveField)))
    (WithZero.log (Ring.ordFrac YZLocalRing (g.toMul : CurveField))) ≤
      WithZero.log (Ring.ordFrac YZLocalRing (h.toMul : CurveField))
  rw [hadd]
  exact log_ordFrac_add_ge_min _ _ f.toMul.ne_zero g.toMul.ne_zero
    (by rw [← hadd]; exact h.toMul.ne_zero)

private theorem z_boundary_add_ge_min (f g h : Additive CurveFieldˣ)
    (hadd : (h.toMul : CurveField) = (f.toMul : CurveField) + (g.toMul : CurveField)) :
    min (zBoundaryOrder f) (zBoundaryOrder g) ≤ zBoundaryOrder h := by
  letI : Algebra ZLocalRing CurveField := zLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing ZLocalRing CurveField := zLocalToFraction_isFractionRing
  change min (WithZero.log (Ring.ordFrac ZLocalRing (f.toMul : CurveField)))
    (WithZero.log (Ring.ordFrac ZLocalRing (g.toMul : CurveField))) ≤
      WithZero.log (Ring.ordFrac ZLocalRing (h.toMul : CurveField))
  rw [hadd]
  exact log_ordFrac_add_ge_min _ _ f.toMul.ne_zero g.toMul.ne_zero
    (by rw [← hadd]; exact h.toMul.ne_zero)

/-- The actual principal divisor satisfies the valuation minimum inequality
at every full closed point, with no omitted boundary or residue degrees. -/
theorem projectivePrincipalDivisor_add_ge_min
    (f g h : Additive CurveFieldˣ)
    (hadd : (h.toMul : CurveField) = (f.toMul : CurveField) + (g.toMul : CurveField))
    (A : fullClosedPointGrading25Two.Atom) :
    min (projectivePrincipalDivisor f A) (projectivePrincipalDivisor g A) ≤
      projectivePrincipalDivisor h A := by
  obtain ⟨s, rfl⟩ := boundaryNonBoundaryToFullAtom_surjective A
  cases s with
  | inl t =>
      cases t with
      | X =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_X]
          exact x_boundary_add_ge_min f g h hadd
      | YZ =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_YZ]
          exact yz_boundary_add_ge_min f g h hadd
      | Z =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_Z]
          exact z_boundary_add_ge_min f g h hadd
  | inr B =>
      simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_nonBoundary,
        nonBoundaryPrincipalDivisor_apply]
      change min (FractionalIdeal.count CurveField (fullNonBoundaryAtomEquivHeightOne B)
          (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField)))
        (FractionalIdeal.count CurveField (fullNonBoundaryAtomEquivHeightOne B)
          (FractionalIdeal.spanSingleton W⁰ (g.toMul : CurveField))) ≤
        FractionalIdeal.count CurveField (fullNonBoundaryAtomEquivHeightOne B)
          (FractionalIdeal.spanSingleton W⁰ (h.toMul : CurveField))
      rw [hadd]
      exact count_spanSingleton_add_ge_min (fullNonBoundaryAtomEquivHeightOne B)
        _ _ f.toMul.ne_zero g.toMul.ne_zero (by rw [← hadd]; exact h.toMul.ne_zero)

end MazurProof.N25F_ProjectivePrincipalAddition
