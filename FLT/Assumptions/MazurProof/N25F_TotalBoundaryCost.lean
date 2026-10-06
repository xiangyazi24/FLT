import FLT.Assumptions.MazurProof.N25F_BoundarySectionFiltration

/-! Total dimension cost of the three genuine boundary filtrations. -/
noncomputable section
namespace MazurProof.N25F_TotalBoundaryCost
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_BoundarySectionFiltration
open RationalPointsN25QuotientTwoClosedPointPartition

/-- Sequentially impose all three actual boundary multiplicities. -/
theorem finrank_le_sub_three_boundaries (D : ProjectiveDivisor25Two) (a b c : ℕ) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two
        (D - (a : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .X) 1
           - (b : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .YZ) 1
           - (c : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .Z) 1)) + (a + b + c) := by
  have hX := finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple D .X a
  have hY := finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple
    (D - (a : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .X) 1) .YZ b
  have hZ := finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple
    (D - (a : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .X) 1
       - (b : ℤ) • Finsupp.single (fullBoundaryAtomOfTag .YZ) 1) .Z c
  omega

end MazurProof.N25F_TotalBoundaryCost
