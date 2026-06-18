import FLT.Assumptions.MazurProof.TorsionBound
import FLT.Assumptions.MazurProof.TorsionFinite

/-! Smoke test: the main theorem is accessible and usable. -/

open scoped WeierstrassCurve.Affine

#check @MazurProof.mazur_torsion_bound
#check @MazurProof.full_rational_torsion_order_le_two
#check @MazurProof.rational_torsion_finite_of_mw

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 20 := by
  have h := MazurProof.mazur_torsion_bound E
  omega
