import FLT.Assumptions.MazurProof.TorsionBound

/-! Smoke test: the main theorem is accessible and usable. -/

open scoped WeierstrassCurve.Affine

#check @MazurProof.mazur_torsion_bound
#check @MazurProof.full_rational_torsion_order_le_two
#check @MazurProof.rational_torsion_finite

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (MazurProof.torsionSet E).ncard ≤ 20 := by
  have h := (MazurProof.mazur_torsion_bound E).2
  omega
