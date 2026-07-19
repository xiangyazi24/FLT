import Mathlib
import FLT.Assumptions.MazurProof.KubertBridgeN16
import FLT.Assumptions.MazurProof.CyclicExclusion16

/-! # N=16 descent bridge

The noncyclic Z/2Z × Z/16Z case is discharged ex falso: the injection
implies a rational point of order 16 (via `point_addOrder16_of_zmod2_zmod16_injection`),
contradicting `no_rational_point_of_order_16` (proved via `X₁(16)` split descent). -/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem no_Z2_cross_Z16_from_descent
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f := by
  rintro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := KubertBridgeN16.point_addOrder16_of_zmod2_zmod16_injection E f hf
  exact no_rational_point_of_order_16 E ⟨P, hP⟩

end MazurProof
