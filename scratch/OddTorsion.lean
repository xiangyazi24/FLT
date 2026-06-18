import Mathlib
import FLT.Assumptions.MazurProof.TorsionBound

open MazurProof

theorem no_full_odd_prime_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hemb : HasFullRationalTorsion E p) : False := by
  have hle := full_rational_torsion_order_le_two E hp.pos hemb
  omega

