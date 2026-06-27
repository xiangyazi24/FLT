import FLT.Assumptions.MazurProof.DescentBridge
import FLT.Assumptions.MazurProof.RationalPointsC20
import FLT.Assumptions.MazurProof.KubertBridgeN10

/-!
# N=10 descent bridge (alternative axiom set)

Reproves `no_Z2_cross_Z10_from_descent` without using the two axioms in
`DescentBridge.lean`:

| Old axiom (DescentBridge)                     | Replaced by (proof + new axiom)                     |
|-----------------------------------------------|-----------------------------------------------------|
| `obstruction_curve_20a4_points_degenerate`    | `RationalPointsC20.obstruction_curve_20a4_from_elementary` |
|                                               |   (depends on axioms `quartic_plus`, `rat_denom_square`)   |
| `Z2xZ10_gives_non_degenerate_E20_point`      | `KubertBridgeN10.bridge_N10`                        |
|                                               |   (depends on axiom `kubert_C10_square`)                   |

Net effect: two opaque axioms are replaced by three narrower, more elementary ones:
  1. `quartic_plus` — infinite descent on a binary quartic (FLT.Four-adjacent)
  2. `rat_denom_square` — p-adic valuation argument for denominator normalization
  3. `kubert_C10_square` — Kubert moduli: Z/2Z x Z/10Z torsion produces a square discriminant
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

theorem no_Z2_cross_Z10_alt
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  rcases KubertBridgeN10.bridge_N10 E hE with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (RationalPointsC20.obstruction_curve_20a4_from_elementary u w hcurve)

end MazurProof
