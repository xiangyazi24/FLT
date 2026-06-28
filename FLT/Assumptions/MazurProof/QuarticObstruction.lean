import Mathlib
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.DescentBridge
import FLT.Assumptions.MazurProof.DescentBridgeN12
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16

/-! # Axiom 4 Assembly — Noncyclic Exclusions

Assembly of the four noncyclic exclusions for Axiom 4:
  ¬ (ℤ/2 × ℤ/n ↪ E(ℚ)_tors)  for n ∈ {10, 12, 14, 16}.

Each case is proved via a separate descent bridge:

- **N=10**: Kubert parametrization → obstruction curve w²=u³+u²-u
  (KubertBridgeN10.lean → DescentBridge.lean).
  The quartic family s⁴+d²s²-d⁴=t² (d=2..7, in scratch/QuarticD*.lean) ALL
  reduce to this same obstruction curve via u=(s/d)², w=st/d³.
  They are auxiliary support for N=10 only, not separate N-values.

- **N=12**: Separate Kubert family with its own obstruction curve
  w²=u³-u²-4u+4 (KubertBridgeN12.lean → DescentBridgeN12.lean).

- **N=14**: Direct obstruction-point axioms (DescentBridgeN14.lean).
  No genus-0 Kubert family; bridge uses obstruction curve w²=u³+u²-2u.

- **N=16**: Direct obstruction-point axioms (DescentBridgeN16.lean).
  No genus-0 Kubert family; bridge uses obstruction curve w²=u³-u²-u.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Individual case re-exports

Each theorem delegates to the corresponding descent bridge. -/

theorem noncyclic_Z2xZ10 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z10_from_descent E

theorem noncyclic_Z2xZ12 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z12_from_descent E

theorem noncyclic_Z2xZ14 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z14_from_descent E

theorem noncyclic_Z2xZ16 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 16 →+ (E⁄ℚ).Point, Function.Injective f :=
  no_Z2_cross_Z16_from_descent E

/-! ## Axiom 4 assembly -/

/-- Axiom 4: no elliptic curve over ℚ has ℤ/2 × ℤ/n torsion for n ∈ {10,12,14,16}. -/
theorem quartic_d_supports_axiom_4 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16) :
    ¬ ∃ f : ZMod 2 × ZMod n →+ (E⁄ℚ).Point, Function.Injective f := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact noncyclic_Z2xZ10 E
  · exact noncyclic_Z2xZ12 E
  · exact noncyclic_Z2xZ14 E
  · exact noncyclic_Z2xZ16 E

end MazurProof
