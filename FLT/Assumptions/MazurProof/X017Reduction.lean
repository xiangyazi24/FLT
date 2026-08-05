import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Small good-reduction point counts for `X₀(17)`

The integral equation

`y² + xy + y = x³ - x² - x - 14`

has three affine points over both `𝔽₂` and `𝔽₃`.  Adding the unique point at
infinity gives four points on each projective fibre.  These tiny
kernel-checked computations are the finite targets needed by a future
prime-to-prime torsion-reduction argument.
-/

namespace MazurProof.X017Reduction

/-- The integral `X₀(17)` equation, written over a general commutative ring so
the same formula can be evaluated in the two good residue fields. -/
def equation17 {R : Type*} [CommRing R] (x y : R) : Prop :=
  y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14

/-- The affine points of the integral model over `𝔽₂`. -/
def affineF2 : Finset (ZMod 2 × ZMod 2) :=
  Finset.univ.filter fun p =>
    p.2 ^ 2 + p.1 * p.2 + p.2 =
      p.1 ^ 3 - p.1 ^ 2 - p.1 - 14

/-- The affine points of the integral model over `𝔽₃`. -/
def affineF3 : Finset (ZMod 3 × ZMod 3) :=
  Finset.univ.filter fun p =>
    p.2 ^ 2 + p.1 * p.2 + p.2 =
      p.1 ^ 3 - p.1 ^ 2 - p.1 - 14

/-- Membership in the enumerated mod-two set is exactly the integral curve
equation, not a separate Boolean approximation. -/
@[simp] theorem mem_affineF2_iff (p : ZMod 2 × ZMod 2) :
    p ∈ affineF2 ↔ equation17 p.1 p.2 := by
  simp [affineF2, equation17]

/-- Membership in the enumerated mod-three set is exactly the same curve
equation reduced modulo three. -/
@[simp] theorem mem_affineF3_iff (p : ZMod 3 × ZMod 3) :
    p ∈ affineF3 ↔ equation17 p.1 p.2 := by
  simp [affineF3, equation17]

/-- There are exactly three affine points on the reduction modulo two. -/
theorem affineF2_card : affineF2.card = 3 := by
  decide

/-- There are exactly three affine points on the reduction modulo three. -/
theorem affineF3_card : affineF3.card = 3 := by
  decide

/-- The discriminant factor `17⁴` remains nonzero modulo two, so the fibre
used by the point count is a good reduction of the characteristic-zero
curve. -/
theorem delta_nonzero_mod2 : ((17 : ZMod 2) ^ 4 ≠ 0) := by
  decide

/-- The discriminant factor `17⁴` remains nonzero modulo three. -/
theorem delta_nonzero_mod3 : ((17 : ZMod 3) ^ 4 ≠ 0) := by
  decide

end MazurProof.X017Reduction
