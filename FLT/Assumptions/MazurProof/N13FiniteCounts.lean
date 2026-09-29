import FLT.Assumptions.MazurProof.N13ArithmeticBasics
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

open MazurProof.N13Arithmetic

namespace MazurProof.N13Arithmetic

/-- All four affine pairs over F₂ satisfy the generalized equation.
The finite universal quantifiers are checked by ordinary `decide`. -/
theorem optEquation13_zmod2_all :
    ∀ u v : ZMod 2, OptEquation13 u v := by
  change ∀ u v : ZMod 2,
    v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v = u ^ 2 + u
  decide

/-- Forgetting the equation proof loses no affine points over F₂. -/
def affineC2Equiv :
    {uv : ZMod 2 × ZMod 2 // OptEquation13 uv.1 uv.2} ≃
      (ZMod 2 × ZMod 2) where
  toFun := Subtype.val
  invFun uv := ⟨uv, optEquation13_zmod2_all uv.1 uv.2⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv uv := rfl

/-- The characteristic-two point type from the implementation contract. -/
abbrev C2 := OptPoint13 (ZMod 2)

/-- The four affine pairs and the two infinity tags, without identifying
any affine point or either infinity tag with another point. -/
def c2EquivPairsAndInfinity :
    C2 ≃ ((ZMod 2 × ZMod 2) ⊕ Bool) :=
  Equiv.sumCongr affineC2Equiv (Equiv.refl Bool)

/-- C01: the generalized projective point model has six F₂-points. -/
theorem card_C2 : Nat.card (OptPoint13 (ZMod 2)) = 6 := by
  calc
    Nat.card (OptPoint13 (ZMod 2)) = Nat.card ((ZMod 2 × ZMod 2) ⊕ Bool) :=
      Nat.card_congr c2EquivPairsAndInfinity
    _ = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide

end MazurProof.N13Arithmetic
