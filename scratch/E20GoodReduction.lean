import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Scratch.E20GoodReduction

def E20_rhs {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 3 + x ^ 2 - x

theorem E20_affine_F3_count :
    (Finset.univ.filter fun p : ZMod 3 × ZMod 3 =>
      p.2 ^ 2 = E20_rhs p.1).card = 5 := by native_decide

theorem E20_affine_F7_count :
    (Finset.univ.filter fun p : ZMod 7 × ZMod 7 =>
      p.2 ^ 2 = E20_rhs p.1).card = 5 := by native_decide

theorem E20_discriminant_good_mod3 :
    ((80 : ZMod 3) ≠ 0) := by native_decide

theorem E20_discriminant_good_mod7 :
    ((80 : ZMod 7) ≠ 0) := by native_decide

theorem E20_discriminant_bad_mod5 :
    ((80 : ZMod 5) = 0) := by native_decide

end Scratch.E20GoodReduction
