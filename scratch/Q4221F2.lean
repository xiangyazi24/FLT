import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

def E02 : WeierstrassCurve.Affine (ZMod 2) where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -5
  a₆ := 2

instance : E02.IsElliptic where
  isUnit := by
    rw [isUnit_iff_ne_zero]
    native_decide

example (P : E02.Point) : (4 : ℕ) • P = 0 := by
  native_decide

end N15FormalBackup
