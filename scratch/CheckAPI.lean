import Mathlib

variable {H : Type*} [AddCommGroup H]

example (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl
