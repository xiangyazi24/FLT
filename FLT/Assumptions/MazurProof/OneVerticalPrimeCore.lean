import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero

/-!
# Divisors supported on one vertical prime

This file isolates the group-theoretic heart of vertical rigidity.  Once
codimension-one coefficients are faithful and the reduced special fibre is
the unique vertical prime, every vertical divisor is an integral multiple
of that fibre.
-/

namespace MazurProof.OneVerticalPrimeCore

structure Data
    (Prime Div : Type*)
    [DecidableEq Prime]
    [AddCommGroup Div] where
  /-- Codimension-one coefficients of a divisor. -/
  toWeil : Div →+ (Prime →₀ ℤ)

  /-- Divisors are determined by their codimension-one coefficients. -/
  toWeil_injective : Function.Injective toWeil

  isVertical : Prime → Prop
  fibrePrime : Prime

  /-- The reduced special fibre as a divisor. -/
  fibre : Div
  toWeil_fibre :
    toWeil fibre = Finsupp.single fibrePrime 1

  /-- The reduced special fibre is the unique vertical prime. -/
  only_vertical :
    ∀ p : Prime, isVertical p → p = fibrePrime

namespace Data

variable {Prime Div : Type*}
variable [DecidableEq Prime]
variable [AddCommGroup Div]
variable (D : Data Prime Div)

/-- A divisor supported on the vertical locus is an integral multiple of
the unique reduced special fibre. -/
theorem eq_zsmul_fibre_of_support_vertical
    (d : Div)
    (hvert :
      ∀ p : Prime,
        D.toWeil d p ≠ 0 → D.isVertical p) :
    ∃ n : ℤ, d = n • D.fibre := by
  let n : ℤ := D.toWeil d D.fibrePrime
  refine ⟨n, D.toWeil_injective ?_⟩
  rw [map_zsmul, D.toWeil_fibre]
  ext p
  rw [Finsupp.smul_apply]
  by_cases hp : p = D.fibrePrime
  · subst p
    simp [n]
  · have hd : D.toWeil d p = 0 := by
      by_contra hne
      exact hp (D.only_vertical p (hvert p hne))
    simp [hd, hp]

end Data

end MazurProof.OneVerticalPrimeCore
