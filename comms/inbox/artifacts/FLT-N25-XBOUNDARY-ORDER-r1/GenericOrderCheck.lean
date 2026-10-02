import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
noncomputable section
open WithZero

namespace N25BoundaryOrderCheck

variable {R K : Type*} [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Field K] [Algebra R K] [IsFractionRing R K]

def orderOnUnits : Additive Kˣ →+ ℤ where
  toFun f := WithZero.log (Ring.ordFrac R (f.toMul : K))
  map_zero' := by change WithZero.log (Ring.ordFrac R (1 : K)) = 0; simp
  map_add' f g := by
    change WithZero.log (Ring.ordFrac R ((f.toMul : K) * (g.toMul : K))) = _
    rw [map_mul]
    exact WithZero.log_mul
      ((Units.isUnit f.toMul).map (Ring.ordFrac R)).ne_zero
      ((Units.isUnit g.toMul).map (Ring.ordFrac R)).ne_zero

/-- The log of the genuine fraction-field order takes the inverse of a
nonzero germ of order n to -n. -/
theorem log_ordFrac_inverse (a : R) (ha : a ≠ 0) (n : ℕ)
    (hord : Ring.ord R a = n) :
    WithZero.log (Ring.ordFrac R ((algebraMap R K a)⁻¹)) = -(n : ℤ) := by
  rw [map_inv₀, WithZero.log_inv, Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hord]
  rfl

#print axioms orderOnUnits
#print axioms log_ordFrac_inverse
end N25BoundaryOrderCheck
