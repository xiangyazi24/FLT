import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NormNum
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25InfinityBaseCheck

variable {k R K : Type*} [Field k] [CommRing R] [Field K]
  [Algebra k R] [Algebra k K]

theorem inverse_germ_image (j : R →ₐ[k] K) (u : Rˣ) (w : R) (y z : K)
    (hy : y ≠ 0) (hu : j (u : R) = z / y) (hw : j w = 1 / y) :
    j (w * (↑u⁻¹ : R)) = 1 / z := by
  rw [map_mul, map_units_inv, hu, hw, inv_div, one_div,
    ← mul_div_assoc, inv_mul_cancel₀ hy]

theorem inverse_germ_ord (u : Rˣ) (w : R) (n : ℕ)
    (hw : Ring.ord R w = n) : Ring.ord R (w * (↑u⁻¹ : R)) = n := by
  rw [Ring.ord_mul_of_isUnit_right (Units.isUnit (u⁻¹)), hw]

theorem aeval_comp_map (j : R →ₐ[k] K) (r : R) (z : K) (hr : j r = z) :
    j.comp (Polynomial.aeval r) = Polynomial.aeval z := by
  rw [← Polynomial.aeval_algHom, hr]

theorem inverse_aeval_injective (z : K)
    (hz : Function.Injective (Polynomial.aeval z : Polynomial k →ₐ[k] K)) :
    Function.Injective (Polynomial.aeval (1 / z) : Polynomial k →ₐ[k] K) := by
  apply transcendental_iff_injective.mp
  have ht : Transcendental k z := transcendental_iff_injective.mpr hz
  simpa only [one_div, Transcendental, IsAlgebraic.inv_iff] using ht

#print axioms inverse_germ_image
#print axioms inverse_germ_ord
#print axioms aeval_comp_map
#print axioms inverse_aeval_injective
end N25InfinityBaseCheck
