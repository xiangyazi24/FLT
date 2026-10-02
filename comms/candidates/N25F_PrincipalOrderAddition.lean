import FLT.Assumptions.MazurProof.N25F_PrincipalDivisorCoefficient
import FLT.Assumptions.MazurProof.N25F_LocalFractionFactorOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! Addition inequalities for the genuine signed local orders and affine
fractional-ideal coefficients used by the existing principal divisor. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_PrincipalOrderAddition
open N25F_LocalFractionFactorOrder

/-- Signed DVR orders satisfy the minimum inequality when all three functions
are nonzero. This is the additive closure input for bounded-pole spaces. -/
theorem log_ordFrac_add_ge_min {R L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (hs : x + y ≠ 0) :
    min (WithZero.log (Ring.ordFrac R x)) (WithZero.log (Ring.ordFrac R y)) ≤
      WithZero.log (Ring.ordFrac R (x + y)) := by
  have hxv : Ring.ordFrac R x ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hx).map (Ring.ordFrac R)).ne_zero
  have hyv : Ring.ordFrac R y ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hy).map (Ring.ordFrac R)).ne_zero
  have hsv : Ring.ordFrac R (x + y) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hs).map (Ring.ordFrac R)).ne_zero
  have h := Ring.ordFrac_add (R := R) x y hs
  by_cases hxy : Ring.ordFrac R x ≤ Ring.ordFrac R y
  · rw [min_eq_left hxy] at h
    exact (min_le_left _ _).trans ((WithZero.log_le_log hxv hsv).mpr h)
  · rw [min_eq_right (le_of_not_ge hxy)] at h
    exact (min_le_right _ _).trans ((WithZero.log_le_log hyv hsv).mpr h)

/-- The actual fractional-ideal count agrees with the genuine signed length
order on the canonical fraction field, at every height-one prime. -/
theorem count_spanSingleton_eq_log_ordFrac {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) (z : FractionRing R) (hz : z ≠ 0) :
    FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ z) =
      WithZero.log (Ring.ordFrac (Localization.AtPrime v.asIdeal) z) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div, ne_eq, not_true_eq_false] at hz
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hna : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr ha
  have hnb : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb'
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul (FractionRing R) v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hna)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hnb)),
    FractionalIdeal.count_inv,
    DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors (FractionRing R) a ha v,
    DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors (FractionRing R) b hb' v]
  simpa only [div_eq_mul_inv, sub_eq_add_neg] using
    (log_ordFrac_atPrime_div v.asIdeal v.ne_bot a b ha hb').symm

/-- Addition has the same minimum inequality for the exact fractional-ideal
coefficients used by the existing affine principal-divisor definition. -/
theorem count_spanSingleton_add_ge_min {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) (x y : FractionRing R)
    (hx : x ≠ 0) (hy : y ≠ 0) (hs : x + y ≠ 0) :
    min (FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ x))
        (FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ y)) ≤
      FractionalIdeal.count (FractionRing R) v (FractionalIdeal.spanSingleton R⁰ (x + y)) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
      (Localization.AtPrime v.asIdeal)
  rw [count_spanSingleton_eq_log_ordFrac v x hx,
    count_spanSingleton_eq_log_ordFrac v y hy,
    count_spanSingleton_eq_log_ordFrac v (x + y) hs]
  exact log_ordFrac_add_ge_min x y hx hy hs

end MazurProof.N25F_PrincipalOrderAddition
