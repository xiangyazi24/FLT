import FLT.Assumptions.MazurProof.N25F_ZChartFractionMap
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

-- Full-module imports make instance search slower than in dot's selective-import check.
set_option synthInstance.maxHeartbeats 200000

/-! The actual coordinate-rigid Z-chart map is injective. A finite image
would force 1/qz to have finite order, contradicted in the established
polynomial coefficient algebra by evaluation of X at zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_ZChartFractionInjective

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

private theorem finite_power_of_not_injective
    {R K : Type*} [CommRing R] [Ring.DimensionLEOne R]
    [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R] [Field K]
    (f : R →+* K) (hf : ¬ Function.Injective f)
    (r : R) (hr : f r ≠ 0) : ∃ n : ℕ, 0 < n ∧ (f r) ^ n = 1 := by
  let m := RingHom.ker f
  have hm : m ≠ ⊥ := by
    intro h
    exact hf ((RingHom.injective_iff_ker_eq_bot f).2 h)
  letI : m.IsMaximal := (RingHom.ker_isPrime f).isMaximal hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite (ZMod 2) (R ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod 2) (R ⧸ m)
  letI : Finite (R ⧸ m) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (R ⧸ m) := Fintype.ofFinite _
  have hbar : Ideal.Quotient.mk m r ≠ 0 := by
    intro h
    apply hr
    simpa only [m, RingHom.kerLift_mk, map_zero] using congrArg (RingHom.kerLift f) h
  refine ⟨Fintype.card (R ⧸ m) - 1, Nat.sub_pos_of_lt Fintype.one_lt_card, ?_⟩
  have hpow := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk m r) hbar
  simpa only [m, map_pow, RingHom.kerLift_mk, map_one] using
    congrArg (RingHom.kerLift f) hpow

/-- No positive power of the actual Z/W coordinate is one. -/
theorem qz_pow_ne_one (n : ℕ) (hn : 0 < n) : (qz : W) ^ n ≠ 1 := by
  intro h
  have hp : (Polynomial.X : Polynomial (ZMod 2)) ^ n = 1 := by
    apply FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) W
    simpa only [map_pow, map_one, algebraMap_Rz_X] using h
  have hzero := congrArg (Polynomial.eval (0 : ZMod 2)) hp
  simpa [Nat.ne_of_gt hn] using hzero

/-- The actual Z-chart transition into the fixed W-chart function field is
injective, with no additional geometric or nonvanishing premise. -/
theorem zChartToFraction_injective : Function.Injective zChartToFraction := by
  by_contra h
  obtain ⟨n, hn, hpow⟩ := finite_power_of_not_injective
    zChartToFraction.toRingHom h zW
    (by simpa using (inv_ne_zero fraction_qz_ne_zero))
  have hfrac : (algebraMap W (FractionRing W) qz) ^ n = 1 := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      zChartToFraction_zW, one_div, inv_pow, inv_eq_one] using hpow
  apply qz_pow_ne_one n hn
  apply IsFractionRing.injective W (FractionRing W)
  simpa only [map_pow, map_one] using hfrac

end MazurProof.N25F_ZChartFractionInjective
