import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
noncomputable section

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

#print axioms finite_power_of_not_injective
