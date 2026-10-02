import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option autoImplicit false
noncomputable section

namespace N25YZUnitCheck

variable {R k : Type*} [CommRing R] [Field k]

local instance (f : R →+* k) : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f

theorem evaluation_one_germ_isUnit (f : R →+* k) (y : R) (hy : f y = 1) :
    IsUnit (algebraMap R (Localization.AtPrime (RingHom.ker f)) y) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) y).2
  apply Ideal.mem_primeCompl_iff.mpr
  intro h
  have hzero : f y = 0 := RingHom.mem_ker.mp h
  rw [hy] at hzero
  exact one_ne_zero hzero

#print axioms evaluation_one_germ_isUnit
end N25YZUnitCheck
