import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic

set_option autoImplicit false
noncomputable section

namespace N25LocalEmbeddingCheck

variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra k K]
  (p : Ideal R) [p.IsPrime]
  (f : R →ₐ[k] K) (hf : Function.Injective f)

include hf
private theorem primeCompl_isUnit (s : p.primeCompl) : IsUnit (f (s : R)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hs : (s : R) = 0 := hf (h.trans (map_zero f).symm)
  exact (Ideal.mem_primeCompl_iff.mp s.2) (hs ▸ p.zero_mem)

def localToField : Localization.AtPrime p →ₐ[k] K :=
  IsLocalization.liftAlgHom
    (A := k) (R := R) (S := Localization.AtPrime p)
    (P := K) (f := f) (primeCompl_isUnit p f hf)

@[simp] theorem localToField_algebraMap (a : R) :
    localToField p f hf (algebraMap R (Localization.AtPrime p) a) = f a := by
  exact IsLocalization.lift_eq (primeCompl_isUnit p f hf) a

theorem localToField_injective : Function.Injective (localToField p f hf) := by
  change Function.Injective
    (IsLocalization.lift (S := Localization.AtPrime p)
      (g := f.toRingHom) (primeCompl_isUnit p f hf))
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    simpa using congrArg (localToField p f hf) h
  · intro h
    exact congrArg (algebraMap R (Localization.AtPrime p)) (hf h)

#print axioms localToField_injective
end N25LocalEmbeddingCheck
