import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityCenterDistinctness

/-- Equal centers give a common-field-compatible local equivalence. -/
theorem exists_equiv_of_same_center
    {A R S K : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing K]
    [Algebra A R] [Algebra A S]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (eR : Localization.AtPrime p ≃ₐ[A] R)
    (eS : Localization.AtPrime q ≃ₐ[A] S)
    (gR : R →+* K) (gS : S →+* K)
    (hc : ∀ a, gR (algebraMap A R a) = gS (algebraMap A S a)) (hpq : p = q) :
    ∃ e : R ≃ₐ[A] S, ∀ r, gS (e r) = gR r := by
  subst q
  let e := eR.symm.trans eS
  refine ⟨e, ?_⟩
  have hm : gS.comp eS.toRingHom = gR.comp eR.toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change gS (eS (algebraMap A (Localization.AtPrime p) a)) =
      gR (eR (algebraMap A (Localization.AtPrime p) a))
    rw [eS.commutes, eR.commutes]
    exact (hc a).symm
  intro r
  have hr := RingHom.congr_fun hm (eR.symm r)
  simpa [e] using hr

private theorem incompatible_unit_ratio
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    (f : R →+* K) (g : S →+* K) (hf : Function.Injective f)
    (e : R ≃+* S) (he : ∀ r, g (e r) = f r)
    (a b : R) (v : S) (hv : IsUnit v)
    (hab : f a * g v = f b) (hord : Ring.ord R a ≠ Ring.ord R b) : False := by
  let u := e.symm v
  have hu : IsUnit u := hv.map e.symm.toRingHom
  have hfu : f u = g v := by simpa [u] using (he u).symm
  have hrel : a * u = b := by
    apply hf
    rw [map_mul, hfu]
    exact hab
  apply hord
  calc
    Ring.ord R a = Ring.ord R (a * u) := (Ring.ord_mul_of_isUnit_right hu a).symm
    _ = Ring.ord R b := congrArg (Ring.ord R) hrel

example {K : Type*} [Field K] (qx qy qz : K) (hy : qy ≠ 0) :
    (qy / qx) * (qz / qy) = qz / qx := by
  rw [div_mul_div_comm, mul_comm qx qy, mul_div_mul_left _ _ hy]

#print axioms exists_equiv_of_same_center
#print axioms incompatible_unit_ratio
end MazurProof.N25F_InfinityCenterDistinctness
