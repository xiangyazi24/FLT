import Mathlib.RingTheory.Valuation.ValuationRing

/-! A local map from a valuation ring to a ring embedded in the same
fraction field is an isomorphism. This is the local comparison needed
after forming the centers of the actual boundary rings. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_LocalValuationRigidity

variable {R S K : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing S] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Domination in the same fraction field forces equality with a valuation ring. -/
theorem bijective_of_local_same_fraction_field
    (f : R →+* S) (g : S →+* K) [IsLocalHom f]
    (hg : Function.Injective g) (hcomp : g.comp f = algebraMap R K) :
    Function.Bijective f := by
  have hmap (r : R) : g (f r) = algebraMap R K r := RingHom.congr_fun hcomp r
  constructor
  · intro a b hab
    apply IsFractionRing.injective R K
    rw [← hmap, ← hmap, hab]
  · intro s
    by_cases hs : s = 0
    · exact ⟨0, by simp [hs]⟩
    have hgs : g s ≠ 0 := by
      intro h
      apply hs
      apply hg
      simpa using h
    rcases ValuationRing.isInteger_or_isInteger R (g s) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, hg ((hmap r).trans hr)⟩
    · have hprod : f r * s = 1 := by
        apply hg
        rw [map_mul, map_one, hmap, hr, inv_mul_cancel₀ hgs]
      have hur : IsUnit r := IsUnit.of_map f r (isUnit_iff_exists_inv.mpr ⟨s, hprod⟩)
      obtain ⟨u, hu⟩ := hur
      refine ⟨↑u⁻¹, hg ?_⟩
      change (g.comp f) (↑u⁻¹ : R) = g s
      rw [hcomp, map_units_inv, hu, hr, inv_inv]

end MazurProof.N25F_LocalValuationRigidity

#print axioms MazurProof.N25F_LocalValuationRigidity.bijective_of_local_same_fraction_field
