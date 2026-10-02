import Mathlib.RingTheory.DedekindDomain.Factorization

/-! A genuine nonzero regular function can dominate any finitely supported
signed affine divisor, by membership in its fractional-ideal product. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_DedekindPrincipalMajorant

/-- Construct a real regular function satisfying all signed affine order lower bounds. -/
theorem exists_nonzero_regular_with_count_ge {R K : Type*}
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (D : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    ∃ a : R, ∃ ha : a ≠ 0, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      D v ≤ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) := by
  classical
  let I : FractionalIdeal R⁰ K :=
    D.prod fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m
  have hI : I ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  obtain ⟨a, ha, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  refine ⟨a, ha, ?_⟩
  intro v
  have hmap : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  have hcount := FractionalIdeal.count_mono K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hmap)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr haI)
  have he : FractionalIdeal.count K v I = D v :=
    FractionalIdeal.count_finsuppProd K v D
  rwa [he] at hcount

end MazurProof.N25F_DedekindPrincipalMajorant

#print axioms MazurProof.N25F_DedekindPrincipalMajorant.exists_nonzero_regular_with_count_ge
