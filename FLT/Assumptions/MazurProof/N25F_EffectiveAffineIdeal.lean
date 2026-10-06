import FLT.Assumptions.MazurProof.N25F_DedekindOrderMembership

/-! Genuine integral ideals realizing every effective affine divisor. -/
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_EffectiveAffineIdeal
open N25F_DedekindOrderMembership CurveDedekindDivisor
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every finite nonnegative order vector is the exact vector of one nonzero integral ideal. -/
theorem exists_ideal_with_exact_counts
    (d : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) (hd : ∀ v, 0 ≤ d v) :
    ∃ I : Ideal R, I ≠ ⊥ ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = d v := by
  classical
  let J : FractionalIdeal R⁰ K := d.prod fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m
  have hJ : J ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count K v J = d v :=
    fun v => FractionalIdeal.count_finsuppProd K v d
  have hle : J ≤ 1 := fractionalIdeal_le_one_of_count_nonneg J hJ (by
    intro v
    rw [hcount]
    exact hd v)
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨I, ?_, ?_⟩
  · apply (FractionalIdeal.coeIdeal_ne_zero (K := K)).mp
    rwa [hI]
  · intro v
    rw [hI]
    exact hcount v

/-- The ideal is uniquely determined by these exact orders, not just a majorant. -/
theorem ideal_eq_of_exact_counts (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)) : I = J := by
  apply FractionalIdeal.coeIdeal_injective (R := R) (K := K)
  apply fractionalIdealDivisor_injectiveOn_nonzero
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)
  ext v
  exact h v

/-- Nonpositive signed affine coefficients give precisely the required vanishing ideal. -/
theorem exists_ideal_for_nonpositive_divisor
    (d : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) (hd : ∀ v, d v ≤ 0) :
    ∃ I : Ideal R, I ≠ ⊥ ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum R,
        FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = -d v) ∧
      ∀ f : K, f ∈ (I : FractionalIdeal R⁰ K) ↔
        f = 0 ∨ ∀ v : IsDedekindDomain.HeightOneSpectrum R,
          0 ≤ d v + FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f) := by
  obtain ⟨I, hI, hc⟩ := exists_ideal_with_exact_counts (K := K) (-d) (by
    intro v
    simpa only [Finsupp.neg_apply] using neg_nonneg.mpr (hd v))
  refine ⟨I, hI, hc, ?_⟩
  intro f
  by_cases hf : f = 0
  · simp [hf]
  rw [or_iff_right hf, mem_fractionalIdeal_iff_count_le _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI) f hf]
  simp only [hc, Finsupp.neg_apply]
  constructor <;> intro h v <;> have hv := h v <;> omega

end MazurProof.N25F_EffectiveAffineIdeal
