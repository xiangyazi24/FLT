import FLT.Assumptions.MazurProof.CurveDedekindDivisor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact affine integrality and ideal membership from all genuine Dedekind orders. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_DedekindOrderMembership
open CurveDedekindDivisor

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Nonnegative coefficients force a genuine fractional ideal to be integral. -/
theorem fractionalIdeal_le_one_of_count_nonneg (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) :
    I ≤ 1 := by
  classical
  let d := fractionalIdealDivisor I
  let J : FractionalIdeal R⁰ K := d.prod fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m
  have hJ : J ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have he : I = J := by
    apply fractionalIdealDivisor_injectiveOn_nonzero hI hJ
    ext v
    exact (FractionalIdeal.count_finsuppProd K v d).symm
  rw [he]
  change d.prod (fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m) ≤ 1
  rw [Finsupp.prod]
  apply Finset.prod_le_one'
  intro v hv
  have hd : 0 ≤ d v := hc v
  have hn : d v = ((d v).toNat : ℤ) := (Int.natCast_toNat_eq_self.mpr hd).symm
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

/-- The converse to order monotonicity, proved from actual fractional-ideal factorization. -/
theorem fractionalIdeal_le_of_count_le (I J : FractionalIdeal R⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) : I ≤ J := by
  have hprod : I * J⁻¹ ≤ 1 :=
    fractionalIdeal_le_one_of_count_nonneg _ (mul_ne_zero hI (inv_ne_zero hJ)) (by
      intro v
      rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
      exact sub_nonneg.mpr (hc v))
  have h := mul_le_mul_right' hprod J
  simpa only [mul_assoc, inv_mul_cancel₀ hJ, mul_one, one_mul] using h

/-- All nonnegative affine orders recover a unique real element of the original ring. -/
theorem existsUnique_algebraMap_eq_of_count_nonneg (f : K)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f)) :
    ∃! a : R, algebraMap R K a = f := by
  have hex : ∃ a : R, algebraMap R K a = f := by
    by_cases hf : f = 0
    · exact ⟨0, by rw [map_zero, hf]⟩
    apply (FractionalIdeal.mem_one_iff R⁰).mp
    exact fractionalIdeal_le_one_of_count_nonneg _
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) hc
      (FractionalIdeal.mem_spanSingleton_self R⁰ f)
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, fun b hb => IsFractionRing.injective R K (hb.trans ha.symm)⟩

/-- Membership in a genuine nonzero fractional ideal is exactly the full set of order inequalities. -/
theorem mem_fractionalIdeal_iff_count_le (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (f : K) (hf : f ≠ 0) : f ∈ I ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum R,
        FractionalIdeal.count K v I ≤
          FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f) := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h v
    exact FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) h
  · exact fractionalIdeal_le_of_count_le _ I (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) hI

end MazurProof.N25F_DedekindOrderMembership
