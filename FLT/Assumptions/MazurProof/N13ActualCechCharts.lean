import FLT.Assumptions.MazurProof.N13FormalInfinityChart

/-!
# The actual two charts in the N13 formal Čech quotient

The preceding files constructed the genuine affine and formal-infinity
restriction maps.  This file proves that their images are exactly the two
submodules used in the Laurent-series Čech calculation.

The only point requiring care on the affine side is that a Laurent series
bounded both below and above has finite support.  Reversing its exponents
therefore reconstructs an honest polynomial in `x=t⁻¹`.
-/

open Polynomial

namespace MazurProof.N13ActualCechCharts

noncomputable section

open HahnSeries
open scoped PowerSeries LaurentSeries

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalCurveOverlap.R₂

abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent

abbrev Overlap : Type :=
  N13FormalCurveOverlap.Overlap

abbrev IntegralAffineRing : Type :=
  N13FormalCurveOverlap.IntegralAffineRing

/-- Evaluation of one polynomial monomial at `x=t⁻¹`. -/
@[simp] theorem polyAtTInv_monomial
    (k : ℕ) (a : R₂) :
    N13FormalCurveOverlap.polyAtTInv (monomial k a) =
      HahnSeries.single (-(k : ℤ)) a := by
  change
    Polynomial.eval₂ (algebraMap R₂ Laurent)
        (N13FormalCurveOverlap.tPow (-1)) (monomial k a) =
      HahnSeries.single (-(k : ℤ)) a
  rw [Polynomial.eval₂_monomial]
  change
    algebraMap R₂ Laurent a *
        HahnSeries.single (-1) 1 ^ k =
      HahnSeries.single (-(k : ℤ)) a
  rw [HahnSeries.single_pow, HahnSeries.algebraMap_apply']
  simp

/-- Reverse all Laurent coefficients between the order and exponent zero. -/
def polynomialOfAffine (f : Laurent) : R₂[X] :=
  ∑ k ∈ Finset.range (Int.natAbs f.order + 1),
    monomial k (f.coeff (-(k : ℤ)))

theorem polyAtTInv_polynomialOfAffine
    (f : Laurent) :
    N13FormalCurveOverlap.polyAtTInv
        (polynomialOfAffine f) =
      ∑ k ∈ Finset.range (Int.natAbs f.order + 1),
        HahnSeries.single (-(k : ℤ))
          (f.coeff (-(k : ℤ))) := by
  simp [polynomialOfAffine]

/-- Reversing the coefficients is inverse to `x=t⁻¹` on Laurent series
with no positive exponents. -/
theorem polyAtTInv_polynomialOfAffine_eq
    (f : Laurent)
    (hf : ∀ n : ℤ, 0 < n → f.coeff n = 0) :
    N13FormalCurveOverlap.polyAtTInv
        (polynomialOfAffine f) =
      f := by
  rw [polyAtTInv_polynomialOfAffine]
  ext n
  rw [HahnSeries.coeff_sum]
  by_cases hn : 0 < n
  · rw [hf n hn]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [HahnSeries.coeff_single]
    split_ifs with hnk
    · omega
    · rfl
  · have hn0 : n ≤ 0 := by omega
    let k : ℕ := Int.natAbs n
    have hkexp : -(k : ℤ) = n := by
      have hkcast : (k : ℤ) = -n := by
        exact Int.ofNat_natAbs_of_nonpos hn0
      omega
    by_cases hcoeff : f.coeff n = 0
    · rw [hcoeff]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [HahnSeries.coeff_single]
      split_ifs with hnj
      · have : -(j : ℤ) = n := hnj.symm
        rw [this, hcoeff]
      · rfl
    · have horder : f.order ≤ n :=
        HahnSeries.order_le_of_coeff_ne_zero hcoeff
      have horder0 : f.order ≤ 0 := horder.trans hn0
      have hkBound :
          k < Int.natAbs f.order + 1 := by
        have hkcast : (k : ℤ) = -n := by
          exact Int.ofNat_natAbs_of_nonpos hn0
        have horderCast :
            ((Int.natAbs f.order : ℕ) : ℤ) =
              -f.order := by
          exact Int.ofNat_natAbs_of_nonpos horder0
        have hkLe : k ≤ Int.natAbs f.order := by
          exact_mod_cast
            (show (k : ℤ) ≤
                (Int.natAbs f.order : ℤ) by omega)
        omega
      rw [Finset.sum_eq_single k]
      · simp [hkexp]
      · intro j hj hjk
        simp only [HahnSeries.coeff_single]
        split_ifs with hnj
        · have hjexp : -(j : ℤ) = n := hnj.symm
          have : j = k := by
            exact_mod_cast
              (show (j : ℤ) = (k : ℤ) by omega)
          exact (hjk this).elim
        · rfl
      · simp [hkBound]

/-- Every abstract affine-section pair comes from an actual function of the
integral affine coordinate ring. -/
theorem exists_affine_preimage
    (z : Overlap)
    (hz :
      z ∈ N13CechLaurentSeriesCore.affineSections (R := R₂)) :
    ∃ w : IntegralAffineRing,
      N13FormalCurveOverlap.affineOverlap w = z := by
  let p : R₂[X] := polynomialOfAffine z.1
  let shifted : Laurent :=
    HahnSeries.single 3 1 * z.2
  let q : R₂[X] :=
    polynomialOfAffine shifted
  let w : IntegralAffineRing :=
    N13GeneralizedMumfordIntegral.xClass p +
      N13GeneralizedMumfordIntegral.xClass q *
        N13GeneralizedMumfordIntegral.yClass
  have hshift :
      ∀ n : ℤ, 0 < n → shifted.coeff n = 0 := by
    intro n hn
    rw [HahnSeries.coeff_single_mul]
    simp only [one_mul]
    exact hz.2 (n - 3) (by omega)
  have hp :
      N13FormalCurveOverlap.polyAtTInv p = z.1 :=
    polyAtTInv_polynomialOfAffine_eq z.1 hz.1
  have hq :
      N13FormalCurveOverlap.polyAtTInv q = shifted :=
    polyAtTInv_polynomialOfAffine_eq shifted hshift
  have hshift_cancel :
      shifted * N13FormalCurveOverlap.tPow (-3) = z.2 := by
    dsimp [shifted]
    calc
      (HahnSeries.single 3 1 * z.2) *
          N13FormalCurveOverlap.tPow (-3) =
          (HahnSeries.single 3 1 *
              N13FormalCurveOverlap.tPow (-3)) * z.2 := by
            ac_rfl
      _ = z.2 := by
        simp [N13FormalCurveOverlap.tPow]
  refine ⟨w, ?_⟩
  simp only [w, N13FormalCurveOverlap.affineOverlap_add,
    N13FormalCurveOverlap.affineOverlap_mul,
    N13FormalCurveOverlap.affineOverlap_xClass,
    N13FormalCurveOverlap.affineOverlap_yClass,
    N13FormalLineBundleCech.mulOverlap]
  rw [hp, hq]
  apply Prod.ext
  · simp
  · simp [hshift_cancel]

/-- The actual affine chart has exactly the restriction image used in the
Čech quotient. -/
theorem range_affineOverlap :
    Set.range N13FormalCurveOverlap.affineOverlap =
      N13CechLaurentSeriesCore.affineSections (R := R₂) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact N13FormalCurveOverlap.affineOverlap_mem_affineSections w
  · intro hz
    exact exists_affine_preimage z hz

end

end MazurProof.N13ActualCechCharts
