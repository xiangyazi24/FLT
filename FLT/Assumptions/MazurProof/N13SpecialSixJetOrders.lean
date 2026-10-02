import FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator
import FLT.Assumptions.MazurProof.N13SpecialJetOrder

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Identify the finite certificate's six nonzero jets with actual local orders
of the same cleared numerator. The two infinity orders have the common -4
shift from the literal reciprocal numerator identity.
-/

namespace MazurProof.N13SpecialSixJetOrders

noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K plus minus
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P

def function (a : Fin 5 → K) (b : Fin 2 → K) : R :=
  N13SpecialAffineNorm.linear (numerator a) (ordinate b)

def sixSeries (a : Fin 5 → K) (b : Fin 2 → K) : Fin 6 → P := ![
  branchZero 0 (function a b), branchOne 0 (function a b),
  branchZero 1 (function a b), branchOne 1 (function a b),
  beta (infinityNumerator a) + beta (infinityOrdinate b) * r₀,
  beta (infinityNumerator a) + beta (infinityOrdinate b) * r₁]

private theorem linear_jet (p q s : K[X]) (r : P)
    (h : (PowerSeries.X : P) ^ 9 ∣ r - beta s) :
    (PowerSeries.X : P) ^ 9 ∣ (beta p + beta q * r) - beta (p + q * s) := by
  have hh := dvd_mul_of_dvd_right h (beta q)
  convert hh using 1 <;> simp only [map_add, map_mul] <;> ring

private theorem evalBase_zero (p : K[X]) : evalBase 0 p = beta p := by
  rw [← beta_comp]
  simp

private theorem evalBase_one (p : K[X]) : evalBase 1 p = beta (p.comp (X + 1)) := by
  rw [← beta_comp]
  simp

theorem six_series_jet_congruence (a : Fin 5 → K) (b : Fin 2 → K) (i : Fin 6) :
    (PowerSeries.X : P) ^ 9 ∣ sixSeries a b i - beta (sixJetPolynomials a b i) := by
  fin_cases i
  · change (PowerSeries.X : P) ^ 9 ∣ branchZero 0 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchZero_xClass, branchZero_yClass, evalBase_zero]
    exact linear_jet _ _ _ _ zero_zero_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchOne 0 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchOne_xClass, branchOne_yClass, evalBase_zero]
    exact linear_jet _ _ _ _ zero_one_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchZero 1 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchZero_xClass, branchZero_yClass, evalBase_one]
    exact linear_jet _ _ _ _ one_zero_jet
  · change (PowerSeries.X : P) ^ 9 ∣ branchOne 1 (function a b) - _
    simp only [function, N13SpecialAffineNorm.linear, map_add, map_mul,
      branchOne_xClass, branchOne_yClass, evalBase_one]
    exact linear_jet _ _ _ _ one_one_jet
  · exact N13SpecialRootJetAgreement.infinity_numerator_zero_jet _ _
  · exact N13SpecialRootJetAgreement.infinity_numerator_one_jet _ _

theorem six_series_orders (a : Fin 5 → K) (b : Fin 2 → K)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (i : Fin 6) : (includeSeries (sixSeries a b i)).order = (sixJetOrders a b i : ℤ) := by
  apply N13SpecialJetOrder.order_eq_of_certified_jet _ _ 9 _
    (hjets i).1 (hjets i).2.1 _ (six_series_jet_congruence a b i)
  intro j hj
  exact (hjets i).2.2 ⟨j, lt_trans hj (hjets i).1⟩ hj

private theorem include_beta (p : K[X]) :
    includeSeries (beta p) = p.eval₂ (algebraMap K L) t := by
  rw [beta_eq_coe]
  exact (N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries K p).symm

/-- The precise reciprocal change of coordinates, including t^4. -/
theorem reciprocal_numerator_identity (a : Fin 5 → K) (b : Fin 2 → K) (r : P) :
    t ^ 4 * (base (numerator a) + base (ordinate b) * (t⁻¹ ^ 3 * includeSeries r)) =
      includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r) := by
  rw [map_add, map_mul, include_beta, include_beta]
  have hb : base = Polynomial.eval₂RingHom (algebraMap K L) t⁻¹ := rfl
  have hu : t * t⁻¹ = 1 := mul_inv_cancel₀ t_ne_zero
  rw [hb]
  generalize t⁻¹ = u at hu ⊢
  generalize t = s at hu ⊢
  simp only [numerator, ordinate, infinityNumerator, infinityOrdinate,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_finsetSum, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow,
    Fin.sum_univ_five]
  norm_num
  linear_combination (algebraMap K L (a 1) * s ^ 3 + algebraMap K L (a 2) * s ^ 2 * (s * u + 1) +
    algebraMap K L (a 3) * s * (s ^ 2 * u ^ 2 + s * u + 1) +
    (algebraMap K L (a 4) + algebraMap K L (b 1) * includeSeries r) *
      (s ^ 3 * u ^ 3 + s ^ 2 * u ^ 2 + s * u + 1) +
    algebraMap K L (b 0) * includeSeries r * s * (s ^ 2 * u ^ 2 + s * u + 1)) * hu

def sixOrders (z : R) : Fin 6 → ℤ := ![
  (includeSeries (branchZero 0 z)).order, (includeSeries (branchOne 0 z)).order,
  (includeSeries (branchZero 1 z)).order, (includeSeries (branchOne 1 z)).order,
  (plus z).order, (minus z).order]

theorem six_orders_of_jets (a : Fin 5 → K) (b : Fin 2 → K)
    (hn : function a b ≠ 0)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (i : Fin 6) : sixOrders (function a b) i =
      (sixJetOrders a b i : ℤ) - (if (i : ℕ) < 4 then 0 else 4) := by
  have ho := six_series_orders a b hjets
  fin_cases i
  · simpa [sixOrders, sixSeries] using ho 0
  · simpa [sixOrders, sixSeries] using ho 1
  · simpa [sixOrders, sixSeries] using ho 2
  · simpa [sixOrders, sixSeries] using ho 3
  · have hr : t ^ 4 * plus (function a b) = includeSeries (sixSeries a b 4) := by
      change _ = includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r₀)
      simpa only [function, N13SpecialAffineNorm.linear, map_add, map_mul, plus_xClass, plus_yClass]
        using reciprocal_numerator_identity a b r₀
    have horder := congrArg HahnSeries.order hr
    rw [HahnSeries.order_mul (pow_ne_zero 4 t_ne_zero) (plus_ne_zero _ hn),
      HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter, ho] at horder
    change (plus (function a b)).order = (sixJetOrders a b 4 : ℤ) - 4
    norm_num at horder
    omega
  · have hr : t ^ 4 * minus (function a b) = includeSeries (sixSeries a b 5) := by
      change _ = includeSeries (beta (infinityNumerator a) + beta (infinityOrdinate b) * r₁)
      simpa only [function, N13SpecialAffineNorm.linear, map_add, map_mul, minus_xClass, minus_yClass]
        using reciprocal_numerator_identity a b r₁
    have horder := congrArg HahnSeries.order hr
    rw [HahnSeries.order_mul (pow_ne_zero 4 t_ne_zero) (minus_ne_zero _ hn),
      HahnSeries.order_pow, N13LaurentPolynomialOrder.order_parameter, ho] at horder
    change (minus (function a b)).order = (sixJetOrders a b 5 : ℤ) - 4
    norm_num at horder
    omega

def weightedLocalCode (z : R) : ZMod 19 :=
  (sixOrders z 0 : ZMod 19) - sixOrders z 1 +
    7 * (sixOrders z 2 : ZMod 19) - 7 * sixOrders z 3 +
    8 * (sixOrders z 4 : ZMod 19) - 8 * sixOrders z 5

theorem weightedLocalCode_of_certified_jets (a : Fin 5 → K) (b : Fin 2 → K)
    (hn : function a b ≠ 0)
    (hjets : ∀ i : Fin 6, sixJetOrders a b i < 9 ∧
      (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
      ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0)
    (hcode : weightedJetCode a b = 0) : weightedLocalCode (function a b) = 0 := by
  unfold weightedLocalCode
  simp only [six_orders_of_jets a b hn hjets]
  norm_num
  unfold weightedJetCode at hcode
  linear_combination hcode

end
end MazurProof.N13SpecialSixJetOrders
