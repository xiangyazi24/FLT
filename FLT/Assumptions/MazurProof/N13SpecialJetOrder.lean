import FLT.Assumptions.MazurProof.N13SpecialFiniteBranchJets

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

A certified nonzero nine-jet determines the actual Laurent order of a power
series. This links the finite polynomial certificate to the actual Hensel
roots, rather than treating a finite Taylor computation as a divisor proof.
-/

namespace MazurProof.N13SpecialJetOrder

noncomputable section
open Polynomial N13SpecialInfinityBranchJets
open N13SpecialLaurentBranches hiding K P
open scoped LaurentSeries

theorem coeff_eq_of_jet_congruence (r : P) (s : K[X]) (n : ℕ)
    (h : (PowerSeries.X : P) ^ n ∣ r - beta s) (j : ℕ) (hj : j < n) :
    PowerSeries.coeff j r = s.coeff j := by
  have hh := PowerSeries.X_pow_dvd_iff.mp h j hj
  rw [map_sub, beta_eq_coe, Polynomial.coeff_coe] at hh
  exact sub_eq_zero.mp hh

theorem order_eq_of_certified_jet (r : P) (s : K[X]) (n k : ℕ)
    (hk : k < n) (hcoeff : s.coeff k ≠ 0)
    (hlow : ∀ j : ℕ, j < k → s.coeff j = 0)
    (hjet : (PowerSeries.X : P) ^ n ∣ r - beta s) :
    (includeSeries r).order = (k : ℤ) := by
  have hkr : PowerSeries.coeff k r ≠ 0 := by
    rwa [coeff_eq_of_jet_congruence r s n hjet k hk]
  have hr : r ≠ 0 := by
    intro h
    apply hkr
    simp [h]
  have hinc : includeSeries r ≠ 0 := by
    have hne := (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)).ne hr
    rw [map_zero] at hne
    exact hne
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    change (HahnSeries.ofPowerSeries ℤ K r).coeff (k : ℤ) ≠ 0
    rwa [HahnSeries.ofPowerSeries_apply_coeff]
  · rw [HahnSeries.le_order_iff_forall hinc]
    intro j hj
    change ((r : LaurentSeries K).coeff j) = 0
    rw [PowerSeries.coeff_coe]
    split_ifs with hneg
    · rfl
    · have hj0 : 0 ≤ j := le_of_not_gt hneg
      have hjabs : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
      have hjk : j.natAbs < k := by omega
      rw [coeff_eq_of_jet_congruence r s n hjet j.natAbs (lt_trans hjk hk)]
      exact hlow _ hjk

end
end MazurProof.N13SpecialJetOrder
