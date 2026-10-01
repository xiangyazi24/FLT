import FLT.Assumptions.MazurProof.N13SpecialSmallFunctionCertificate

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

An approximate root with the prescribed constant term agrees with the
actual characteristic-two Hensel root through the certified jet precision.
The difference factor is a unit because its constant term is1. Apply this
to the two actual infinity roots and the explicit nine-jet polynomials.
-/

namespace MazurProof.N13SpecialRootJetAgreement

noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets

theorem root_jet_agreement (H R s : K[X]) (r : P) (n : ℕ)
    (hH : H.coeff 0 = 1)
    (hconstant : PowerSeries.constantCoeff r = s.coeff 0)
    (hr : r ^ 2 + beta H * r - beta R = 0)
    (hs : (X : K[X]) ^ n ∣ residual H R s) :
    (PowerSeries.X : P) ^ n ∣ r - beta s := by
  have hc (p : K[X]) : PowerSeries.constantCoeff (beta p) = p.coeff 0 := by
    rw [beta_eq_coe, ← PowerSeries.coeff_zero_eq_constantCoeff]
    exact Polynomial.coeff_coe p 0
  have hu : IsUnit (r + beta s + beta H) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_add, hconstant, hc, hc, hH]
    have htwo : s.coeff 0 + s.coeff 0 = 0 := by
      simpa only [two_mul, zero_mul] using
        congrArg (fun a : K => a * s.coeff 0) (show (2 : K) = 0 by decide)
    rw [htwo, zero_add]
    exact isUnit_one
  have hd : (PowerSeries.X : P) ^ n ∣ beta (residual H R s) := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨beta w, ?_⟩
    rw [hw, map_mul, map_pow]
    simp [beta]
  have he : (r - beta s) * (r + beta s + beta H) = -beta (residual H R s) := by
    simp only [residual, map_sub, map_add, map_pow, map_mul]
    linear_combination hr
  have hprod : (PowerSeries.X : P) ^ n ∣ (r - beta s) * (r + beta s + beta H) := by
    rw [he]
    exact dvd_neg.mpr hd
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at hprod
  obtain ⟨w, hw⟩ := hprod
  refine ⟨w * (↑(u⁻¹) : P), ?_⟩
  calc
    r - beta s = ((r - beta s) * (u : P)) * (↑(u⁻¹) : P) := by simp [mul_assoc]
    _ = (PowerSeries.X : P) ^ n * (w * (↑(u⁻¹) : P)) := by rw [hw]; ring

theorem infinity_zero_jet_agreement :
    (PowerSeries.X : P) ^ 9 ∣ r₀ - beta jetInfinityZero := by
  apply root_jet_agreement N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly
    jetInfinityZero r₀ 9
  · decide
  · simpa [jetInfinityZero] using r₀_constant
  · simpa [beta, N13SpecialInfinityChart.hPoly, N13SpecialInfinityChart.rhsPoly, h, rhs] using r₀_relation
  · exact jet_polynomials_satisfy_equations.2.2.2.2.1

theorem infinity_one_jet_agreement :
    (PowerSeries.X : P) ^ 9 ∣ r₁ - beta jetInfinityOne := by
  apply root_jet_agreement N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly
    jetInfinityOne r₁ 9
  · decide
  · simpa [jetInfinityOne] using r₁_constant
  · simpa [beta, N13SpecialInfinityChart.hPoly, N13SpecialInfinityChart.rhsPoly, h, rhs] using r₁_relation
  · exact jet_polynomials_satisfy_equations.2.2.2.2.2

theorem infinity_numerator_zero_jet (A B : K[X]) :
    (PowerSeries.X : P) ^ 9 ∣
      (beta A + beta B * r₀) - beta (A + B * jetInfinityZero) := by
  have hd := dvd_mul_of_dvd_right infinity_zero_jet_agreement (beta B)
  convert hd using 1 <;> simp only [map_add, map_mul] <;> ring

theorem infinity_numerator_one_jet (A B : K[X]) :
    (PowerSeries.X : P) ^ 9 ∣
      (beta A + beta B * r₁) - beta (A + B * jetInfinityOne) := by
  have hd := dvd_mul_of_dvd_right infinity_one_jet_agreement (beta B)
  convert hd using 1 <;> simp only [map_add, map_mul] <;> ring

end
end MazurProof.N13SpecialRootJetAgreement
