import FLT.Assumptions.MazurProof.N13IntegralHermiteCoefficientBounds

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Assemble the exact FirstJetDoublingCompatibility from the actual selected
principal multiplier. The SAME alpha and numerator are retained through
regularity, two-infinity bounds, good-model conversion, Hermite matching,
and exact integral norm descent. No compatibility or separatedness input
is added. Together with constructed K1 this gives actual-kernel separation.
-/

namespace MazurProof.N13ConstructedKernelDoubling

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open N13CenteredNumeratorPoleBounds N13GoodCenteredNumerator
open N13PrincipalHermiteNormalization N13ActualPrincipalNorm N13IntegralMatchedNorm
open N13IntegralHermiteCoefficientBounds
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem selected_cross_coefficients
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∀ i, ((L.pair z).u ^ 2 - N13AbelChartBase.baseSmoothMumford.u *
        (L.pair (2 • z)).u).coeff i ∈
      N13TwoAdicKernelChart.coordIdeal L.coord z * N13TwoAdicKernelChart.coordIdeal L.coord z := by
  let P := L.pair z
  let Q := L.pair (2 • z)
  obtain ⟨α, hα, hp, hm⟩ := multiplier_of_centered_double P Q
    (N13MumfordCenteredDoublingAdapter.centeredPic_pair_two_nsmul L z)
  obtain ⟨n, hmem, he⟩ := tensor_numerator_mem_product
    P.mumford.toSemi P.mumford.toSemi Q.mumford.toSemi B.mumford.toSemi α hα
  have hmem' : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
      mumfordIdeal M B.mumford.u B.mumford.v) *
    (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
      (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2 := by
    simpa only [pow_two] using hmem
  have he' : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)) := by
    simpa only [pow_two] using he
  have hn : n ≠ 0 := by
    intro hz
    have hx : algebraMap R F (xClass M (P.mumford.u ^ 2)) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R F).ne
        (xClass_ne_zero M (pow_ne_zero 2 P.mumford.u_monic.ne_zero))
    rw [hz, map_zero] at he'
    exact mul_ne_zero α.ne_zero hx he'.symm
  have hsmall := polynomial_bounds n hn
    (positive_numerator_order P α n he' hp) (negative_numerator_order P α n he' hm)
  obtain ⟨A, b, hA, hb, hshape⟩ := exists_good_hermite_shape n hsmall.1 hsmall.2
    (selected_base_membership P Q n hmem')
  obtain ⟨t, d₀, d₁, e₀, e₁, ht, hAmatch, hbmatch, he₀, he₁, hd₀, hd₁⟩ :=
    normalize_actual_numerator P Q n A b hn hA hb hshape hmem'
  -- hα belongs to this exact α; no independent norm multiplier is selected.
  obtain ⟨k, hnormQ⟩ := norm_of_actual_shape P Q α n A b hα he' hshape
  have hnormZ := descend_actual_norm P Q A b t ht d₀ d₁ e₀ e₁ hAmatch hbmatch he₁ k
    (by simpa only [N13TwoAdicMumfordTransport.mapPoly_apply] using hnormQ)
  have hcross := N13CenteredNormFirstOrder.cross_coefficients_of_norm P Q
    (N13HermiteResidualDivisibility.quad d₀ d₁)
    (N13HermiteResidualDivisibility.lin e₀ e₁) (1 - e₁)
    (quad_monic d₀ d₁) (centered_coefficients_mem P d₀ d₁ hd₀ hd₁)
    (lin_coefficients_mem P e₀ e₁ he₀ he₁) hnormZ
  intro i
  simpa only [N13CenteredHermiteFirstOrder.I,
    N13RationalKernelDoublingAdapter.NearBaseFamily.coord, P, Q] using hcross i

/-- The exact existing unary compatibility, with no new arithmetic input. -/
def forFamily
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility L :=
  N13MumfordCenteredDoublingAdapter.FirstJetDoublingCompatibility.ofCenteredCrossCoefficients
    L (fun z => selected_cross_coefficients L z 1)
      (fun z => selected_cross_coefficients L z 3)

/-- K2 for the SAME near-base family constructed by K1. -/
def firstJetCompatibility :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
      N13ConstructedMappedSpecialFamily.nearBaseFamily :=
  forFamily N13ConstructedMappedSpecialFamily.nearBaseFamily

/-- Separation of the actual constructed additive specialization kernel. -/
theorem actual_kernel_separated :
    N18RouteC.Separated.NSeparated N13ConstructedSpecialization.specialization.ker 2 :=
  N13ConstructedMappedSpecialFamily.mappedSpecialFamily.separated firstJetCompatibility

end
end MazurProof.N13ConstructedKernelDoubling
