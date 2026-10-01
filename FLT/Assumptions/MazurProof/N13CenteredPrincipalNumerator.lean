import FLT.Assumptions.MazurProof.N13ConstructedMappedSpecialFamily
import FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter
import FLT.Assumptions.MazurProof.N13PrincipalBranchBalance

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Extract the actual principal multiplier for the selected centered double,
with zero order on both infinity sheets. Clearing u(P)^2 gives a nonzero
regular numerator lying in BOTH the base/double ideal and the squared
conjugate ideal. The normalized Hermite numerator is not identified here.
-/

namespace MazurProof.N13CenteredPrincipalNumerator

noncomputable section
open SexticMumford
open scoped nonZeroDivisors
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := ℚ_[2]
abbrev M := N13Mumford.model K
abbrev R := N13Mumford.CoordinateRing K
abbrev F := N13Mumford.FunctionField K
abbrev DiskPair := N13TwoAdicAbelChartData.DiskPair
abbrev B := N13TwoAdicAbelChartData.basePair

theorem multiplier_of_centered_double (P Q : DiskPair)
    (hc : N13TwoAdicAbelChartPic.DiskPair.centeredPic Q =
      2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic P) :
    ∃ α : Fˣ,
      mumfordIdealUnit M P.mumford.toSemi * mumfordIdealUnit M P.mumford.toSemi *
        toPrincipalIdeal R F α = mumfordIdealUnit M Q.mumford.toSemi *
          mumfordIdealUnit M B.mumford.toSemi ∧
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0 ∧
      Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) = 0 := by
  have hs : N13TwoAdicAbelChartPic.DiskPair.pic P +
      N13TwoAdicAbelChartPic.DiskPair.pic P =
    N13TwoAdicAbelChartPic.DiskPair.pic Q + N13TwoAdicAbelChartPic.DiskPair.pic B := by
    calc
      _ = 2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic P +
          2 • N13TwoAdicAbelChartPic.DiskPair.pic B := by
        simp only [N13TwoAdicAbelChartPic.DiskPair.centeredPic, two_nsmul]
        abel
      _ = N13TwoAdicAbelChartPic.DiskPair.centeredPic Q +
          2 • N13TwoAdicAbelChartPic.DiskPair.pic B := by rw [← hc]
      _ = _ := by
        simp only [N13TwoAdicAbelChartPic.DiskPair.centeredPic, two_nsmul]
        abel
  let q := QuotientGroup.mk'
    (principalOriented M (N13Infinity.positiveInfinityOrder K)).range
  have hq : q (mumfordRaw M P.mumford * mumfordRaw M P.mumford) =
      q (mumfordRaw M Q.mumford * mumfordRaw M B.mumford) := by
    change q (mumfordRaw M P.mumford) * q (mumfordRaw M P.mumford) =
      q (mumfordRaw M Q.mumford) * q (mumfordRaw M B.mumford) at hs
    simpa only [map_mul] using hs
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at hq
  rw [QuotientGroup.mk'_eq_mk'] at hq
  obtain ⟨a, ha, he⟩ := hq
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp ha
  have hp := congrArg Prod.fst he
  have hplus : Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0 := by
    have hi := congrArg (fun z : OrientedFrac M => Multiplicative.toAdd z.2) he
    change ((-1 : ℤ) + -1) +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = -1 + -1 at hi
    omega
  refine ⟨α, hp, hplus, ?_⟩
  have hsum := N13PrincipalBranchBalance.principal_branch_orders_sum
    P.mumford.toSemi P.mumford.toSemi Q.mumford.toSemi B.mumford.toSemi α hp
  have hd (D : DiskPair) : D.mumford.toSemi.u.natDegree = 2 :=
    N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree D
  simp only [hplus, hd] at hsum
  omega

theorem tensor_numerator_mem_product
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α =
      mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    ∃ z : R,
      z ∈ (mumfordIdeal M D₂.u D₂.v * mumfordIdeal M D₃.u D₃.v) *
        (mumfordIdeal M (conjugateSemiMumford M D₀).u (conjugateSemiMumford M D₀).v *
          mumfordIdeal M (conjugateSemiMumford M D₁).u (conjugateSemiMumford M D₁).v) ∧
      algebraMap R F z = (α : F) * algebraMap R F (xClass M (D₀.u * D₁.u)) := by
  have hx (D : N13Mumford.SemiMumford K) :
      algebraMap R F (xClass M D.u) ∈
        (mumfordIdealUnit M D : FractionalIdeal R⁰ F) *
          (mumfordIdealUnit M (conjugateSemiMumford M D) : FractionalIdeal R⁰ F) := by
    rw [coe_mumfordIdealUnit, coe_mumfordIdealUnit,
      conjugateSemiMumford_u, conjugateSemiMumford_v,
      mumfordIdeal_mul_conj_fractional]
    exact FractionalIdeal.mem_coeIdeal_of_mem R⁰
      (Ideal.subset_span (Set.mem_singleton (xClass M D.u)))
  have hα : (α : F) ∈ (toPrincipalIdeal R F α : FractionalIdeal R⁰ F) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hmem := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mul_mem_mul (hx D₀) (hx D₁)) hα
  have hf := congrArg (fun U : InvFrac M => (U : FractionalIdeal R⁰ F)) h
  simp only [Units.val_mul] at hf
  have he :
      ((mumfordIdealUnit M D₀ : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₀)) *
        ((mumfordIdealUnit M D₁ : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) * toPrincipalIdeal R F α =
      ((mumfordIdealUnit M D₂ : FractionalIdeal R⁰ F) * mumfordIdealUnit M D₃) *
        ((mumfordIdealUnit M (conjugateSemiMumford M D₀) : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) := by
    calc
      _ = ((mumfordIdealUnit M D₀ : FractionalIdeal R⁰ F) * mumfordIdealUnit M D₁ *
          toPrincipalIdeal R F α) *
        ((mumfordIdealUnit M (conjugateSemiMumford M D₀) : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) := by ac_rfl
      _ = _ := by rw [hf]
  rw [he] at hmem
  simp only [coe_mumfordIdealUnit, ← FractionalIdeal.coeIdeal_mul] at hmem
  obtain ⟨z, hz, hze⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hmem
  refine ⟨z, hz, ?_⟩
  simpa only [xClass_mul, map_mul, mul_comm, mul_left_comm, mul_assoc] using hze

/-- The selected family double supplies a genuine regular numerator,
with all conjugate-double vanishing retained on the same witness. -/
theorem exists_selected_numerator
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∃ α : Fˣ, ∃ n : R,
      n ≠ 0 ∧
      n ∈ (mumfordIdeal M (L.pair (2 • z)).mumford.u (L.pair (2 • z)).mumford.v *
          mumfordIdeal M B.mumford.u B.mumford.v) *
        (mumfordIdeal M (conjugateSemiMumford M (L.pair z).mumford.toSemi).u
          (conjugateSemiMumford M (L.pair z).mumford.toSemi).v) ^ 2 ∧
      algebraMap R F n = (α : F) * algebraMap R F (xClass M ((L.pair z).mumford.u ^ 2)) ∧
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0 ∧
      Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) = 0 := by
  obtain ⟨α, hα, hp, hm⟩ := multiplier_of_centered_double (L.pair z) (L.pair (2 • z))
    (N13MumfordCenteredDoublingAdapter.centeredPic_pair_two_nsmul L z)
  obtain ⟨n, hn, he⟩ := tensor_numerator_mem_product
    (L.pair z).mumford.toSemi (L.pair z).mumford.toSemi
    (L.pair (2 • z)).mumford.toSemi B.mumford.toSemi α hα
  have hne : n ≠ 0 := by
    intro hz
    have hx : algebraMap R F (xClass M
        ((L.pair z).mumford.toSemi.u * (L.pair z).mumford.toSemi.u)) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R F).ne
        (xClass_ne_zero M (mul_ne_zero (L.pair z).mumford.u_monic.ne_zero
          (L.pair z).mumford.u_monic.ne_zero))
    rw [hz, map_zero] at he
    exact mul_ne_zero α.ne_zero hx he.symm
  refine ⟨α, n, hne, ?_, ?_, hp, hm⟩
  · simpa only [pow_two] using hn
  · simpa only [pow_two] using he

end
end MazurProof.N13CenteredPrincipalNumerator
