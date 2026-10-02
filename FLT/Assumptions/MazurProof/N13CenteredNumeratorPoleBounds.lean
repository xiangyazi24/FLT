import FLT.Assumptions.MazurProof.N13CenteredPrincipalNumerator
import FLT.Assumptions.MazurProof.N13BranchLeading

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

The actual selected-double principal numerator has pole order exactly four
at both infinities. The existing two-branch minimum-order theorem therefore
forces its sextic polynomial coefficients into degrees at most four and
one. No small-numerator hypothesis is supplied by the caller.
-/

namespace MazurProof.N13CenteredNumeratorPoleBounds

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open scoped LaurentSeries nonZeroDivisors
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem positive_numerator_order (P : DiskPair) (α : Fˣ) (n : R)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hα : Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0) :
    (N13Infinity.coordinateToLaurent K n).order = -4 := by
  have ha : N13Infinity.functionFieldToLaurent K (α : F) ≠ 0 := by
    simpa only [map_zero] using (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have hu : P.mumford.u ^ 2 ≠ 0 := pow_ne_zero 2 P.mumford.u_monic.ne_zero
  have hm := congrArg (N13Infinity.functionFieldToLaurent K) hn
  rw [map_mul, N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass] at hm
  change N13Infinity.coordinateToLaurent K n =
    N13Infinity.functionFieldToLaurent K (α : F) *
      N13BranchNorm.evalPoly K (P.mumford.u ^ 2) at hm
  change (N13Infinity.functionFieldToLaurent K (α : F)).order = 0 at hα
  rw [hm, HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hu), hα,
    N13BranchNorm.evalPoly_order K _ hu, natDegree_pow,
    show P.mumford.u.natDegree = 2 from
      N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree P]
  norm_num

theorem negative_numerator_order (P : DiskPair) (α : Fˣ) (n : R)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hα : Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) = 0) :
    (N13InfinityMinus.coordinateToLaurentMinus K n).order = -4 := by
  have ha : N13InfinityMinus.functionFieldToLaurentMinus K (α : F) ≠ 0 := by
    simpa only [map_zero] using (N13InfinityMinus.functionFieldToLaurentMinus_injective K).ne α.ne_zero
  have hu : P.mumford.u ^ 2 ≠ 0 := pow_ne_zero 2 P.mumford.u_monic.ne_zero
  have hm := congrArg (N13InfinityMinus.functionFieldToLaurentMinus K) hn
  rw [map_mul, N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
    N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
    N13InfinityMinus.coordinateToLaurentMinus_xClass] at hm
  change N13InfinityMinus.coordinateToLaurentMinus K n =
    N13InfinityMinus.functionFieldToLaurentMinus K (α : F) *
      N13BranchNorm.evalPoly K (P.mumford.u ^ 2) at hm
  change (N13InfinityMinus.functionFieldToLaurentMinus K (α : F)).order = 0 at hα
  rw [hm, HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hu), hα,
    N13BranchNorm.evalPoly_order K _ hu, natDegree_pow,
    show P.mumford.u.natDegree = 2 from
      N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree P]
  norm_num

theorem polynomial_bounds (n : R) (hne : n ≠ 0)
    (hp : (N13Infinity.coordinateToLaurent K n).order = -4)
    (hm : (N13InfinityMinus.coordinateToLaurentMinus K n).order = -4) :
    (coeff0 M n).natDegree ≤ 4 ∧ (coeffY M n).natDegree ≤ 1 := by
  let p := coeff0 M n
  let q := coeffY M n
  have hr : N13BranchNorm.linearFunction K p q = n := recompose M n
  have hx := N13BranchLeading.branch_min_order K p q (by rwa [hr])
  rw [hr, hp, hm, min_self] at hx
  have hb : N13BranchLeading.poleDegree K p q ≤ 4 := by omega
  change p.natDegree ≤ 4 ∧ q.natDegree ≤ 1
  by_cases hq : q = 0
  · simp only [N13BranchLeading.poleDegree, hq, if_true] at hb
    refine ⟨(le_max_left _ _).trans hb, ?_⟩
    rw [hq, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · simp only [N13BranchLeading.poleDegree, hq, if_false] at hb
    have h2 := (le_max_right _ _).trans hb
    exact ⟨(le_max_left _ _).trans hb, by omega⟩

theorem exists_selected_small_numerator
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∃ α : Fˣ, ∃ n : R,
      n ≠ 0 ∧ (coeff0 M n).natDegree ≤ 4 ∧ (coeffY M n).natDegree ≤ 1 ∧
      n ∈ (mumfordIdeal M (L.pair (2 • z)).mumford.u (L.pair (2 • z)).mumford.v *
          mumfordIdeal M B.mumford.u B.mumford.v) *
        (mumfordIdeal M (conjugateSemiMumford M (L.pair z).mumford.toSemi).u
          (conjugateSemiMumford M (L.pair z).mumford.toSemi).v) ^ 2 ∧
      algebraMap R F n = (α : F) * algebraMap R F (xClass M ((L.pair z).mumford.u ^ 2)) := by
  obtain ⟨α, n, hn, hmem, he, hp, hm⟩ := exists_selected_numerator L z
  have hb := polynomial_bounds n hn
    (positive_numerator_order (L.pair z) α n he hp)
    (negative_numerator_order (L.pair z) α n he hm)
  exact ⟨α, n, hn, hb.1, hb.2, hmem, he⟩

end
end MazurProof.N13CenteredNumeratorPoleBounds
