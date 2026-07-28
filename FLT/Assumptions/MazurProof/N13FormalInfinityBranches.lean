import FLT.Assumptions.MazurProof.N13FormalInfinityChart
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The two Hensel branches at infinity for N13

The formal-infinity equation

`v² + (1 + X² + X³)v - (X + X²) = 0`

reduces modulo `X` to `v(v + 1)`.  Both roots of the special fibre are
simple.  This file lifts the root `0` by X-adic Hensel, obtains the conjugate
root from the quadratic equation, and proves that their difference is a
unit.  These are the structural inputs for splitting the complete
infinity-chart algebra by two-point evaluation.
-/

open Polynomial

namespace MazurProof.N13FormalInfinityBranches

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalInfinityChart.R₂

abbrev Power : Type :=
  N13FormalInfinityChart.Power

/-- The X-adic ideal in the complete coefficient ring. -/
def xIdeal : Ideal Power :=
  Ideal.span ({PowerSeries.X} : Set Power)

local instance : IsAdicComplete xIdeal Power := by
  unfold xIdeal
  infer_instance

theorem infinityCurvePoly_eval_zero_mem :
    N13FormalInfinityChart.infinityCurvePoly.eval 0 ∈ xIdeal := by
  have hx : PowerSeries.X ∈ xIdeal :=
    Ideal.subset_span (Set.mem_singleton PowerSeries.X)
  have hrhs : N13FormalInfinityChart.rhsPower ∈ xIdeal := by
    unfold N13FormalInfinityChart.rhsPower
    refine Ideal.add_mem xIdeal hx ?_
    simpa only [pow_two] using
      Ideal.mul_mem_left xIdeal PowerSeries.X hx
  simpa [N13FormalInfinityChart.infinityCurvePoly] using
    Submodule.neg_mem xIdeal hrhs

theorem infinityCurvePoly_derivative_eval_zero :
    N13FormalInfinityChart.infinityCurvePoly.derivative.eval 0 =
      N13FormalInfinityChart.hPower := by
  simp [N13FormalInfinityChart.infinityCurvePoly]

theorem infinityCurvePoly_derivative_mod_x_isUnit :
    IsUnit
      (Ideal.Quotient.mk xIdeal
        (N13FormalInfinityChart.infinityCurvePoly.derivative.eval 0)) := by
  rw [infinityCurvePoly_derivative_eval_zero]
  have hmod :
      Ideal.Quotient.mk xIdeal N13FormalInfinityChart.hPower = 1 := by
    have hx : PowerSeries.X ∈ xIdeal :=
      Ideal.subset_span (Set.mem_singleton PowerSeries.X)
    have hx0 :
        Ideal.Quotient.mk xIdeal PowerSeries.X = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simp [N13FormalInfinityChart.hPower, hx0]
  rw [hmod]
  exact isUnit_one

/-- The simple special-fibre root `v = 0` has an X-adic lift. -/
theorem exists_branch_zero :
    ∃ r : Power,
      N13FormalInfinityChart.infinityCurvePoly.IsRoot r ∧
        r ∈ xIdeal := by
  obtain ⟨r, hr, hr0⟩ :=
    HenselianRing.is_henselian
      N13FormalInfinityChart.infinityCurvePoly
      N13FormalInfinityChart.infinityCurvePoly_monic
      0 infinityCurvePoly_eval_zero_mem
      infinityCurvePoly_derivative_mod_x_isUnit
  refine ⟨r, hr, ?_⟩
  simpa using hr0

/-- The Hensel branch reducing to `v = 0`. -/
def branchZero : Power :=
  Classical.choose exists_branch_zero

theorem branchZero_isRoot :
    N13FormalInfinityChart.infinityCurvePoly.IsRoot branchZero :=
  (Classical.choose_spec exists_branch_zero).1

theorem branchZero_mem_xIdeal :
    branchZero ∈ xIdeal :=
  (Classical.choose_spec exists_branch_zero).2

theorem branchZero_relation :
    branchZero ^ 2 +
        N13FormalInfinityChart.hPower * branchZero -
      N13FormalInfinityChart.rhsPower = 0 := by
  simpa [N13FormalInfinityChart.infinityCurvePoly] using
    branchZero_isRoot

theorem branchZero_constantCoeff :
    PowerSeries.constantCoeff branchZero = 0 := by
  have hle :
      xIdeal ≤ RingHom.ker
        (PowerSeries.constantCoeff : Power →+* R₂) := by
    rw [xIdeal, Ideal.span_le]
    intro z hz
    subst z
    exact RingHom.mem_ker.mpr PowerSeries.constantCoeff_X
  exact RingHom.mem_ker.mp (hle branchZero_mem_xIdeal)

/-- The conjugate Hensel branch, reducing to `v = 1` modulo `(2, X)`. -/
def branchOne : Power :=
  -N13FormalInfinityChart.hPower - branchZero

theorem branchOne_isRoot :
    N13FormalInfinityChart.infinityCurvePoly.IsRoot branchOne := by
  have hsame :
      branchOne ^ 2 +
          N13FormalInfinityChart.hPower * branchOne -
        N13FormalInfinityChart.rhsPower =
        branchZero ^ 2 +
          N13FormalInfinityChart.hPower * branchZero -
        N13FormalInfinityChart.rhsPower := by
    unfold branchOne
    ring
  simpa [N13FormalInfinityChart.infinityCurvePoly, hsame] using
    branchZero_relation

theorem branch_sum :
    branchZero + branchOne =
      -N13FormalInfinityChart.hPower := by
  unfold branchOne
  ring

theorem branch_product :
    branchZero * branchOne =
      -N13FormalInfinityChart.rhsPower := by
  have heq :
      branchZero ^ 2 +
          N13FormalInfinityChart.hPower * branchZero =
        N13FormalInfinityChart.rhsPower :=
    sub_eq_zero.mp branchZero_relation
  unfold branchOne
  calc
    branchZero *
          (-N13FormalInfinityChart.hPower - branchZero) =
        -(branchZero ^ 2 +
          N13FormalInfinityChart.hPower * branchZero) := by ring
    _ = -N13FormalInfinityChart.rhsPower := by rw [heq]

theorem branchOne_constantCoeff :
    PowerSeries.constantCoeff branchOne = -1 := by
  simp [branchOne, branchZero_constantCoeff,
    N13FormalInfinityChart.hPower]

theorem branch_difference_constantCoeff :
    PowerSeries.constantCoeff (branchZero - branchOne) = 1 := by
  simp [branchZero_constantCoeff, branchOne_constantCoeff]

/-- The two lifted branches remain disjoint over the complete base. -/
theorem branch_difference_isUnit :
    IsUnit (branchZero - branchOne) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    branch_difference_constantCoeff]
  exact isUnit_one

theorem infinityCurvePoly_factor :
    N13FormalInfinityChart.infinityCurvePoly =
      (X - C branchZero) * (X - C branchOne) := by
  calc
    N13FormalInfinityChart.infinityCurvePoly =
        X ^ 2 -
          C (branchZero + branchOne) * X +
          C (branchZero * branchOne) := by
            rw [branch_sum, branch_product]
            simp [N13FormalInfinityChart.infinityCurvePoly]
            ring
    _ = (X - C branchZero) * (X - C branchOne) := by
      rw [map_add, map_mul]
      ring

end

end MazurProof.N13FormalInfinityBranches
