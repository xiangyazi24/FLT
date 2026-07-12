import FLT.Assumptions.MazurProof.N18MumfordRecover
import FLT.Assumptions.MazurProof.N18InfinityAPI

/-!
# Constant-principal end of balanced Mumford rigidity

The geometric small-pole lemma is separated from the purely algebraic final
step.  Once the principal multiplier is constant, its fractional ideal and
positive-infinity order are trivial; the kernel calculation then recovers the
balanced triple.
-/

open scoped nonZeroDivisors

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem principal_between_balanced_of_constant
    {D₁ D₂ : Mumford K} {α : (FunctionField K)ˣ}
    (c : Kˣ)
    (hα : α = N18Infinity.functionConstUnit K c)
    (hIdeal :
      mumfordIdealUnit K D₁.toSemi *
          toPrincipalIdeal (CoordinateRing K) (FunctionField K) α =
        mumfordIdealUnit K D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N18Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    D₁ = D₂ := by
  subst α
  have hUnits : mumfordIdealUnit K D₁.toSemi =
      mumfordIdealUnit K D₂.toSemi := by
    simpa only [N18Infinity.principalIdeal_functionConstUnit, mul_one] using hIdeal
  have hFrac := congrArg
    (fun I : InvFrac K ↦
      (I : FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))) hUnits
  simp only [coe_mumfordIdealUnit] at hFrac
  have hIdeal' : mumfordIdeal K D₁.u D₁.v =
      mumfordIdeal K D₂.u D₂.v :=
    FractionalIdeal.coeIdeal_inj.mp hFrac
  have hInf' :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
    simpa only [N18Infinity.ordPlus_functionConstUnit, mul_one] using hInf
  have hz : ((D₁.nInf : ℤ) - 1) = ((D₂.nInf : ℤ) - 1) :=
    Multiplicative.ofAdd.injective hInf'
  have hn : D₁.nInf = D₂.nInf := by omega
  exact mumford_eq_of_ideal_eq_of_nInf_eq K hIdeal' hn

end

end MazurProof.N18Mumford
