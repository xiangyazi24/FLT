import FLT.Q6822Check
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.RamificationInertia.Inertia

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Q6822Check

/-- The original scalar tower for the polynomial-evaluation algebra. -/
local instance infinityParameterScalarTower :
    IsScalarTower ℚ InfinityParameterRing InfinityChart :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext q
    change
      algebraMap ℚ InfinityChart q =
        (Polynomial.eval₂RingHom
          (algebraMap ℚ InfinityChart) infinityChartU)
          (Polynomial.C q)
    simp

local instance basePrime_isMaximal : basePrime.asIdeal.IsMaximal :=
  basePrime.isPrime.isMaximal basePrime.ne_bot

attribute [local instance]
  infinityBoundaryXIdeal_isMaximal
  infinityBoundaryYIdeal_isMaximal
  infinityBoundaryZIdeal_isMaximal
  Ideal.Quotient.field

local instance infinityBoundaryXIdeal_liesOver :
    infinityBoundaryXIdeal.LiesOver basePrime.asIdeal :=
  infinityBoundaryXPrimeOver.property.2

local instance infinityBoundaryYIdeal_liesOver :
    infinityBoundaryYIdeal.LiesOver basePrime.asIdeal :=
  infinityBoundaryYPrimeOver.property.2

local instance infinityBoundaryZIdeal_liesOver :
    infinityBoundaryZIdeal.LiesOver basePrime.asIdeal :=
  infinityBoundaryZPrimeOver.property.2

/-- Evaluation at `0`, transported from `span {X - C 0}` to `basePrime.asIdeal`. -/
noncomputable def basePrimeResidueAlgEquiv :
    (InfinityParameterRing ⧸ basePrime.asIdeal) ≃ₐ[ℚ] ℚ :=
  (Ideal.quotientEquivAlgOfEq ℚ (by
      rw [basePrime_asIdeal]
      simp)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℚ))

/-- The old two-ideal inertia degree is one when the upper residue field is rational. -/
private theorem inertiaDeg'_eq_one_of_residueAlgEquiv
    (P : Ideal InfinityChart) [P.IsMaximal]
    [P.LiesOver basePrime.asIdeal]
    (eP : (InfinityChart ⧸ P) ≃ₐ[ℚ] ℚ) :
    basePrime.asIdeal.inertiaDeg' P = 1 := by
  rw [Ideal.inertiaDeg'_algebraMap]
  have hbase :
      Module.finrank ℚ
        (InfinityParameterRing ⧸ basePrime.asIdeal) = 1 := by
    simpa using basePrimeResidueAlgEquiv.toLinearEquiv.finrank_eq
  have htop : Module.finrank ℚ (InfinityChart ⧸ P) = 1 := by
    simpa using eP.toLinearEquiv.finrank_eq
  have htower :=
    Module.finrank_mul_finrank ℚ
      (InfinityParameterRing ⧸ basePrime.asIdeal)
      (InfinityChart ⧸ P)
  rw [hbase, htop] at htower
  simpa using htower

/-! Mock versions of the three residue equivalences already present in the
production boundary-fibre module. -/

noncomputable def infinityBoundaryXResidueAlgEquiv :
    (InfinityChart ⧸ infinityBoundaryXIdeal) ≃ₐ[ℚ] ℚ := by
  simpa [InfinityChart, infinityBoundaryXIdeal] using
    (AlgEquiv.quotientBot ℚ ℚ)

noncomputable def infinityBoundaryYResidueAlgEquiv :
    (InfinityChart ⧸ infinityBoundaryYIdeal) ≃ₐ[ℚ] ℚ := by
  simpa [InfinityChart, infinityBoundaryYIdeal] using
    (AlgEquiv.quotientBot ℚ ℚ)

noncomputable def infinityBoundaryZResidueAlgEquiv :
    (InfinityChart ⧸ infinityBoundaryZIdeal) ≃ₐ[ℚ] ℚ := by
  simpa [InfinityChart, infinityBoundaryZIdeal] using
    (AlgEquiv.quotientBot ℚ ℚ)

@[simp] theorem infinityBoundaryX_inertiaDeg' :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryXIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv
    infinityBoundaryXIdeal infinityBoundaryXResidueAlgEquiv

@[simp] theorem infinityBoundaryY_inertiaDeg' :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryYIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv
    infinityBoundaryYIdeal infinityBoundaryYResidueAlgEquiv

@[simp] theorem infinityBoundaryZ_inertiaDeg' :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryZIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv
    infinityBoundaryZIdeal infinityBoundaryZResidueAlgEquiv

@[simp] theorem infinityBoundaryX_inertiaDeg :
    infinityBoundaryXIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryXIdeal]
  exact infinityBoundaryX_inertiaDeg'

@[simp] theorem infinityBoundaryY_inertiaDeg :
    infinityBoundaryYIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryYIdeal]
  exact infinityBoundaryY_inertiaDeg'

@[simp] theorem infinityBoundaryZ_inertiaDeg :
    infinityBoundaryZIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryZIdeal]
  exact infinityBoundaryZ_inertiaDeg'

end Q6822Check
