import FLT.Q6822Check
import Mathlib.NumberTheory.RamificationInertia.Inertia
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
  rw [Ideal.inertiaDeg_algebraMap]
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

@[simp] theorem infinityBoundaryX_inertiaDeg'_test
    (eX : (InfinityChart ⧸ infinityBoundaryXIdeal) ≃ₐ[ℚ] ℚ) :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryXIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv infinityBoundaryXIdeal eX

@[simp] theorem infinityBoundaryY_inertiaDeg'_test
    (eY : (InfinityChart ⧸ infinityBoundaryYIdeal) ≃ₐ[ℚ] ℚ) :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryYIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv infinityBoundaryYIdeal eY

@[simp] theorem infinityBoundaryZ_inertiaDeg'_test
    (eZ : (InfinityChart ⧸ infinityBoundaryZIdeal) ≃ₐ[ℚ] ℚ) :
    basePrime.asIdeal.inertiaDeg' infinityBoundaryZIdeal = 1 :=
  inertiaDeg'_eq_one_of_residueAlgEquiv infinityBoundaryZIdeal eZ

@[simp] theorem infinityBoundaryX_inertiaDeg_test
    (eX : (InfinityChart ⧸ infinityBoundaryXIdeal) ≃ₐ[ℚ] ℚ) :
    infinityBoundaryXIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryXIdeal]
  exact infinityBoundaryX_inertiaDeg'_test eX

@[simp] theorem infinityBoundaryY_inertiaDeg_test
    (eY : (InfinityChart ⧸ infinityBoundaryYIdeal) ≃ₐ[ℚ] ℚ) :
    infinityBoundaryYIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryYIdeal]
  exact infinityBoundaryY_inertiaDeg'_test eY

@[simp] theorem infinityBoundaryZ_inertiaDeg_test
    (eZ : (InfinityChart ⧸ infinityBoundaryZIdeal) ≃ₐ[ℚ] ℚ) :
    infinityBoundaryZIdeal.inertiaDeg InfinityParameterRing = 1 := by
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    basePrime.asIdeal infinityBoundaryZIdeal]
  exact infinityBoundaryZ_inertiaDeg'_test eZ

end Q6822Check
