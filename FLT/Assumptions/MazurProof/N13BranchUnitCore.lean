import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Branch-unit extraction for the N13 no-escape argument

The project-specific Čech layer will provide an integral infinity component
whose normalized reduction is the canonical special section.  This file
isolates the generic local-algebra consequence: a power series reducing to
one along a local homomorphism is a unit, and multiplication by an invertible
transition transfers that unit property to the affine branch restriction.
-/

namespace MazurProof.N13BranchUnitCore

noncomputable section

universe uR uk uA uV uV₀

variable {R : Type uR} {k : Type uk}
variable [CommRing R] [CommRing k]
variable (ρ : R →+* k) [IsLocalHom ρ]

/-- A power series whose coefficientwise image under a local homomorphism
is one must already be a unit. -/
theorem powerSeries_isUnit_of_map_eq_one
    {f : PowerSeries R}
    (hf : PowerSeries.map ρ f = 1) :
    IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  apply isUnit_of_map_unit ρ (PowerSeries.constantCoeff f)
  have h0 := congrArg (PowerSeries.coeff 0) hf
  have hconst :
      ρ (PowerSeries.constantCoeff f) = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  rw [hconst]
  exact isUnit_one

variable {A : Type uA}
variable {V : Type uV} {V₀ : Type uV₀}
variable [AddCommMonoid V] [AddCommMonoid V₀]

/--
If the normalized infinity component reduces to the canonical special
section on both branches, then an invertible transition makes both
normalized affine restrictions units.
-/
theorem normalizedAffineBranches_isUnit
    (redV : V →+ V₀)
    (affBranch : Fin 2 → A → PowerSeries R)
    (infBranch : Fin 2 → V → PowerSeries R)
    (specialInfBranch : Fin 2 → V₀ → PowerSeries k)
    (hbranchMap :
      ∀ j v,
        PowerSeries.map ρ (infBranch j v) =
          specialInfBranch j (redV v))
    (transition : Fin 2 → (PowerSeries R)ˣ)
    (baseInfinity : V₀)
    (hbase : ∀ j, specialInfBranch j baseInfinity = 1)
    (a : A)
    (v : V)
    (hred : redV v = baseInfinity)
    (hglue :
      ∀ j,
        affBranch j a =
          (transition j : PowerSeries R) * infBranch j v) :
    ∀ j, IsUnit (affBranch j a) := by
  have hinf : ∀ j, IsUnit (infBranch j v) := by
    intro j
    apply powerSeries_isUnit_of_map_eq_one (ρ := ρ)
    rw [hbranchMap j v, hred, hbase j]
  intro j
  rw [hglue j]
  exact (transition j).isUnit.mul (hinf j)

end

end MazurProof.N13BranchUnitCore
