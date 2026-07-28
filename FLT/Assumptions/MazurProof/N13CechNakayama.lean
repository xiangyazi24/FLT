import FLT.Assumptions.MazurProof.N13FormalAbelLinearization
import Mathlib.RingTheory.LocalRing.Module

/-!
# The Nakayama step in the N13 nonspecial Čech lift

For a two-affine Čech complex over a local ring, surjectivity of the
special-fibre coboundary implies surjectivity of the integral coboundary
when its target is finite.  Moreover, any integral cochain whose
coboundary vanishes modulo the maximal ideal can be corrected, without
changing its reduction, to an actual cocycle.

These are the module-theoretic steps in lifting the canonical section of
the fixed nonspecial degree-two divisor.  The curve-specific work still
has to identify the two bounded-pole Čech modules and prove special-fibre
surjectivity.  No Picard scheme or representative-existence hypothesis is
used here.
-/

namespace MazurProof.N13CechNakayama

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {C0 : Type v} {C1 : Type w}
variable [AddCommGroup C0] [Module R C0]
variable [AddCommGroup C1] [Module R C1]

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- A linear map to a finite module is surjective when its range is
surjective after quotienting by the maximal ideal. -/
theorem surjective_of_residue_range_eq_top
    [Module.Finite R C1]
    (d : C0 →ₗ[R] C1)
    (hres :
      (LinearMap.range d).map
          (Submodule.mkQ
            (𝔪 • (⊤ : Submodule R C1))) = ⊤) :
    Function.Surjective d := by
  rw [← LinearMap.range_eq_top]
  exact (IsLocalRing.map_mkQ_eq_top).mp hres

/-- Čech cocycles lift across the residue map once the special-fibre
coboundary is surjective: an arbitrary cochain lift can be corrected by a
cochain in the maximal-ideal multiple. -/
theorem exists_kernel_lift_of_residue_range_eq_top
    [Module.Finite R C1]
    (d : C0 →ₗ[R] C1)
    (hres :
      (LinearMap.range d).map
          (Submodule.mkQ
            (𝔪 • (⊤ : Submodule R C1))) = ⊤)
    (x : C0)
    (hx : d x ∈ 𝔪 • (⊤ : Submodule R C1)) :
    ∃ z : C0,
      d z = 0 ∧
        x - z ∈ 𝔪 • (⊤ : Submodule R C0) := by
  have hd : Function.Surjective d :=
    surjective_of_residue_range_eq_top d hres
  have hrange : LinearMap.range d = ⊤ :=
    LinearMap.range_eq_top.mpr hd
  have hmap :
      (𝔪 • (⊤ : Submodule R C0)).map d =
        𝔪 • (⊤ : Submodule R C1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  have hxmap :
      d x ∈ (𝔪 • (⊤ : Submodule R C0)).map d := by
    rwa [hmap]
  obtain ⟨t, ht, htx⟩ := hxmap
  refine ⟨x - t, ?_, ?_⟩
  · rw [map_sub, htx, sub_self]
  · simpa using ht

end

end MazurProof.N13CechNakayama
