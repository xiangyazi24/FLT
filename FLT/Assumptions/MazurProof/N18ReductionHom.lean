import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_Reduction
import FLT.Assumptions.MazurProof.N18Block5FormalKernel

/-!
# N18 Route C — the reduction homomorphism and the `hQ` prime-to-3 killer

This file discharges the *group-theoretic* content of the `hQ` gap of the N18
Block-5 instantiation (`N18Block5Instantiation.hQ`):

> prime-to-`3` torsion of `E₀(L)` is killed by `[7]`.

The chain is exactly the one sketched in the instantiation's `sorry`:

* the reduction map `red : E₀(L) →+ Ẽ₀(𝔽_π)` (`RedPoint`, `#RedPoint = 7`) sends
  `[7]·anything` to `0` because `Reduction.seven_nsmul` kills every residue
  point;
* hence `[7]·P` lies in `ker red`, which is the **formal kernel** `Ê₀(𝔪)`;
* the formal kernel has **no** prime-to-`3` torsion — this is the *already
  proven* `FormalKernel18.no_prime_to_3_torsion` (Lemma A);
* `[7]·P` is still prime-to-`3` torsion (multiply the killing exponent through),
  so it must be `0`.

The only inputs that the committed Route C infrastructure does **not** yet
construct are packaged as the two explicit hypotheses of the main theorem:

* `red : Isogeny.E0Point →+ Reduction.RedPoint` — the residue-reduction
  homomorphism (Mathlib has `WeierstrassCurve.Affine.Point.map` for a *field*
  hom, but not the 𝒪 → 𝔽 residue reduction; this map is the genuine residual);
* `e : red.ker ≃+ FK.M` — the identification of `ker red` with the formal
  kernel `FK.M = Ê₀(𝔪)` (this is the kernel-characterization `red_ker`,
  `red P = 0 ↔ 1 ≤ v_π(zParam P)`, packaged as an additive equivalence).

Everything downstream of those two objects — the `[7]`-killing and the Lemma-A
application — is proved here with **no** `sorry`.  The instantiation therefore
only has to supply `red` and `e` (equivalently `red` and `red_ker`).
-/

namespace MazurProof.N18ReductionHom

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny

/-- `[7]` kills every point of the seven-element reduction, as a `ℤ`-scalar
statement (the `ℕ`-version is `Reduction.seven_nsmul`). -/
theorem seven_zsmul_redPoint (Q : Reduction.RedPoint) : (7 : ℤ) • Q = 0 := by
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_cast, natCast_zsmul]
  exact Reduction.seven_nsmul Q

/-- **`hQ` core (fully proved, conditional on `red` and the kernel
identification `e`).**

Given the reduction homomorphism `red : E₀(L) →+ Ẽ₀(𝔽_π)` and an identification
`e : ker red ≃+ FK.M` of its kernel with the formal kernel of any
`FormalKernel18`, prime-to-`3` torsion of `E₀(L)` is annihilated by `[7]`.

Proof shape: `red ([7]·P) = [7]·red P = 0` (`seven_zsmul_redPoint`) puts `[7]·P`
in `ker red ≃ FK.M`; it is still killed by the prime-to-`3` exponent `j`, so
`FormalKernel18.no_prime_to_3_torsion` (Lemma A) forces `[7]·P = 0`. -/
theorem prime_to_3_torsion_killed_by_seven
    (red : E0Point →+ Reduction.RedPoint)
    (FK : FormalKernel18)
    (e : red.ker ≃+ FK.M)
    (P : E0Point) (hj : ∃ j : ℤ, ¬ (3 ∣ j) ∧ j • P = 0) :
    (7 : ℤ) • P = 0 := by
  obtain ⟨j, hj3, hjP⟩ := hj
  -- `[7]·P` reduces to `0`, hence lies in `ker red`.
  have hred7 : red ((7 : ℤ) • P) = 0 := by
    rw [map_zsmul]
    exact seven_zsmul_redPoint (red P)
  have hmem : (7 : ℤ) • P ∈ red.ker := AddMonoidHom.mem_ker.mpr hred7
  set q : red.ker := ⟨(7 : ℤ) • P, hmem⟩ with hq
  -- `[7]·P` is still prime-to-`3` torsion: `j • ([7]·P) = [7]·(j·P) = 0`.
  have hj7 : j • ((7 : ℤ) • P) = 0 := by
    rw [smul_comm, hjP, smul_zero]
  -- Transport into the formal kernel and apply Lemma A.
  have hjq : j • q = 0 := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_zsmul, ZeroMemClass.coe_zero, hq]
    exact hj7
  have hjz : j • (e q) = 0 := by
    rw [← map_zsmul, hjq, map_zero]
  have hzzero : e q = 0 := FK.no_prime_to_3_torsion j hj3 (e q) hjz
  have hqzero : q = 0 := e.injective (by rw [map_zero]; exact hzzero)
  have hval := congrArg Subtype.val hqzero
  rwa [ZeroMemClass.coe_zero] at hval

end MazurProof.N18ReductionHom

-- Axiom audit (kept for the record; safe to delete).
-- #print axioms MazurProof.N18ReductionHom.prime_to_3_torsion_killed_by_seven
