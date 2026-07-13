import Mathlib

/-!
# Prime order 19 exclusion — kernel polynomial infrastructure

The CM 19-isogeny kernel polynomial `k₁₉` has no rational root.
Python-verified: monic, irreducible over ℚ, constant=-19⁴,
k₁₉ mod 2 = X⁹+X⁷+X²+X+1 has no root in 𝔽₂.
-/

open Polynomial

namespace MazurProof.PrimeExclusion19

noncomputable section

def kernelPoly19 : Polynomial ℤ :=
  X ^ 9 - C 38 * X ^ 8 + C 437 * X ^ 7 - C 1444 * X ^ 6
    - C 7942 * X ^ 5 + C 82308 * X ^ 4 - C 274360 * X ^ 3
    + C 390963 * X ^ 2 - C 130321 * X - C 130321

theorem kernelPoly19_monic : kernelPoly19.Monic := by
  unfold kernelPoly19; decide

private theorem kernelPoly19_no_root_mod2 (z : ZMod 2) :
    aeval z kernelPoly19 ≠ 0 := by
  fin_cases z <;> simp [kernelPoly19, aeval_def] <;> decide

theorem kernelPoly19_no_rational_root (x : ℚ) :
    aeval x kernelPoly19 ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic kernelPoly19_monic hx
  have hint : aeval z kernelPoly19 = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) kernelPoly19 = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 2) z) kernelPoly19 = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact kernelPoly19_no_root_mod2 _ hmod

end

end MazurProof.PrimeExclusion19
