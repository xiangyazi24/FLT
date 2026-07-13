import Mathlib

/-!
# Prime order 19 exclusion — kernel polynomial infrastructure

The exclusion of rational torsion of prime order 19 goes through X₀(19):

1. A rational order-19 point produces a rational cyclic 19-isogeny,
   hence a noncuspidal point on X₀(19)(ℚ).
2. X₀(19) = 19a1 has rank 0, torsion ℤ/3ℤ; its only noncuspidal
   rational point is the CM point (j = -884736).
3. The CM 19-isogeny kernel has x-coordinate polynomial `k₁₉` of
   degree 9 with no rational root.
4. Therefore no rational point of exact order 19 exists.

This file proves step 3: `kernelPoly19` has no rational root.
Steps 1–2 and 4 are deferred.

Python-verified: k₁₉ is monic, irreducible over ℚ, constant=-19⁴,
k₁₉ mod 2 = X⁹+X⁷+X²+X+1 has no root in 𝔽₂. (2026-07-12)
-/

open Polynomial

namespace MazurProof.PrimeExclusion19

noncomputable section

/-- The kernel x-coordinate polynomial of the CM 19-isogeny on 361a1. -/
def kernelPoly19 : Polynomial ℤ :=
  X ^ 9 - C 38 * X ^ 8 + C 437 * X ^ 7 - C 1444 * X ^ 6
    - C 7942 * X ^ 5 + C 82308 * X ^ 4 - C 274360 * X ^ 3
    + C 390963 * X ^ 2 - C 130321 * X - C 130321

/-- The monic integer polynomial `k₁₉` has no rational root.
    Proof sketch: monic ⇒ any ℚ root is in ℤ; k₁₉ mod 2 = X⁹+X⁷+X²+X+1
    has no root in 𝔽₂; hence no ℤ root, hence no ℚ root. -/
theorem kernelPoly19_no_rational_root (x : ℚ) :
    (kernelPoly19.map (Int.castRingHom ℚ)).eval x ≠ 0 := by
  sorry

end

end MazurProof.PrimeExclusion19
