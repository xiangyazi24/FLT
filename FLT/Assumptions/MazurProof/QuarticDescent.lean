import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsC20

/-!
# Infinite descent for the binary quartic s² = r⁴ + r²B² - B⁴

This file aims to prove `quartic_plus` by strong induction on `B`.

## Descent structure

Given `s² = r⁴ + r²B² - B⁴` with `gcd(r,B) = 1`, `r,B > 0`:

1. Both r, B are odd (mod 4 analysis).
2. Set `U = 2r²+B²-2s`, `V = 2r²+B²+2s`. Then `U·V = 5B⁴`.
3. `gcd(U,V) = 1`, both odd, both positive.
4. Factor: `(U,V) = (a⁴, 5b⁴)` or `(5a⁴, b⁴)` with `ab = B`, `gcd(a,b) = 1`.
5. In each case: `4r² = (a²-b²)² + 4b⁴` → `h² + b⁴ = r²` where `h = |a²-b²|/2`.
6. Pythagorean parametrize: `b² = (m-n)(m+n)`, coprime → `m-n = u²`, `m+n = v²`, `b = uv`.
7. New solution: `a² = v⁴ + v²u² - u⁴` with `B' = u < uv = b ≤ ab = B`. Descent!

## Status

This file is a WORK IN PROGRESS. The descent requires several helper lemmas that
are being developed in parallel (ChatGPT + subagents).
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.QuarticDescent

/-! ## Step 1: Both r, B must be odd -/

theorem quartic_plus_both_odd {r B s : ℤ} (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  -- If r even, B odd: s² ≡ 0 + 0 - 1 = -1 ≡ 3 (mod 4), impossible
  -- If r odd, B even: contradicts gcd(r,B)=1 only if B=2k with k odd, giving s²≡5 (mod 16)
  -- Both even: contradicts gcd(r,B)=1
  sorry

/-! ## Step 2: UV = 5B⁴ factorization -/

theorem UV_eq_five_mul_fourth {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) * (2 * r ^ 2 + B ^ 2 + 2 * s) = 5 * B ^ 4 := by
  nlinarith [heq, sq_nonneg s, sq_nonneg r, sq_nonneg B]

/-! ## Step 3: Coprimality and positivity of U, V -/

-- These require careful mod arithmetic and are sorry'd for now

/-! ## Step 4: Descent step (the core) -/

-- Given the factorization and Pythagorean parametrization, produce a smaller solution.
-- This is the key lemma that connects to PythagoreanTriple.isPrimitiveClassified_of_coprime.

/-! ## Step 5: Strong induction -/

-- theorem quartic_plus_proved : same statement as the axiom in RationalPointsC20.lean

end MazurProof.QuarticDescent
