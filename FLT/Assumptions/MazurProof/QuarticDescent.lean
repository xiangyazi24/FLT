import Mathlib
import Mathlib.NumberTheory.PythagoreanTriples

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
  sorry -- ZMod 4 / ZMod 16 case analysis; r even B odd gives s²≡3 (mod 4)

/-! ## Step 2: UV = 5B⁴ factorization -/

theorem UV_eq_five_mul_fourth {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    (2 * r ^ 2 + B ^ 2 - 2 * s) * (2 * r ^ 2 + B ^ 2 + 2 * s) = 5 * B ^ 4 := by
  nlinarith [heq, sq_nonneg s, sq_nonneg r, sq_nonneg B]

/-! ## Step 3: Coprimality and positivity of U, V -/

-- These require careful mod arithmetic and are sorry'd for now

/-! ## Step 4: Coprime factorization of 5B⁴ -/

/-- If `U * V = 5 * B ^ 4` with `gcd(U,V) = 1`, `U,V > 0`, both odd,
then `∃ a b > 0` with `gcd(a,b) = 1`, `a*b = B`, and the factorization
is `(a⁴, 5b⁴)` or `(5a⁴, b⁴)`. -/
theorem coprime_factor_split_five_fourth {U V B : ℤ}
    (hU : 0 < U) (hV : 0 < V) (hB : 0 < B)
    (hcop : Int.gcd U V = 1)
    (hprod : U * V = 5 * B ^ 4) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ a * b = B ∧
      ((U = a ^ 4 ∧ V = 5 * b ^ 4) ∨ (U = 5 * a ^ 4 ∧ V = b ^ 4)) := by
  sorry -- unique factorization: each prime in B^4 divides exactly one of U,V

/-! ## Step 5: Pythagorean parametrization -/

/-- From `h² + b⁴ = r²` with `gcd(h, b²) = 1`, `h > 0`, extract Pythagorean
parametrization and coprime square factorization of `b²`. -/
theorem pythagorean_square_step {h b r : ℤ}
    (hh : 0 < h) (hb : 0 < b) (hr : 0 < r)
    (hcop : Int.gcd h (b ^ 2) = 1)
    (heq : h ^ 2 + b ^ 4 = r ^ 2) :
    ∃ u v : ℤ, 0 < u ∧ u < v ∧ Int.gcd u v = 1 ∧
      b = u * v ∧ 2 * h = v ^ 4 - u ^ 4 := by
  sorry -- PythagoreanTriple.isPrimitiveClassified_of_coprime + coprime square factors

/-! ## Step 6: Descent step -/

/-- The descent step: from a solution `(r, B, s)` with `B > 1`, produce a
smaller solution `(r', B', s')` with `B' < B`. -/
theorem descent_step {r B s : ℤ} (hr : 0 < r) (hB : 1 < B)
    (hcop : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    ∃ r' B' s' : ℤ, 0 < r' ∧ 0 < B' ∧ B'.natAbs < B.natAbs ∧
      Int.gcd r' B' = 1 ∧ s' ^ 2 = r' ^ 4 + r' ^ 2 * B' ^ 2 - B' ^ 4 := by
  sorry -- factor 5B⁴, Pythagorean step, new solution with smaller B

/-! ## Step 7: Strong induction -/

theorem quartic_plus_proved (r B s : ℤ) (hB : 0 < B) (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) : r = 1 ∧ B = 1 := by
  -- Strong induction on B.natAbs
  induction B.natAbs using Nat.strongRecOn with
  | _ n ih => sorry -- if B > 1, descent_step gives smaller; if B = 1, direct check

end MazurProof.QuarticDescent
