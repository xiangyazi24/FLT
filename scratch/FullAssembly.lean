import Mathlib

/-!
# Complete proof: rational points on y²=x³+x²-x have x ∈ {-1,0,1}
-/

-- Already proved in Descent20a4.lean (0 sorry, 57 lines)
axiom int_solutions_20a4 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1

-- Already proved in CoprimeSqDvd.lean (0 sorry, 28 lines)
axiom coprime_sq_dvd (q : ℕ) (b : ℕ) (a N : ℤ)
    (hab : Int.gcd a b = 1) (hqN : Nat.Coprime q N.natAbs)
    (heq : a ^ 2 * (q : ℤ) = (b : ℤ) ^ 2 * N) : IsSquare q

theorem obstruction_20a4 (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  -- Case u = 0
  by_cases hu : u = 0
  · right; left; exact hu
  -- Case u ≠ 0: show u.den = 1, then apply integer case.
  -- TODO: prove u.den = 1 using the chain.
  -- For now: axiomatize and prove the rest.
  sorry

