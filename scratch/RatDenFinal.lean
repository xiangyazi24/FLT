import Mathlib

/-!
# Denominator theorem for y²=x³+x²-x — simplified proof

Chain: cover trick → p=±1 → p=1 immediate → p=-1 via integer descent.
-/

-- From Descent20a4.lean (0 sorry)
axiom int_solutions_20a4 (u w : ℤ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1

-- The ONE remaining number-theory lemma:
-- if a²q = b²N with gcd(q,N)=1 and gcd(a,b)=1, then q is a perfect square.
-- (from: v_ℓ(q) = 2v_ℓ(b) - v_ℓ(a) = 2v_ℓ(b) for all ℓ|q)
axiom coprime_sq_dvd_implies_sq (q b : ℕ) (a N : ℤ)
    (hq : 2 ≤ q)
    (hab : Int.gcd a b = 1)
    (hqN : Nat.Coprime q N.natAbs)
    (heq : a ^ 2 * q = b ^ 2 * N) :
    IsSquare q

theorem rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  sorry -- will be filled once coprime_sq_dvd_implies_sq is proved

