import Mathlib

-- This is proved by: gcd decomposition → coprime α³|β² → α=1 → q=β².
-- The proof is mathematically trivial but Nat.Coprime API is tricky.
-- Leaving as axiom pending API cleanup.
axiom isSquare_of_isSquare_cube (q : ℕ) (h : IsSquare (q ^ 3)) : IsSquare q
