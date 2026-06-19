# Automode Doctrine: Discharge obstruction_curve_20a4_points_degenerate

## Goal
Replace axiom obstruction_curve_20a4_points_degenerate with a theorem.
Concretely: prove ∀ u w : ℚ, w²=u³+u²-u → u ∈ {-1,0,1}.

## Avenues (ranked)

(a) SQUARECLASS BYPASS — use cover_forces_unit to show squarefree(p·q)=±1 directly,
    bypassing the valuation/multiplicity argument. If q has a prime factor with odd
    multiplicity, the cover equation forces that prime to divide 1. So q must be a
    perfect square. Then Int.sq_of_isCoprime → denominator quartic → contradiction.
    Terminal: rat_den_one_of_curve compiles with 0 sorry.

(b) VALUATION APPROACH — prove q is a perfect square via Nat.factorization/multiplicity.
    From b²|q³ and gcd(N,q)=1: 3v_ℓ(q)=2v_ℓ(b) → v_ℓ(q) even → q is perfect square.
    Terminal: clearing_denominators_gives_quartic compiles with 0 sorry.

(c) CODEX GRIND — let Codex (already dispatched) find the Mathlib API path.
    Terminal: Codex produces a compiling file.

## Fallback
If all avenues fail: leave rat_den_one_of_curve as the sole remaining axiom.
The chain from rat_den_one_of_curve → obstruction_20a4_discharge is already proved.

## Status
- dm1: working on perfect-square sub-lemma
- dm2: working on squareclass bypass approach
- Codex: dispatched for full rat_den_one_of_curve
