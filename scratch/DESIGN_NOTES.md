# Mazur's Theorem Formalization — Consolidated Design Notes (R1-R4)

## Goal
Prove in Lean 4: `∀ E : WeierstrassCurve ℚ, [E.IsElliptic] → (torsion E(ℚ)).ncard ≤ 16`

## Key Insight (R3): |T| ≤ 16 ≠ full Mazur classification
We only need the SIZE bound, not the classification. This means:
- ℤ/11 (size 11 ≤ 16): don't need to exclude
- ℤ/13 (size 13 ≤ 16): don't need to exclude
- ℤ/2 × ℤ/8 (size 16): largest in Mazur's list, OK

Only need to exclude groups with > 16 elements.

## Architecture (R4, confirmed by Weil pairing)

### Input 0: Torsion is finite
- Method: good reduction at two primes of different residue char
- Mathlib status: Reduction.lean has good/bad reduction predicates. Missing: injectivity of reduction on torsion.

### Input 1: Torsion rank ≤ 2
- E[n] ≅ (ℤ/n)² over algebraic closure → T ≅ ℤ/m × ℤ/n with m | n
- Mathlib status: finite abelian group structure theorem EXISTS. EC torsion structure missing.

### Input 2: Weil pairing → m ≤ 2
- If E[m] ⊂ E(ℚ), Weil pairing is nondegenerate → μ_m ⊂ ℚ* → m ≤ 2
- SHORTCUT: Mathlib has `LinearOrderedRing.orderOf_le_two` (codex found this)
  In ℚ (linear ordered field), any element of finite multiplicative order has order ≤ 2, i.e., = ±1.
  Combined with Weil pairing → m ≤ 2.
- Alternative: determinant of mod-m Galois representation = cyclotomic character, trivial iff μ_m ⊂ K.
- Mathlib status: Weil pairing MISSING. But roots of unity over ℚ = {±1} is provable now.

### Input 3: No rational torsion point of order ≥ 17 (THE HARD PART)
- Equivalent to: X_1(n)(ℚ) = cusps for n ≥ 17
- Must handle: n = 17, 18, 19, 20, ..., and all n ≥ some bound
- Composite orders: n = 18 (= 2×9) has all prime factors < 17 but |ℤ/18| = 18 > 16
- Two sub-layers:
  (a) Large primes: no point of order p for ALL primes p ≥ 17 (Mazur/Merel)
  (b) Composite: no point of order n for specific n = 18, 20, 21, 22, 24, 25, 26, 27, 28
      (all have prime factors < 17 but n > 16)
- For (b): a point of order n has a point of order d for each d | n. So:
  - order 18 → order 9 and order 2 → ℤ/18 cyclic (since gcd(9,2)=1)
  - order 20 → order 5 and order 4 → ℤ/20 cyclic
  - etc.
  These require X_1(n)(ℚ) = cusps for specific composite n. Explicit curve models available.

### Input 4: Noncyclic exclusions
- After m ≤ 2: only need to exclude ℤ/2 × ℤ/2n for 2n ≥ 10 (size 4n ≥ 20 > 16)
- Specifically: ℤ/2 × ℤ/10, ℤ/2 × ℤ/12, ℤ/2 × ℤ/14, ℤ/2 × ℤ/16
- And ℤ/2 × ℤ/2n for all 2n ≥ 18 (handled by Input 3: if ℤ/2 × ℤ/2n exists, there's a point of order 2n ≥ 18)

## Mathlib/FLT Infrastructure Summary

| Component | Status | Notes |
|-----------|--------|-------|
| WeierstrassCurve, points, group law | EXISTS | |
| j-invariant, discriminant | EXISTS | |
| Division polynomials | PARTIAL | Basic + Degree |
| Reduction mod primes | PARTIAL | Good/bad/mult/add predicates |
| Torsion subgroup definition | PARTIAL | nTorsion defined, key theorems sorry |
| Weil pairing | MISSING | |
| Isogenies | MISSING | |
| Modular curves X_0/X_1 | MISSING | |
| Jacobians of curves | MISSING | |
| Néron models | MISSING | |
| Formal groups of EC | MISSING | General formal group law EXISTS |
| Modular forms (analytic) | PARTIAL | Eisenstein, q-exp, cusps |
| Galois representations | PARTIAL | FLT deformation theory |
| Roots of unity over ℚ = {±1} | PROVABLE NOW | LinearOrderedRing.orderOf_le_two |
| Finite abelian group structure | EXISTS | |
| Cyclotomic polynomials | EXISTS | |
| DVRs, Dedekind domains | EXISTS | |
| Schemes | PARTIAL (4 files) | |

## Open Questions for R5+
1. What EXACTLY must be excluded for |T| ≤ 16? (dm1 R5 in progress)
2. Phase 1 implementation plan and LOC estimate? (dm2 R5 in progress)
3. Can codex prove roots-of-unity = {±1} in Lean 4? (codex R3 in progress)
