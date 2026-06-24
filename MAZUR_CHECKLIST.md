# Mazur |T|≤16 — Checklist

**Status: 0 sorry, 12 axioms | Infrastructure building phase**

## Axiom 1: obstruction_curve_20a4_points_degenerate (3/6 done)
- [x] Integer descent: u ∈ Z → u ∈ {-1,0,1} (Descent20a4.lean)
- [x] Selmer φ-direction: 6/6 obstructions (SelmerD2, Selmer20a4, SelmerNeg, SelmerD10, SelmerNeg10Phi)
- [x] Selmer φ̂-direction: 6/6 obstructions (SelmerDual, SelmerDualD2, SelmerDualD10)
- [ ] Quartic d-by-d: d=2✅ d=3✅ d=4✅ d=5✅ d=6✅ d=7✅ d=8⬜ d=9✅
  - ⚠️ Each d is a theorem but doesn't cover all d uniformly
- [ ] Assembly: Selmer → rank 0 → integrality → integer descent → axiom
  - ⚠️ Blocked: descent exact sequence framework not in Mathlib
- [ ] 2-torsion bound: |E(Q)[2]| ≤ 4 (TwoTorsionBound.lean by Codex, needs verification)

## Axiom 2: obstruction_curve_N12_points_degenerate (2/5 done)
- [x] Bug fix: degenerate set {-2,1,2} → {-2,0,1,2,4}
- [x] N=12 descent structure: 3∤(u-1) case proved (DescentN12.lean)
- [ ] N=12 quartic subcase: b²=3a⁴+2a²-1
  - ⚠️ Blocked: same as quartic general d
- [ ] Integrality for Q
- [ ] Assembly

## Axiom 3: obstruction_curve_N14_points_degenerate (1/4 done)
- [x] Integer descent: odd case + even case (DescentN14.lean, 0 sorry)
- [ ] Integrality for Q
- [ ] Assembly

## Axiom 4: obstruction_curve_N16_points_degenerate (1/4 done)
- [x] Integer descent (DescentN16.lean, 0 sorry)
- [ ] Integrality for Q
- [ ] Assembly

## Axiom 5-8: Z2xZ{10,12,14,16}_gives_non_degenerate_*_point (0/4 done)
- [ ] Tate normal form infrastructure
- [ ] Kubert parametrization table
- [ ] Per-N polynomial computation
  - ⚠️ Blocked: requires Tate normal form + Kubert table formalization

## Axiom 9: mordell_weil_fg (0/1 done)
- [ ] Mordell-Weil theorem
  - ⚠️ Blocked: deep theorem, active FLT project work

## Axiom 10: rational_torsion_two_invariant_factors (0/1 done)
- [ ] Derive from mordell_weil_fg + weil_pairing + Mathlib structure theorem
- [x] InvariantFactorLemmas.lean: 4 supporting lemmas (0 sorry)
- [x] TwoTorsionBound.lean: |E[2]| ≤ 4 (Codex, 0 sorry, needs verification)
  - ⚠️ Needs: connect to rational_torsion_two_invariant_factors

## Axiom 11: weil_pairing_primitive_root (0/1 done)
- [ ] Weil pairing theory
  - ⚠️ Blocked: not in Mathlib

## Axiom 12: no_rational_point_of_order_ge_17 (0/1 done)
- [ ] Mazur cyclic bound (the hardest axiom)
  - ⚠️ Blocked: requires modular curve theory

---
**Infrastructure files (all 0 sorry):**
Descent20a4, DescentN14, DescentN16, Isogeny20a4, E20GoodReduction,
Selmer20a4, SelmerD2, SelmerNeg, SelmerD10, SelmerNeg10Phi,
SelmerDual, SelmerDualD2, SelmerDualD10, DescentN12, QuarticObstruction,
QuarticD2, QuarticD3, QuarticD4, QuarticD5, QuarticD6, QuarticD7, QuarticD9,
GroupTheory, RootsOfUnity, InvariantFactorLemmas, TwoTorsionBound,
X1_13_PointCount, X1_17_PointCount, E20_TorsionOrder, OddTorsion

Last verified: 2026-06-18
