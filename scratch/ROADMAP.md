# Mazur |T|≤16 Formalization — Status

## 0 sorry, 12 custom axioms

### Axiom Changes This Campaign
- **ELIMINATED**: `rational_torsion_two_invariant_factors` (EC-specific)
  → Derived as theorem from `mordell_weil_fg` + `weil_pairing_primitive_root` + group theory
- **ADDED**: `finite_abelian_two_invariant_factors` (pure group theory)
  → Provable from Mathlib `AddCommGroup.equiv_directSum_zmod_of_finite` + CRT
- **FIXED**: N=12 degenerate set {-2,1,2} → {-2,0,1,2,4} (old was FALSE)

### Current 12 Custom Axioms

| # | Axiom | Type | Difficulty |
|---|-------|------|-----------|
| 1 | `mordell_weil_fg` | EC theory | Deep (Mordell-Weil) |
| 2 | `weil_pairing_primitive_root` | EC theory | Medium (Weil pairing) |
| 3 | `finite_abelian_two_invariant_factors` | Group theory | **Mathlib-provable** |
| 4 | `no_rational_point_of_order_ge_17` | Modular curves | Hardest |
| 5-8 | `obstruction_curve_*` (×4) | Rank 0 | Hard (2-descent) |
| 9-12 | `Z2xZ*_gives_non_degenerate_*` (×4) | Kubert parametrization | Medium-Hard |

### Infrastructure Built (all 0 sorry)

**Integer Descent**: Descent20a4.lean, DescentN16.lean
**Complete 2-Descent Selmer Computation** for 20.a4:
  - φ-Selmer = {1,-1}: SelmerD2, Selmer20a4, SelmerNeg, SelmerD10, SelmerNeg10Phi
  - φ̂-Selmer = {1,5}: SelmerDual, SelmerDualD2, SelmerDualD10
  - 12 local obstructions, all 0 sorry
  - Rank formula: 1+1-1-1 = 0

**Other**: Isogeny20a4, E20GoodReduction, GroupTheory, RootsOfUnity,
X1_13_PointCount, X1_17_PointCount, OddTorsion
