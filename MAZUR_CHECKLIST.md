# MazurProof Sorry Analysis — 2026-07-08

**Status: 12 sorry, 14 axiom (in CyclicOrderAssembly + other files)**

## Sorry Classification

### Category A: Tate NF Bridge (4 sorry)
These bridge from `HasRationalPointOfOrder E N` to Tate NF parameters.
BLOCKED ON: general Tate NF reduction theorem (not in Mathlib).

| File | Sorry | Statement |
|------|-------|-----------|
| CyclicExclusion11:173 | `tate_polynomial_system_solution_of_order11` | order 11 → Tate system |
| CyclicExclusion15:155 | `simultaneous_order3_and5_tate_bridge` | orders 3+5 → Tate |
| CyclicExclusion18:29 | `order18_to_tate_obstruction` | order 18 → Tate |
| CyclicExclusion21:34 | `order21_to_tate_obstruction` | order 21 → Tate |

### Category B: Diophantine / Rational Points (4 sorry)
Prove that specific polynomial systems have no rational solutions.
BLOCKED ON: descent/Chabauty/rank computations.

| File | Sorry | Curve | Genus | Method |
|------|-------|-------|-------|--------|
| CyclicExclusion11:185 | `no_tate_order11_polynomial_solution` | X₁(11) = 11a3 | 1 | rank 0 descent |
| CyclicExclusion15:172 | `no_tate_order5_psi3_root_solution` | X₁(15) | 1 | rank 0 descent |
| CyclicExclusion18:32 | `no_obstruction18` | X₁(18) | 2 | Chabauty |
| CyclicExclusion21:37 | `no_obstruction21` | X₁(21) | ? | Chabauty/descent |

### Category C: Kubert Bridge / Modular Parametrization (4 sorry)
Explicit polynomial maps between Tate NF and obstruction curves.
BLOCKED ON: modular curve parametrization computation.

| File | Sorry | Content |
|------|-------|---------|
| CyclicExclusion14:77 | `cyclic_order_14_kubert_bridge` | order 14 → 96A1 |
| CyclicExclusion16:112 | `cyclic_order_16_kubert_bridge` | order 16 → N16 curve |
| KubertBridgeN16:288 | `kubert_C16_discriminant_data` | Z/2×Z/16 → Tate disc |
| KubertBridgeN16:307 | `EN16_point_of_Phi16_and_disc` | Tate disc → N16 curve |

## Tractability Assessment

**Most tractable (Category B, genus 1):**
- X₁(11) = 11a3: rank 0 over Q, denominator descent feasible (~1000 lines)
- X₁(15): rank 0 over Q, similar approach

**Moderate (Category C):**
- Kubert bridges: concrete polynomial computation, could be done with
  polyrith/ring/field_simp once the map is known

**Hard (Category A):**
- General Tate NF reduction: requires Weierstrass coordinate change theory

**Hardest (Category B, genus 2):**
- X₁(18), X₁(21): need genus-2 Jacobian rank computation (Chabauty)

## Session Progress

| Commit | Content | Sorry closed |
|--------|---------|-------------|
| 0796e235 | CyclicExclusion20: 5 group-theory sorry | 5 |
| 3b0e38e6 | CyclicExclusion15: false statement fixed | 0 |
| 6734e097 | eq_five_nsmul independence lemma | 0 |
| cef30929 | N14 axiom→theorem wiring (remote build) | 1+1axiom |
| fa82cf3b | Z2×Z10 injective embedding | 0 |
| 20ff9cfa | CyclicExclusion20: ALL 7 sorry CLOSED | 2 |

**Total this session: 7 sorry closed, 1 axiom discharged, 1 false statement fixed.**
