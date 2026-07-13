# Automode Doctrine: Complete Mazur |E(ℚ)_tors| ≤ 16

## Goal

Discharge all axioms/sorry so `mazur_cyclic_order_bound_assembled` has
`#print axioms` = `{propext, Classical.choice, Quot.sound}` only.

## Current state (post-commit 077eebc6, 2026-07-12)

### Full axiom inventory (`#print axioms mazur_cyclic_order_bound_assembled`)
1. `no_order_13_prime` — NEW sub-axiom for p=13
2. `no_prime_order_ge_17` — NEW sub-axiom for p≥17
3. `no_order_18` — N18 (Layer 1 residual)
4. `no_explicit_order25_obstruction` — N25
5. `no_raw_order49_tate_obstruction` — N49
6. `exists_rational_two_isogeny_quotient` — N20/N24

### Sorry in source files
7. `CyclicExclusion18.lean:76` — `no_five_descent_solution` (feeds #3)
8. `N18AddCongr.lean:294` — `add_congr` (Package I, feeds #7)
9. `KubertBridgeN16.lean:342` — `kubert_C16_discriminant_data`
10. `KubertBridgeN16.lean:361` — `EN16_point_of_Phi16_and_disc`

### Closed this session (commit 077eebc6)
- `mazur_prime_torsion_bound_sub` axiom → THEOREM (11+13+ge17 dispatcher)
- N18 bridge (C): `five_descent_to_noncuspidal` + `C_sq_eq_F18Positive` sorry-free

## Layer 2 ChatGPT pre-designs (scratch/layer2/)
- Q4463: Layer 2 scope (2A=p11, 2B=p13, 2C=tail p≥17, 2D=dispatcher)
- Q4464/Q4475: p=11 design + Lean draft (X₁(11)=11a3, genus-1 descent)
- Q4470/Q4478: p=13 design + Lean draft (X₁(13) genus-2)
- Q4490/Q4491/Q4494/Q4499/Q4505: uniform tail (Eisenstein/formal immersion/Kato)
- Q4481: Layer 3 design (torsion finiteness by 2-prime reduction, Weil pairing m≤2)

## Avenues (ranked by actionability)

### (a) Layer 2A: p=11 — X₁(11)=11a3, genus-1 descent [FIRST]
**Terminal:** sorry-free theorem feeding `mazur_prime_torsion_bound_sub` for p=11.
Architecture: 2-descent → 5-annihilator → formal-kernel separatedness → finite enum → cusps only.
Mirrors existing N15/N21 shared-filtration pattern. Lean draft Q4475 ready.
CyclicExclusion11.lean already sorry-free (handles order 11 via divisor reduction from 33/55/77).
Need: a PRIME-level theorem `no_prime_torsion_11`.

### (b) Layer 2 dispatcher: decompose the prime axiom
**Terminal:** `mazur_prime_torsion_bound_sub` replaced by `by_cases hp17` → three sub-axioms.
Per Q4463: prime p ≥ 11 is 11, 13, or ≥17. Pure `omega`/`interval_cases`.

### (c) Layer 2B: p=13 — X₁(13) genus-2
**Terminal:** sorry-free `no_prime_torsion_13`.
Fixed-curve Jacobian descent. Lean draft Q4478.

### (d) Layer 2C: uniform tail p≥17 — formal immersion
**Terminal:** sorry-free `no_prime_order_ge_17`, or axiomatized as `PrimeTailPackage` (Q4499).
Research-scale. May axiomatize interface and fill later.

### (e) N18 E₀ route — Fable campaign plan (2026-07-13 05:00)
**Terminal:** `no_five_descent_solution` sorry-free → `no_order_18` becomes a theorem.

**Completed:**
- (C) Bridge: `five_descent_to_noncuspidal` sorry-free
- Package I `add_congr` for E0: all 3 branches sorry-free (1278 lines)
  (inverse + distinct-x + tangent in N18AddCongrProof.lean)

**Remaining chain (Fable plan, 4 tiers):**

TIER 1 (interface fixes, do first):
- 1a: Fix `zParam_neg` → `vpi_zParam_neg` in FormalKernelData [LOW, Codex]
- 1b: N18GoodModelAssembly.lean skeleton [LOW, Codex]

TIER 2 (good-model FormalKernelData, serial core):
- 2a: zParamGood definition [LOW]
- 2b: vpi/vpi_three/vpi_unit reuse [LOW]
- 2c: val_coords for E0Good (Newton polygon, ℤ[a] coefficients) [MED]
- **2d: add_congr for E0Good** [HIGH — BC_factor fails (a₁≠1,a₃≠1), needs new identity (8). Oracle design required]
- 2e: vpi_pos_bridge [LOW]
- 2f: kernel_add_closed [MED]
- 2g: Package III (3-power torsion in kernel) [MED]
- **2h: Package II msq_torsionFree** [HIGH — needs [3]-series or Ψ₃. Oracle design required]

TIER 3 (transport and assembly):
- 3a: redGood : E0GoodPoint →+ RedPoint [MED-HIGH — no Mathlib API]
- 3b: hkerGood (kernel = formal kernel) [MED]
- 3c: Transport h21 via e0GoodEquiv [LOW]
- 3d: Build red_E0 and hker7_E0 [LOW]

TIER 4 (front-end wiring):
- 4a: Coordinate bridge (ring lemma) [LOW]
- 4b: no_five_descent_solution final assembly [LOW]

**Critical path:** 2d ‖ 2h (parallel, each HIGH) → 3a+3b → assembly
**Biggest risks:** 2d (new identity for E0Good) and 2h (Package II torsion-free)
**Front-end (B):** NOT needed per Fable — existing FiberTable does direct exhaustion

### (f) KubertBridgeN16 (Z/2×Z/16)
**Terminal:** 2 sorry closed. Polynomial computations in Tate NF.

## Fallback
Axiomatize remaining hard theorems with precisely-scoped interfaces. Last resort.

## Execution order
(a) → (b) → (c) → (e.C) → (d) axiomatize → (e.A)+(f) parallel
