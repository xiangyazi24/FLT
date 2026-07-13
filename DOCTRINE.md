# Automode Doctrine: Complete Mazur |E(ℚ)_tors| ≤ 16

## Goal

Discharge all axioms/sorry so `mazur_cyclic_order_bound_assembled` has
`#print axioms` = `{propext, Classical.choice, Quot.sound}` only.

## Current state (code-verified 2026-07-12)

### Axioms in CyclicOrderAssembly.lean
1. `mazur_prime_torsion_bound_sub` (line 70) — **Layer 2**: ∀ prime p ≥ 11, no rational p-torsion
2. `no_order_18` (line 80) — **Layer 1 residual**: ¬ HasRationalPointOfOrder E 18

### Sorry in source files
3. `CyclicExclusion18.lean:76` — `no_five_descent_solution` (the N18 content)
4. `N18AddCongr.lean:294` — `add_congr` (Package I formal kernel, feeds N18)
5. `KubertBridgeN16.lean:342` — `kubert_C16_discriminant_data` (Z/2×Z/16)
6. `KubertBridgeN16.lean:361` — `EN16_point_of_Phi16_and_disc` (Z/2×Z/16)

### Already closed (since prior doctrine)
CyclicExclusion 11, 14, 15, 16, 20, 21, 25, 27, 35, 49 — all sorry-free.

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

### (e) N18 E₀ route (Layer 1 residual)
**Terminal:** `no_five_descent_solution` sorry-free → `no_order_18` becomes a theorem.
Three sub-pieces per N18_HANDOFF.md:
  (A) Good-model port (crux)
  (B) Front-end via reduction-mod-5
  (C) Bridge: integer soln → rational point (independent, small)

### (f) KubertBridgeN16 (Z/2×Z/16)
**Terminal:** 2 sorry closed. Polynomial computations in Tate NF.

## Fallback
Axiomatize remaining hard theorems with precisely-scoped interfaces. Last resort.

## Execution order
(a) → (b) → (c) → (e.C) → (d) axiomatize → (e.A)+(f) parallel
