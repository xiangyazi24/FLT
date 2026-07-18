# Automode Doctrine: Complete Mazur |E(ℚ)_tors| ≤ 16

## Goal

Discharge all axioms/sorry so `mazur_cyclic_order_bound_assembled` has
`#print axioms` = `{propext, Classical.choice, Quot.sound}` only.

## Current state (post-session 2026-07-17)

### Sorry inventory (code-level, after Fable R1 audit)

**LIVE sorry (4):**
1. `N18GoodModelAssembly.lean:86` — `exists_good_reduction` (reduction hom)
2. `N18GoodModelAssembly.lean:262` — `add_congr_good_weak` (ultrametric on E0Good)
3. `KubertBridgeN16.lean:342` — `kubert_C16_discriminant_data`
4. `KubertBridgeN16.lean:361` — `EN16_point_of_Phi16_and_disc`

**DEAD CODE sorry (4, no longer on critical path):**
- `N18GoodModelZParam.lean:42,44` — FALSE theorem (counterexample: (0, a-a²))
  File is orphan (nothing imports it). Superseded by `zParamGood_eq_zero_good`
  at Assembly:346 (proved, with InFormalKernel guard).
- `N18AddCongr.lean:303` — old `add_congr` (original E0 model). Superseded by
  `add_congr_wired` at N18AddCongrWired:56 (sorry-free). No consumers; the
  good-model route uses `add_congr_good_weak` instead.
- CyclicExclusion18.lean:76 — `no_five_descent_solution` WAS sorry; now wired
  to Assembly's proof via `exact Assembly.no_five_descent_solution`.

### Axiom inventory (`#print axioms mazur_cyclic_order_bound_assembled`)
1. `no_order_13_prime` — NEW sub-axiom for p=13
2. `no_prime_order_ge_17` — NEW sub-axiom for p≥17
3. `no_order_18` — feeds through CyclicExclusion18 → Assembly → sorry #1,#2
4. `no_explicit_order25_obstruction` — N25
5. `no_raw_order49_tate_obstruction` — N49
6. `exists_rational_two_isogeny_quotient` — N20/N24

### Key structural discovery (2026-07-17 Fable R1)

The CyclicExclusion18 import cycle was broken:
- Assembly imported CyclicExclusion18 only for transitive RationalPointsN18Descent access.
- Replaced with direct import. Now CyclicExclusion18 imports Assembly and uses its
  `no_five_descent_solution` (proved via Block 7 + formal kernel machine).
- The N18 sorry cluster reduces to **2 live sorry** (Assembly:86, :262).

## Avenues (ranked by actionability, updated 2026-07-17)

### (e) N18 Assembly — close the 2 remaining sorry [ACTIVE]

**2 sorry → 0 sorry closes axiom #3 (`no_order_18`).**

**Sorry #1: `exists_good_reduction` (Assembly:86)**
Terminal boss. Block 7 consumes the hom itself.
Fable design:
- OL = Z[a] (maximal, disc=81). Residue map at π=a-1 is a↦1 onto F₃.
- Define red by valuation trichotomy: 0/near-O → 0; integral → residues.
- Kernel characterization is definitional. Pain concentrates in `map_add`.
- `map_add` four cases: (i) 0 input; (ii) integral+near-O; (iii) both near-O;
  (iv) both integral (hardest: divided-difference identity + finite ZMod 3 checks).

**Sorry #2: `add_congr_good_weak` (Assembly:262)**
Regenerate the three E0 branch proofs for E0Good with general a₁, a₃.
Ultrametric estimates only used v(aᵢ) ≥ 0 (holds for E0Good integral model).
The a₁=a₃=1 specialization in BC_factor is the only breakage — fix with
generalized identity (still closes by `ring`). Use N18AddCongrProof.lean
(1278 lines) as template.

**Critical path:** #1 ‖ #2 (parallel). Then `no_order_18` closes.

### (f) KubertBridgeN16 — 2 sorry
**Terminal:** polynomial computations in Tate NF.
- `kubert_C16_discriminant_data` — Tate → discriminant data
- `EN16_point_of_Phi16_and_disc` — birational map

### (a)-(d) Layer 2 prime exclusions
After N18 lands. See earlier doctrine entries.

## Fallback
Axiomatize remaining hard theorems with precisely-scoped interfaces. Last resort.

## Execution order (updated 2026-07-17 post-Fable)
1. (e) N18 Assembly sorry #1 ‖ #2 — parallel, both HIGH
2. (f) KubertBridgeN16 — parallelizable with (e)
3. (a)/(b)/(c) — prime exclusions
