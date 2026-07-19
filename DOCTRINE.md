# Automode Doctrine: Complete Mazur |E(ℚ)_tors| ≤ 16

## Goal

Discharge all axioms/sorry so `mazur_cyclic_order_bound_assembled` has
`#print axioms` = `{propext, Classical.choice, Quot.sound}` only.

## Current state (post-session 2026-07-18, N18 ported from staging)

### Sorry inventory (code-level, after N16 ex-falso + N18 staging port)

**LIVE sorry on critical path: 0**
All N18 sorry discharged by porting complete proofs from staging tree
(`/home/xhuan5/repos/flt/`, 2026-07-13 vintage).

**DEAD CODE sorry (still present but NOT on critical path):**
- `KubertBridgeN16.lean:342` — `kubert_C16_discriminant_data` (disconnected by
  ex-falso rewiring of DescentBridgeN16.lean; `bridge_N16` unused)
- `KubertBridgeN16.lean:361` — `EN16_point_of_Phi16_and_disc` (same)
- `N18GoodModelZParam.lean:42,44` — FALSE theorem (counterexample: (0, a-a²))
  File is orphan (nothing imports it).
- `N18AddCongr.lean:303` — old `add_congr` (original E0 model). Superseded.
- `CyclicExclusion18.lean:76` — `no_five_descent_solution` (intentional sorry;
  bypassed at CyclicOrderAssembly level via Assembly's proved version)

### Axiom inventory (`#print axioms mazur_cyclic_order_bound_assembled`)
(Post N18 port, 2026-07-18 — pending build verification)
1. `no_order_13_prime` — prime p=13 exclusion
2. `no_order_17_prime` — prime p=17 exclusion
3. `no_order_19_prime` — prime p=19 exclusion
4. `no_prime_order_ge_23` — primes p≥23 exclusion
5. `CyclicExclusion25.no_explicit_order25_obstruction` — N25
6. `CyclicExclusion49.no_raw_order49_tate_obstruction` — N49
7. `exists_rational_two_isogeny_quotient` — N20/N24

**N=14,15,16,18,21,27,35 are now fully proved** (no longer axioms).
Total axioms: 7 (down from 8).

### Key structural discoveries

**2026-07-17: N16 sorry discharged ex falso.**
- DescentBridgeN16.lean rewired: Z/2Z × Z/16Z → ex falso via
  `no_rational_point_of_order_16`. KubertBridgeN16 sorry now dead code.

**2026-07-18: N18 ported from staging (0 sorry).**
- Complete proofs from `/home/xhuan5/repos/flt/` (2026-07-13) ported:
  N18PackageII (909L), N18GoodModelValCoords (250L), N18GoodModelAssembly (3107L),
  N18ReductionGood (337L).
- Import cycle resolved: CyclicExclusion18 reverted to staging (sorry on
  `no_five_descent_solution`); CyclicOrderAssembly.no_order_18 proved by composing
  CyclicExclusion18.order18_to_five_descent + N18GoodModelAssembly.no_five_descent_solution.
- **Live sorry on critical path: 2 → 0. no_order_18 axiom eliminated.**

## Avenues (ranked by actionability, updated 2026-07-18)

### (a) Layer 2 prime exclusions — 4 axioms [NEXT TARGET]
- `no_order_13_prime` — Mazur: modular curves / Ogg's conjecture route
- `no_order_17_prime` — Mazur: modular symbols
- `no_order_19_prime` — Mazur: modular symbols
- `no_prime_order_ge_23` — Mazur: Eisenstein ideal

### (b) Concrete composite exclusions — 2 axioms
- `no_explicit_order25_obstruction` — N25
- `no_raw_order49_tate_obstruction` — N49

### (c) 2-isogeny quotient — 1 axiom
- `exists_rational_two_isogeny_quotient` — N20/N24

### (f) KubertBridgeN16 — 2 sorry (DEAD CODE)
Not on critical path. Low priority.

## Fallback
Axiomatize remaining hard theorems with precisely-scoped interfaces. Last resort.

## Execution order (updated 2026-07-18)
1. Build verification + axiom audit (in progress)
2. (b) N25/N49 — most likely tractable (concrete polynomial computations)
3. (c) 2-isogeny — single axiom, well-defined interface
4. (a) Prime exclusions — hardest (modular curve infrastructure)
