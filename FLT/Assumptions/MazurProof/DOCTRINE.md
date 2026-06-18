# DOCTRINE: Mazur |T| ≤ 16 — Axiom Discharge Campaign

## Goal
Discharge as many of the 6 axiom seams in MazurProof/ as possible, compiling on uisai2.

## Avenues (ranked by feasibility)

### (a) Axiom 2a: rational_torsion_finite
Replace with mordell_weil_fg axiom + provable group-theory reduction.
Terminal: TorsionFinite.lean compiles with mordell_weil_fg as sole axiom.

### (b) Axiom 4: no_Z2_cross_Zn_forbidden (N=10 case first)
Build ObstructionCurve.lean: define 20a1, verify discriminant, list rational points,
show closure under group law. Rank-0 certificate via 2-descent as a sub-axiom.
Terminal: ObstructionCurve.lean compiles, N=10 exclusion proved modulo descent certificate.

### (c) Axiom 2b+2c: torsion structure refinement
Decompose opaque predicates into concrete Lean definitions where possible.
Pure group theory parts (e.g., ℤ/m × ℤ/n with m|n contains (ℤ/m)²) should be proved.
Terminal: group-theory lemmas compile, hard EC inputs remain as smaller axioms.

### (d) Axiom 1: Weil pairing
Explore defining Weil pairing via Miller's algorithm or divisor theory.
Terminal: even a partial formalization (definition + key property) is progress.

### (e) Axiom 3: no_rational_point_of_order_ge_17
Explore explicit X_1(17) model + rational-point certificate.
Terminal: any progress on the smallest case (p=17).

## Fallback
If all avenues hit Mathlib API gaps, document gaps precisely (file, line, missing lemma)
and file Mathlib issues or write bridging lemmas.

## Workers
- codex (uisai2): writes + compiles Lean code
- dm1, dm2 (ChatGPT Pro): mathematical analysis + Lean proof sketches
- me (Opus): architecture, review, integration, Xiang-proxy adjudication
