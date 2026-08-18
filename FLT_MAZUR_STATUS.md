# Mazur Proof Status — 2026-08-18 (updated)

## Overall: `mazur_cyclic_order_bound_assembled` in CyclicOrderAssembly.lean

Theorem proved modulo 4 endpoint axioms (+ 5 dead-code sorries).
Mordell-Weil (`mordell_weil_fg`) intentionally kept.

## Banked this session

- `RationalPointsN49.lean` (94 lines, 0 sorry): proves preΨ'_7(0) = b^16*(c³+bc-b²)
- `FLT_MAZUR_STATUS.md`: this file
- ChatGPT Q5265 (N49 factorization), Q5267 (N49 chart lemma), Q5269 (p≥23 strategy), Q5270 (N13 local proof)

## Remaining Axioms + Consolidated Strategy

### 1. `C13Sextic_affine_x_is_cuspidal` — N13
- **Verdict (Q5270)**: Local mod-p arguments are fundamentally incomplete. The MW sieve needs J(Q)→J(F₅) injectivity (rank-0 proof). Wiring the existing 283-file infrastructure is LESS work than building MW sieve from scratch.
- **Concrete gap**: N13MumfordCenteredDoublingAdapter (line 160) constructs FirstJetDoublingCompatibility from h₁,h₃. This file is never imported. Need to instantiate kernel, class_eq_iff, and verify h₁/h₃ for the specific curve.
- **Next step**: Understand the NearBaseFamily interface and what h₁/h₃ require concretely.

### 2. `no_explicit_order25_obstruction` — N25
- **Status**: Active development (172 Aug commits). Don't touch.
- **Architecture**: Koszul resolution + twisting sheaves + Frobenius orbits. The ambient Koszul-to-curve seam is closed. Remaining: Picard/Riemann-Roch, canonical geometry, global rank-zero.

### 3. `no_raw_order49_tate_obstruction` — N49
- **Key facts (Q5265)**: preΨ'_49(0) = b^800 · F_7 · H_49 (3526 terms). Condition reduces to H_49(b,c)=0 with b≠0.
- **Verdict (Q5267)**: Tate scaling cannot normalize b (a₂=a₃ forces λ=1). Bihomogenize H_49, check 9 parity charts mod 2. Affine charts give 0,1,1,1. Five infinity charts need edge coefficients. The (0,0) chart is provably ZERO — needs Newton-face argument.
- **Verdict (Q5269)**: Pure local obstructions are impossible for any order (split Tate curves). The polynomial approach is the right one.
- **Sign check**: H_49 is NOT sign-definite (changes sign between (1,1) and (1,2)). Real roots exist but appear irrational.
- **Next step**: Compute edge coefficients h_{0,147}, h_{98,0}, h_{98,147} of H_49 mod 2.

### 4. `no_prime_order_ge_23` — p≥23
- **Verdict (Q5269)**: No shortcut exists. The formal-immersion/Eisenstein-ideal argument is the ONLY viable route. Faltings doesn't enumerate. Local obstructions are impossible. Merel-Oesterlé gives a uniform bound but is even deeper.
- **Architecture needed**: cusp specialization + abelian quotient A_p + MW control on A_p(Q) + formal immersion at cusp + noncuspidality contradiction.
- **Status**: Hardest axiom. No infrastructure exists yet.

### 5. `mordell_weil_fg` — Mordell-Weil
- **Status**: Intentionally kept as axiom. Standard.

## Dead-Code Sorries (5)

All confirmed dead — not transitively used by the assembled theorem.
| File | Line | Why dead |
|------|------|----------|
| N18AddCongr.lean | 303 | Wired version exists independently |
| KubertBridgeN16.lean | 342, 361 | DescentBridgeN16 uses different path |
| N18GoodModelZParam.lean | 42, 44 | File not imported by anything |

## Priority Ranking

1. **N13 wiring** — most concrete, infrastructure exists, Q5270 recommends this over MW sieve
2. **N49 edge computation** — needs H_49 edge coefficients + Newton-face, could close with ~5 more ChatGPT rounds
3. **N25** — actively developed, don't duplicate
4. **p≥23** — needs formal immersion, very hard, long-term
