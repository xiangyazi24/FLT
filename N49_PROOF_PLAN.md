# N49 Proof Plan — 2026-08-18 (updated)

## Goal
Prove `no_raw_order49_tate_obstruction`: H_49(b,c) = 0 has no rational root with b ≠ 0.

## Status: 8/9 bihomogeneous charts CLOSED

### Computation results (Python, verified)
- H_49 computed over Z[b,c]: 3526 terms, degrees 98 in b, 147 in c
- H_49 mod 2: 1603 terms
- Known edges: left = c^133, top = b^7, right = -1
- Diagonal: H_49(t,t) = -t^157

### Charts excluded

| Chart | (p,q)×(r,s) mod 2 | Method | Status |
|-------|-------------------|--------|--------|
| 3 | (0,1)×(1,1) | Parity | ✓ EXCLUDED |
| 4 | (1,0)×(0,1) | Parity | ✓ EXCLUDED |
| 6 | (1,0)×(1,1) | Parity | ✓ EXCLUDED |
| 7 | (1,1)×(0,1) | Parity | ✓ EXCLUDED |
| 8 | (1,1)×(1,0) | Parity | ✓ EXCLUDED |
| 9 | (1,1)×(1,1) | Parity | ✓ EXCLUDED |
| 1 | (0,1)×(0,1) | Newton face, sum odd | ✓ EXCLUDED |
| 5 | (1,0)×(1,0) | Newton face, sum odd | ✓ EXCLUDED |
| 2 | (0,1)×(1,0) | Multi-stage Newton | OPEN |

### Chart #2 Analysis

Newton polygon of H_49 in (i, 147-j) coordinates has 3 vertices:
- (0,14) with h_{0,133} = 1
- (2,3) with h_{2,144} = -1
- (7,0) with h_{7,147} = 1

For non-boundary α/β ratios: single vertex dominates with unit coefficient → excluded.
For boundary slopes α/β = 11/2 and 3/5: face polynomial = sum of 2 terms ±1, vanishes mod 2.

Stage-2 analysis: face brackets are (s'-r') mod 4 and (p'^5 r'^3 - q'^5 s'^3) mod 4.
For generic residues: stage 2 succeeds. Full closure needs all residue classes.

Multi-prime CRT {2,3,5} checked: same 3 charts zero at every prime (structural zeros from
h_{0,0}=h_{0,147}=h_{98,147}=0). CRT cannot close Chart #2.

### Approach options for Chart #2

1. **Complete Newton polygon descent at p=2**: Handle the 2 boundary slopes by
   multi-stage analysis. The face bracket 1-u^Δi v^Δj has v_2 depending on residues;
   show it never vanishes identically via mod-4/mod-8/... analysis.

2. **Algebraic argument**: Use the composition identity preΨ'_49 = preΨ'_7(x(7P))·preΨ'_7^49
   to reduce to a structural statement about the 7-division polynomial.

3. **Modular curve X_1(49)(Q) = cusps**: The traditional number-theoretic proof.
   Requires J_1(49)(Q) = 0 and Chabauty/descent.

### ChatGPT Q5293 dispatched for structural shortcut.

## Update: X_0(49) route (Q5294) — the correct global approach

### Key facts
- X_0(49) has genus 1 = elliptic curve E: y² + xy = x³ - x² - 2x - 1 (49a1)
- E(Q) = {O, (2,-1)} ≅ Z/2 (rank 0, torsion Z/2)
- Both rational points are cusps
- X_1(49) → X_0(49) by forgetting the generator
- Noncuspidal X_1(49) point → noncuspidal X_0(49) point → contradiction

### Required for Lean formalization
1. **Explicit map** (b,c) → (x,y) ∈ X_0(49) (via Vélu quotient E/⟨P⟩)
2. **Rank-0 proof** E(Q) = Z/2 (by 2-descent on 49a1)
3. **Cuspidality** Both points {O,(2,-1)} are cusps; noncusp Tate params map elsewhere

### Genus comparison
- X_1(49) has genus 69 (Q5294)
- X_0(49) has genus 1 (elliptic curve!)
- The quotient map has degree [Γ_0(49):Γ_1(49)] = φ(49)/2 = 21

### Q5297 dispatched for explicit map computation.
