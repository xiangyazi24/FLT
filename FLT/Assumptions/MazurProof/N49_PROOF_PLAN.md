# N49 Proof Plan — 2026-08-18

## Goal
Prove `no_raw_order49_tate_obstruction`: H_49(b,c) = 0 has no rational root with b ≠ 0.

## Bihomogeneous Parity Chart Analysis (mod 2)

Define H̃(p,q,r,s) = q^98 · s^147 · H_49(p/q, r/s) ∈ Z, where b=p/q, c=r/s in lowest terms.

### Computed edge data
- h_{0,0} = 0
- h_{98,0} = -1 (odd)
- Σ_j h_{0,j} = H_49(0,1) = 1 (odd)
- Σ_j h_{98,j} = -1 (odd, leading b-coeff of H_49(b,1))
- Σ_i h_{i,0} = H_49(1,0) = -1 (odd)
- Σ_i h_{i,147} = 1 (odd, leading c-coeff of H_49(1,t))
- H_49(1,1) = -1 (odd)

### Chart status (9 charts, need all nonzero mod 2)

| # | (p,q) mod 2 | (r,s) mod 2 | Value mod 2 | Status |
|---|-------------|-------------|-------------|--------|
| 1 | (0,1) | (0,1) | h_{0,0} = 0 | **ZERO — needs Newton-face** |
| 2 | (0,1) | (1,0) | h_{0,147} | **UNKNOWN** |
| 3 | (0,1) | (1,1) | Σ_j h_{0,j} = 1 | EXCLUDED |
| 4 | (1,0) | (0,1) | h_{98,0} = 1 | EXCLUDED |
| 5 | (1,0) | (1,0) | h_{98,147} | **UNKNOWN** |
| 6 | (1,0) | (1,1) | Σ_j h_{98,j} = 1 | EXCLUDED |
| 7 | (1,1) | (0,1) | Σ_i h_{i,0} = 1 | EXCLUDED |
| 8 | (1,1) | (1,0) | Σ_i h_{i,147} = 1 | EXCLUDED |
| 9 | (1,1) | (1,1) | H_49(1,1) = 1 | EXCLUDED |

### Remaining work
1. **Compute h_{0,147} and h_{98,147} mod 2** — needs bivariate H_49 or Wolfram computation
2. **Newton-face argument for chart #1** — the (v_2(b)>0, v_2(c)>0) case where H̃≡0 mod 2
3. **Newton-face for any UNKNOWN charts that turn out 0** (charts #2 and #5)

## Composition Shortcut (Q5276)
preΨ'_49(0) = D̂_7(Φ_7(0), ΨSq_7(0)) · F_7

This avoids the 48-step recursion but does NOT shortcut the arithmetic obstruction proof.
The composition reformulates the SAME condition geometrically (7P is a 7-torsion point).
Useful for computation and possibly for a Lean certificate, not for the proof itself.

## Alternative approaches (all require global arithmetic)
- Modular curve: prove X_1(49)(Q) = {cusps} directly (essentially Mazur's theorem for this specific level)
- MW sieve: need J(X_1(49))(Q) structure (extremely hard, genus > 100)
- Descent on H_49 = 0 curve (potentially tractable if H_49 has good descent data)

## Edge Structure (Q5282)

Remarkably simple edges:
- Left edge (b^0 coeff): H_49 restricted to b=0 is just **c^133** (single monomial)
- Top edge (c^147 coeff): coeff of c^147 is just **b^7** (single monomial)  
- Right edge (b^98 coeff): coeff of b^98 is **-1** (constant)

Corner coefficients:
- h_{0,147} = 0 (no b^0·c^147 term!)
- h_{98,0} = -1
- h_{98,147} = 0 (no b^98·c^147 term!)

The three zero-mod-2 charts that need Newton-face:
1. (0,0): v_2(b)>0, v_2(c)>0 — approach: use left edge c^133 as anchor
2. (0,∞): v_2(b)>0, v_2(c)<0 — approach: use left edge c^133 and top edge b^7
3. (∞,∞): v_2(b)<0, v_2(c)<0 — approach: use right edge -1 and top edge b^7

## Newton-face strategy for zero charts

For chart (0,0) [v_2(b)>0, v_2(c)>0]:
Write b=2^α u, c=2^γ v with u,v odd, α,γ ≥ 1.
The 2-adic valuation of h_{i,j} b^i c^j = h_{i,j} 2^{αi+γj} u^i v^j.
The minimum valuation monomial determines the initial form.
The left edge c^133 at (i,j)=(0,133) has val = 133γ.
The right edge -1 at (i,j)=(98,0) has val = 98α.
Interior monomials have val ≥ min boundary.
If 133γ ≠ 98α, the unique minimum-valuation term is nonzero mod 2.
If 133γ = 98α, need to check the initial form on the Newton face.
Since gcd(133,98) = 7, this happens only when α/γ = 133/98 = 19/14.

## ChatGPT questions pending
- Q5271: N49 admissible change
- Q5285: how to use composition shortcut
- Edge coefficient computation: COMPLETE (Q5282)
