# ω_n / Projective Bridge Design — Rounds 1-4 Summary

## Architecture (settled R1-R4)
Path A: define ω_n + projective formula [n]P=[φ_n:ω_n:ψ_n]

## Seams
- A/B: ω_n definition + projective formula (MAIN EFFORT, new construction)
- C: φ_n(P)≠0 at ψ_n(P)=0 — ALREADY PROVEN (no_adjacent_preΨ_zero, KeystoneCoprimality.lean L450)
- D: ω_n(P)≠0 — from C + equation at Z=0 (ω²=φ³)
- E: local parameter t=[n]Pε = -φ_n·ψ_n/ω_n over K[ε]
- F: connect to TangentO / preΨ'_deriv_ne_zero / separability

## Key findings
- Projective formula is NOT circular (pure polynomial identity, doesn't need separability)
- Adjacent nonvanishing already proved (no_adjacent_preΨ_zero, requires h4:(4:k)≠0)
- ω_n definition needs quotient/divisibility: 2·ψ_n·ω_n = ψ_{2n} - ψ_n²·(a₁φ_n+a₃ψ_n²)
- Mathlib has EDS complement (complEDS₂/normEDS_dvd_normEDS_two_mul) for ψ_n|ψ_{2n}
- char-zero prototype: ~600-1200 lines; full: ~1000-2500
- Biggest risk: ω_n normalization + projective formula proof
- Jacobian.addXYZ/dblXYZ work over CommRing (verified), but no packaged group law over K[ε]

## Design rounds saved
- R1 (Q174): route ranking, first-order jet recommended over full formal group
- R2 (Q176): no OJetPoint wrapper, use TangentO; critical = Ω_n; chain via projective local param
- R3 (Q177): Path A best; Path C raw Jacobian collapses to Path A; φ_n≠0 from adjacent; ω_n≠0 from Z=0 eq
- R4 (Q180): stress test passed; not circular; adjacent nonvanishing exists; size 600-2500; risk=ω_n normalization
- R5 (Q__): atom decomposition (in flight)

## R5 (Q181): Atom decomposition
- 8 atoms identified (0-7 + assembly)
- ATOM 1: use complEDS₂ for ψ_{2n}/ψ_n (NOT polynomial division)
- ATOM 2: ω_n = C(C(2⁻¹)) * (ψTwoMulQuot - ψ_n * (a₁φ+a₃ψ²)) in char-zero
- ATOM 3/4: projective formula [n]P=[φ_n:ω_n:ψ_n] — MAIN EFFORT
- ATOM 5-7: ω≠0, local param, coeffε bridge — moderate/mechanical

## R6 (Q183): Final audit — key findings
- Addition identity: addXYZ(P, R_m) = ψ_{m-1} • R_{m+1} (polynomial, not point-level)
- ψ_{m-1} scalar can vanish → prove as coordinate-ring identity, not point equivalence
- Doubling: dblXYZ(R_m) = R_{2m} (cleaner, no scalar)
- Z-component of doubling = normalization check for ω_m
- TRAP: don't use addXYZ identity at points where ψ_{m-1}=0
- CAS-verify componentwise: addX-ψ_{m-1}²φ_{m+1} ∈ (F_W), addY-ψ_{m-1}³ω_{m+1} ∈ (F_W)

## Implementation order (post-design)
1. Atoms 0-2 (ω_n definition) — sub-agent F in flight
2. CAS-verify addition/doubling identities (sympy on uisai2)
3. ATOM 3/4 Z-component (addZ = ψ_{m-1}ψ_{m+1}, exact from φ definition)
4. ATOM 3/4 X/Y components (coordinate-ring mod F_W, the hard polynomial identities)
5. ATOM 5 (ω≠0 from φ≠0 + Z=0 equation)
6. ATOM 6-7 (dual-number local parameter + coeffε bridge)
7. ATOM 8 (assembly → separability)
