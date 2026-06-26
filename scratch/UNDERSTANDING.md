# SEAM1 Separability — Session Handoff (2026-06-26)

## FormalGroupW: COMPLETE (0 sorry, commit 67a7e09)
The formal group law F(t₁,t₂) = t₁+t₂+O(2) is fully proved:
- 3 divisibility proofs (addX/Y/Z via domain + universal ring transport)
- Full naturality chain
- normalizedAddY_constantCoeff = 1 (sign bug fixed)
- formalGroupLaw: constantCoeff=0, lin_coeff_X=1, lin_coeff_Y=1
- Olean built at .lake/build/lib/lean/scratch/FormalGroupW.olean

## FormalNsmulDirect: COMPLETE (0 sorry, commit 1061bdc)
Tangent [n]'(0) = n. Bypasses FormalGroup.assoc.

## FormalBridge: COMPLETE (0 sorry, commit 7aaef13)
Wired to SeparabilityCore.

## SeparabilityCore: 4 sorry (commit fde7314)
Strong induction decomposed into 4 precise sub-sorries:

### L135: Ψ₃=0 cofactor nonvanishing
On the 3-torsion stratum, need cofactor ≠ 0. ChatGPT dm1 Q813 says:
use identity preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄)·Ψ₃, so at Ψ₃=0:
preΨ₄ = -Ψ₂Sq². Then cofactor becomes explicit monomial × 2.
TRACTABLE if (2:K) ≠ 0.

### L177: Cofactor-root case (Even Case B)
When cofactor(x) = 0 but preΨ(m+3)(x) ≠ 0. Needs cofactor'(x) ≠ 0.
ChatGPT dm2 Q814: bypass as named axiom, close other cases first.
HARD — might need dual-number/differential argument.

### L208: n=4 base case
Pure computation: Bézout certificate for preΨ₄ separability.
CAS: Res(preΨ₄, preΨ₄') = 2⁹·Δ⁵.
TRACTABLE — generate Bézout cofactors by sympy.

### L219: Odd n ≥ 5
ChatGPT dm3 Q819: EDS descent doesn't work for odd case.
Needs differential identity v·Φ·ψ'+n·Ω ≡ 0 (mod ψ) OR dual-number bridge.
Ω_n is NOT in Mathlib (TODO). Would need to define it.
HARD — requires new infrastructure (Ω_n or dual-number tangent).

## Recommended next steps
1. Close n=4 via Bézout certificate (pure CAS computation)
2. Close Ψ₃=0 case using preΨ₄=-Ψ₂Sq² identity
3. Leave cofactor-root (L177) as named axiom
4. For odd n: define Ω_n + prove polynomial identity, OR dual-number bridge

## Torsion.lean: 3 sorry (downstream, depends on SEAM1)

## Update (2026-06-26 02:30)

### Odd-via-even reduction CONFIRMED (ChatGPT dm4 Q848)
For odd n with (2:K) ≠ 0:
- Double root of preΨ'(n) → double root of preΨ'(2n) (via factorization + product rule)
- But preΨ'(2n) separable by even theorem → contradiction
- Only char 2 needs separate treatment

### preΨ₄ = -Ψ₂Sq² at Ψ₃ roots (ChatGPT dm1 Q845)
Identity: preΨ₄ + Ψ₂Sq² = (6X²+b₂X+b₄)·Ψ₃, provable by ring.
Simplifies cofactor on Ψ₃=0 stratum.

### Sub-agents active on L135 (Ψ₃=0) and L223 (odd via even)
