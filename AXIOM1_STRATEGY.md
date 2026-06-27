# Axiom 1 (Weil Pairing) — Discharge Strategy

## Axiom Statement
```lean
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

If all `m`-torsion points of E are rational, then ℚ contains a primitive m-th root of unity.

## Mathematical Background
1. **Weil pairing**: A bilinear, non-degenerate pairing on E[m] × E[m] → μ_m (m-th roots of unity)
2. **Galois action**: If all E[m] points are rational, Galois acts trivially on E[m]
3. **Determinant of Galois**: The determinant of the Galois action on E[m] must act trivially on μ_m
4. **Consequence**: The Galois action fixes μ_m, so μ_m ⊆ ℚ

## Discharge Path (Sketch)

### Phase 1: Weil Pairing Definition (est. 3000 LOC)
- Import/define divisor theory on elliptic curves
- Define the Weil pairing: E[m] × E[m] → μ_m
- Prove non-degeneracy and bilinearity
- Reference: Silverman's Arithmetic of EC or Milne's notes

### Phase 2: Galois Action (est. 1500 LOC)
- Define Galois action on E[m]
- Prove that full rationality → trivial Galois action
- Extract the determinant representation

### Phase 3: Closure (est. 500 LOC)
- Show: trivial action on E[m] + non-degeneracy → μ_m ⊆ ℚ
- Use Galois descent and fixed-point arguments

## Current State
- ✅ Axioms.lean has framework: `HasFullRationalTorsion`, `IsPrimitiveRoot`, axiom skeleton
- ❓ Weil pairing infrastructure: NOT yet in Axioms.lean 569L (check Bridge1*.lean for related work)
- ❓ Galois machinery: May exist in Mathlib or FLT/EC/ modules

## Next Immediate Actions
1. **Compile verification**: confirm scratch/Bridge1*.lean compiles (may contain EC/divisor infrastructure)
2. **Audit existing code**: grep for `pairing`, `divisor`, `Galois` in FLT/ to find existing machinery
3. **Route decision**:
   - If Bridge1* has divisor/pairing infrastructure → integrate into Axiom 1 discharge
   - If not → either build from Mathlib or dispatch to Codex/ChatGPT for skeleton

## Risk Mitigation
- **If Weil pairing is not in Mathlib**: high-difficulty, dispatch to Codex Pro for the full 3000-line infrastructure + interactive proving
- **If Galois machinery is weak**: pair with ChatGPT for a focused theory audit (which Mathlib lemmas exist, which gaps)

## Terminal Conditions
- **Success**: A Lean theorem `weil_pairing_primitive_root_of_something` that closes the axiom for a concrete case (e.g., m=2,3,4)
- **Partial**: A compiled scaffold with 2-3 major theorems and named sub-sorries
- **Failure**: After serious dispatch attempts, Weil pairing requires too much infrastructure not in Mathlib → defer to next cycle, move to Axiom 2 instead
