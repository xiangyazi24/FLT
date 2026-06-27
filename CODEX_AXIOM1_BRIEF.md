# CODEX Brief: Axiom 1 (Weil Pairing) Scaffold

## Task
Formalize Weil pairing infrastructure to discharge `weil_pairing_primitive_root` axiom in `FLT/Assumptions/MazurProof/Axioms.lean`.

## Axiom Statement (current)
```lean
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

## Goal
Replace axiom with theorem: produce a complete (or well-structured sorry-scaffolded) proof that:
- If E[m] is fully rational, then ℚ contains a primitive m-th root of unity

## Mathematical Backbone
1. **Weil Pairing**: bilinear, non-degenerate map E[m] × E[m] → μ_m (m-th roots)
   - If E[m] rational → Galois acts trivially
   - Determinant of Galois action on E[m] fixes μ_m
   - Therefore μ_m ⊆ ℚ

2. **Key Theorems Needed**:
   - Weil pairing definition + properties (non-degeneracy, bilinearity)
   - Galois descent (fixed-points ↔ Galois action)
   - Determinant extraction from matrix representation

## Build-Out Strategy
### Phase 1: Divisor Theory & Pairing Definition (~2000 LOC)
- Divisor.lean: formal divisors on elliptic curves
- WeilPairingDef.lean: define the pairing via Tate twist or standard formula
- Test on simple cases (m=2)

### Phase 2: Non-degeneracy & Galois (~2000 LOC)
- WeilPairingNondegen.lean: prove non-degeneracy for generic E[m]
- GaloisAction.lean: formalize Galois action on E[m], extract determinant
- LiftingTheorem.lean: connect rational m-torsion → fixed-point criterion

### Phase 3: Assembly (~500 LOC)
- WeilPairingThm.lean: assemble phases into final theorem
- Case work on small m (2, 3, 4) to verify scaffold
- Name remaining sorries precisely (e.g., `sorry_mordell_weil_structure`, `sorry_cohomology_vanishing`)

## Acceptable Outcomes
- **Goal (A)**: Complete 0-sorry proof (unlikely but possible for m ≤ 4)
- **Goal (B)**: Compiled scaffold with 3-5 major sub-theorems + named sorries on hardest obstacles
- **Fallback**: Clear roadmap file naming every sub-obligation + evidence that the obstacles are deep-but-finite

## Constraints
- Do NOT try to discharge `mordell_weil_fg` axiom or prove E[m] is finite — those are separate axioms
- Focus purely on the pairing + Galois descent logic
- Keep divisor theory minimal (reuse Mathlib where possible; custom definitions only for missing pieces)

## Files to Reference
- FLT/EllipticCurve/: existing EC machinery
- FLT/Assumptions/MazurProof/Axioms.lean: context + axiom site
- scratch/Bridge1*.lean: division polynomial work (may relate to pairing computation)

## Entry Point
Start in `FLT/Assumptions/MazurProof/WeilPairing.lean` (create new file):
- Import Mathlib divisor theory, Galois modules, torsion API
- Define or import Weil pairing
- Build theorem: `theorem weil_pairing_gives_primitive_root ...`

## Success Criteria
- File compiles (even with named sorries)
- Theorem statement matches `weil_pairing_primitive_root` signature
- No axiom calls except `mordell_weil_fg` and other legitimate axioms
- Clear comment on each sorry naming the mathematical obstacle

---

**Effort cap**: None (this is a hard problem; grind until terminal condition)
**Timeline**: Run until compiled scaffold or rigorous proof-of-infeasibility
