# Axiom 4 + QuarticD Integration Plan

## Axiom 4 Statement
```
no_Z2_cross_Zn_forbidden (E : WeierstrassCurve ℚ) [E.IsElliptic] :
  ¬∃ f : ZMod 2 × ZMod 12 →+ (E⁄ℚ).Point, Function.Injective f  [and similar for n=10,14,16]
```

Proof strategy (from ROADMAP.md):
1. Parametrize ALL curves with Z/2 × Z/n torsion (Kubert/Tate normal form)
2. Full 2-torsion imposes discriminant-square condition
3. This defines an obstruction curve C over ℚ
4. Show C(ℚ) consists only of degenerate/cuspidal points
5. Contradiction: if E had Z/2 × Z/n, we'd get a non-degenerate point on C

## QuarticD Role
QuarticD d=2-7 prove: `s^4 + d^2·s^2 - d^4 = t^2` has no integer solutions (with gcd(s,d)=1).

These are potentially:
- The obstruction curves themselves, OR
- Auxiliary squeezed forms of those curves (via parametrization)

Current evidence: DescentObstruction.lean mentions "quartic obstruction y² = -x⁴ + ..." (not yet matched to d=2-7)

## Integration Tasks

### Task 1: Map QuarticD d=2-7 to Axiom 4's {n=10,12,14,16}
- [ ] QuarticD2: maps to n = ? (check equation form)
- [ ] QuarticD3: maps to n = ?
- [ ] ... (and so on)
- [ ] Document: "d ↔ n" mapping with equation cross-reference

### Task 2: Connect Kubert Parametrization to QuarticD
- [ ] Read Kubert normal form for curves with full 2-torsion + Zn point
- [ ] Show how parametrization simplifies to quartic form s^4 + d²s² - d⁴
- [ ] Document the reduction: Kubert family → quartic obstacle

### Task 3: Create FLT/Assumptions/MazurProof/QuarticObstruction.lean
```lean
-- Import relevant QuarticD proofs from scratch
import scratch.QuarticD2
import scratch.QuarticD3
...

-- Define: "the Kubert parametrization for [n] reduces to quartic_no_sol_d[n]"
theorem no_degenerate_point_on_kubert_n12_via_quartic : ... :=
  quartic_no_sol_d2 ...  -- or whichever d maps to n=12

-- Assemble all n ∈ {10,12,14,16}
theorem no_Z2_cross_Zn_by_kubert_quartic : 
  ∀ n ∈ [10,12,14,16], ¬∃ f : ZMod 2 × ZMod n →+ ..., ... := by
    ...
```

## Decision: Scratch vs Integrated
- **QuarticD**: stay in scratch/ (exploratory, complete proofs)
- **QuarticObstruction.lean** (NEW): created in FLT/Assumptions/MazurProof/, imports scratch.QuarticD*, assembles Axiom 4

Reasoning:
- scratch/ is for development/exploration (we have 0 sorry, fully correct)
- Main proof structure should be in FLT/Assumptions/ so the axiom discharge is visible + tracked
- Clean separation: scratch = raw materials, Assumptions = the structural assembly

## Hard Blockers to Watch
1. **Parametrization details**: Kubert normal form may require deep EC theory
   → Dispatch to Codex/ChatGPT if needed
2. **Equation matching**: verifying QuarticD d matches the right obstruction curve
   → Use CAS (SageMath/SymPy) to check: does Kubert family → s^4+d²s²-d⁴?
3. **Non-degeneracy witness**: the final contradiction needs explicit point
   → May require number-theoretic computation (rank 0 verification for LMFDB curves)

## Next Immediate Steps
1. **Grep & document**: find exact obstruction curve equations (scratch/DescentObstruction.lean + FLT/Assumptions)
2. **Map test**: pick one (e.g., d=2 ↔ n=12) and verify by hand/CAS
3. **Dispatch or DIY**: if mapping is clear → write QuarticObstruction.lean directly; else dispatch to Codex
4. **Compile**: verify new file compiles, axiom calls are correct

---

**Effort**: Medium—requires careful matching but mostly assembly/refactoring, not deep new proofs
**Timeline**: Complete mapping + draft QuarticObstruction.lean in this cycle
