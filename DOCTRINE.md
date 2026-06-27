# FLT FLATdec Automode — Phase 2→1 Campaign

## Goal
Complete QuarticD d=2-7 verification + integration, then push Mazur torsion-bound axioms (Axiom 1: Weil pairing).

## Current State
- QuarticD d=2-7: all 6 proofs committed (0 sorry), in scratch/
- Axioms.lean: +569 lines (Weil pairing + two invariant factor tools), uncommitted
- lakefile.toml: scratch lib added (to enable QuarticD + Bridge1* compilation)
- Bridge1*: three new files (division polynomial exploration)

## Candidate Avenues (ranked by promise)

### (a) PRIMARY: Full stack — compile verification → integrate → Axiom 1
1. **Compile & verify**: uisai2 `lake build` → check QuarticD + Axioms.lean 569L + Bridge1* all green
   - Terminal: all compile OR concrete error in one piece
2. **If green**: commit Axioms + lakefile changes → map QuarticD to Axiom 4 roles → decide scratch vs FLT/Assumptions/ location
3. **Integrate QuarticD**: either move to FLT/Assumptions/MazurProof/ or keep in scratch with explicit reference
4. **Pivot to Axiom 1 (Weil pairing)**: draft/discharge using new Axioms.lean infrastructure
   - Win condition: a Lean theorem discharging weil_pairing_primitive_root for a concrete case OR a clear design for the general discharge
   - Fallback within this avenue: switch to Axiom 2 (two invariant factors) if Axiom 1 proves harder-than-expected

### (b) PIVOT: Compile survives, but Axiom 1 stalls → prioritize Axiom 2-3 first
- Axiom 2 (torsion structure): pure group theory, infrastructure already in 569L new code
- Or Axiom 3 (no order ≥17): hard but strategy exists in UNDERSTANDING.md
- Terminal condition: successfully discharge ONE of {Axiom 2, Axiom 3} or hit rigorous proof-of-infeasibility

### (c) FALLBACK: Compile fails with critical errors → debug and fix
- If lakefile/import issues: simplify to a minimal compilable state
- If Axioms.lean 569L is malformed: revert to prior stable version, extract working pieces
- If QuarticD has subtle issues: isolate to one file, verify individually
- Terminal: get to a GREEN compile state (even if partial), then re-assess avenue ranking

## Known Blockers & Mitigations
- **uisai2 might lack Lean setup**: fallback to uisai1 or compile on local mini if context/disk allows
- **569L new code may have type-level errors**: revert only that block, keep rest of Axioms.lean
- **QuarticD may need specific imports/lemmas**: check each d's references, add imports as needed
- **Axiom 1 (Weil pairing) may be deep**: prepared to dispatch to ChatGPT Pro for design audit or sub-agent for Lean scaffolding

## Victory Conditions
- (a): Axiom 1 has a theorem discharge strategy + at least one test case compiled
- (b): ONE axiom discharged (theorem, not sorry), OR all avenues hit terminal failure with documented verdict per avenue
- (c): Compile green for the whole project (even if QuarticD/Bridge1* remain in scratch as exploratory)

## Failure Modes to Catch
- Do NOT estimate time or declare "this will take X hours" — grind until terminal condition
- Do NOT ask "should I do X?" — decide by: (1) build test, (2) source read, (3) ChatGPT, (4) best judgment, then push
- Do NOT switch avenues without terminal verdict on current one
- Do NOT stop on "this is hard" or "needs fresh context" — dispatch to sub-agent or ChatGPT if personal context exhausted
- Do NOT pre-commit to Axiom 1 if Axiom 2 emerges as higher leverage — update doctrine, keep grinding

---

**Doctrine version: 2026-06-26, initial draft**
**Last updated: [during run]**
