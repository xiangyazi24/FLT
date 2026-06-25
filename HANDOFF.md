# Session Handoff — 2026-06-24 Mazur FLT Formalization

## What was accomplished this session

### Torsion.lean: 8 → 5 sorries (verified green, 8599 jobs)
- h4 (4≠0): CLOSED via CharZero threading (f929c76)
- hc3 (Ψ₃≠0): CLOSED via Mathlib Ψ₃_ne_zero (f929c76)
- hψ_ne (ψ_m≠0): CLOSED via coordinate-ring degree argument (ee3af21)

### SEAM1: bridge-1 CLOSED, bridge-2 = 1 sorry
- Bridge1Even: 0 sorry (eac5bdf) — EDS closed-form odd+even cases fully proved
- Bridge1HCD: 0 sorry (2723e94) — preΨ₄²+4Ψ₃³=0 at Ψ₂Sq-root
- Bridge-1 wired into SeamE1_Core (4e49710) — preΨ'_root_Ψ₂Sq_ne DISCHARGED
- Bridge-2 (dual_root_implies_tangent_zero): 1 named sorry remains
- SeamE1_Core: 1 sorry (bridge-2 only). scratch.SeamE1 builds 3012 jobs.

### ω_n projective bridge infrastructure
- OmegaDivPoly.lean: 0 sorry (4c2c69b) — ψTwoMulQuot + ωProto + normalization
- ProjectiveFormula.lean: 0 sorry (ff5cc53) — addZ + dblZ Z-components
- ProjectiveFormulaXY.lean: m=1 proved, m=2 framework (1 sorry)
- 6-round ChatGPT design brainstorm complete (R1-R6), architecture settled
- Design doc: scratch/DESIGN_omega_projective_bridge.md

### Other
- exists_nonsingular: 0 sorry (b45feae) — sub-D step 1
- ψ_ne_zero_of_charZero: 0 sorry (ee3af21)
- Proactive context management via sub-agents: validated + banked

## What needs to happen next

### Priority 1: Close bridge-2 (the last SEAM1 sorry)
The deep crux = general-n preΨ'_n separability = derivative nonvanishing at roots.
Two sub-routes converging:

**Route A (general projective formula):**
- ATOM 3/4 X/Y components need coordinate-ring identities mod F_W
- Proof pattern: CAS-compute cofactor Q, then `rw [AdjoinRoot.mk_eq_zero]; exact ⟨Q, by ring⟩`
- addX cofactors CAS-verified for m=2..8 (Q₂=3 terms...Q₈=15160)
- dblX/dblY cofactors also verified
- Needs: per-m or general-m coordinate-ring Lean proofs
- Once projective formula proved → ATOM 5 (ω≠0 from φ≠0) → ATOM 6 (local param) → ATOM 7 (coeffε) → assembly

**Route B (bypass via SeamE1_FormalBridge):**
- preΨ'_deriv_ne_zero_at_nontorsion_root (= separability) already reduced to single sorry
- n=3 case proved (074cd1c)
- Closes if the projective formula proves general-n separability

### Priority 2: sub-D wiring (Torsion.lean L175)
- exists_nonsingular ready; bridge-1 ready
- Needs: IsSepClosed → IsAlgClosed check (dm4 Q asked)
- Should drop Torsion.lean from 5 → 4 sorries

### Priority 3: per-n Bezout certificates (fallback for small n)
- n=3: done; n=5: cofactors computed (216+236 terms); n=4,6,8: dm1 computing
- Not tractable for n≥11 (cofactors too large)
- Useful as building blocks even if general theorem is the main path

## Build state on uisai2
- Branch: ai-scratch
- Latest commit: f9d83ad (CHANGELOG)
- Canonical Torsion.lean: 5 sorries, 8599 jobs green
- scratch.SeamE1: 1 sorry (bridge-2), 3012 jobs green
- scratch.Bridge1Even: 0 sorry
- scratch.OmegaDivPoly: 0 sorry
- scratch.ProjectiveFormula: 0 sorry
