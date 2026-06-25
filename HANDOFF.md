# Session Handoff — 2026-06-24 FINAL (Mazur FLT Formalization)

## Session achievements: Torsion.lean 8 → 3 sorries

### Closed (verified green, 8601 jobs)
- h4 (4≠0): CharZero threading (f929c76)
- hc3 (Ψ₃≠0): Mathlib Ψ₃_ne_zero (f929c76)
- hψ_ne (ψ_m≠0): coordinate-ring degree argument (ee3af21)
- sub-D root realization: IsSepClosed→IsAlgClosed→bridge-1→assembly (be32fe3)
- SEAM1 bridge-1 coprimality: CLOSED + wired (4e49710)

### Remaining 3 sorries (all NOT OURS)
- L52 n_torsion_finite (David Angdinata)
- L1072 Module.Finite (depends on above)
- L1133 galoisRep (data sorry)

## SEAM1 bridge-2: the ONE remaining mathematical sorry

`dual_root_implies_tangent_zero` in SeamE1_Core = general-n preΨ'_n separability.

### Architecture (6-round ChatGPT brainstorm, settled)
Path: ω_n projective formula + local parameter + d[n]|_O = n identification.

### What's built (all 0-sorry)
- OmegaDivPoly: ψTwoMulQuot (complEDS₂) + ωProto + normalization
- ProjectiveFormula: addZ + dblZ (Z-components)
- ProjectiveFormulaXY: m=1,2 X-component
- Bridge1Even: EDS closed forms (odd+even, all 6 ring identities)
- SeamE1_FormalNsmul: formalNsmul_coeff_one ([n]'(0)=n)
- SeamE1_DualUnit: ψ₂-unit at non-2-torsion
- SeamE1_FormalBridge: decomposition + n=3 case

### The critical next step (for next session)
**The direct addX proof needs 5 inputs, not 4.** CAS verified (dm1 Q288):
1. hω: `W.two_mul_ψ_mul_ωProto m` (PROVED, OmegaDivPoly)
2. heven: `W.ψ_even m` (MATHLIB)
3. hφ: `WeierstrassCurve.φ` definition (MATHLIB)
4. hFW: `AdjoinRoot.mk_self` (MATHLIB)
5. **Hmiss**: Ward invariant relation = `mk_invariant_descended` (PsiInvariant.lean, IN REPO)

With all 5, `2·(addX - ψ_{m-1}²·φ_{m+1})` reduces to 0 mod F_W. Implementation: `rw [AdjoinRoot.mk_eq_zero]; exact ⟨cofactor_expressed_via_5_inputs, by ring⟩` or `linear_combination`.

After addX general-m closes → addY (similar) → ATOM 5 (ω≠0) → ATOM 6 (local param) → ATOM 7 (coeffε) → assembly → bridge-2 CLOSED → SEAM1 fully 0-sorry.

## Shortcut analysis (all ruled out)
- Per-n Bezout: tractable n≤5, intractable n≥11 ✗
- Torsion counting (rank-2): circular ✗
- Resultant recurrence: no EDS recurrence for resultants ✗
- Function-field route: needs same projective formula ✗
- Direct 4-input proof: needs 5th input (Ward invariant) — FOUND ✓

## Build state on uisai2
- Branch: ai-scratch, latest: 4a264fc
- Torsion.lean: 3 actual sorries, 8601 jobs green
- scratch.SeamE1: 1 sorry (bridge-2), 3012 jobs green
## Update 2026-06-25 (continued session)

### New findings
- ATOM 5 (ω≠0): PROVED (32804ef, 0-sorry)
- addX general-m: ω-elimination proved, ωfree_dvd 1 sorry (sub-agent grinding)
- c₅=0 breakthrough: addX with Ψ₂Sq-Hmiss is an EXACT polynomial identity (no AdjoinRoot needed)
- addY structural obstruction: ω_m² term needs 1/ψ_m → MUST use coordinate ring (polynomial LC impossible)
- Discriminant route: NOT viable for general n (same formal-group content, normalization traps)
- Finite morphism injectivity: NOT a shortcut (finite+nonconstant ≠ unramified)
- Torsion counting: circular
- Function-field: needs same projective formula

### The irreducible gap: tangent bridge
After exhaustive exploration (40+ ChatGPT rounds, 5 alternative routes ruled out):
The tangent bridge = connecting projective local-parameter coefficient to abstract d[n]|_O = n.
This is the CORE CONTENT of the Weierstrass formal group and cannot be bypassed.

### Two legs remaining for bridge-2
1. Projective formula addX/addY (leg 1): ωfree_dvd sub-agent grinding
2. Tangent bridge (leg 2): needs W.formalGroup or equivalent first-order construction

### Verified state on uisai2
- Torsion.lean: 3 actual sorries (all not-ours), 8601 jobs green
- scratch.SeamE1: 1 sorry (bridge-2), 3012 jobs green  
- scratch.Bridge1Even: 0 sorry
- scratch.OmegaDivPoly: 0 sorry
- scratch.ProjectiveFormula: 0 sorry (Z-components)
- scratch.Atom5OmegaNonzero: 0 sorry
- scratch.AddXGeneral: 1 sorry (ωfree_dvd, sub-agent in flight)

## Update 2026-06-25 (late)

### Mathlib FormalGroup discovery
Mathlib has FormalGroup at RingTheory/FormalGroup/Basic.lean (Wenrong Zou).
Same structure as our SeamE1_FormalNsmul.lean. Has additiveFormalGroup.
Our formalNsmul_coeff_one (d[n]=n) is NOT in Mathlib — our contribution.
W.formalGroup instance is NOT in Mathlib — the tangent bridge gap.

### Proven this sub-session
- addX general-m: 0-sorry (fcc5aa4)
- ATOM 5 (ω≠0): 0-sorry (32804ef)
- addY: 6/7 helpers 0-sorry, assembly 1 sorry (sub-agent grinding)

### ChatGPT bridge reliability
Last 2 rounds (~8 questions) ALL returned PENDING (bridge capture failure on Pro long-thinks).
Answers in tabs but git-write not triggering. Need manual paste or bridge fix.

### Remaining for bridge-2
1. addY assembly (1 sorry, sub-agent in flight)
2. Tangent bridge (irreducible, needs W.formalGroup or equivalent)
