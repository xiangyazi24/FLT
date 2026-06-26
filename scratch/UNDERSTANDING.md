# FormalGroupW — Weierstrass formal group construction

## Goal
Build W.formalGroupLaw : MvPowerSeries (Fin 2) R with:
- F(0,0) = 0
- coeff_X(F) = 1
- coeff_Y(F) = 1

This feeds into FormalNsmulDirect (tangent [n] = n) → separability → Torsion.lean.

## Current state (2026-06-25)

### DONE (0 sorry)
- formalW, formalU definitions + functional equations
- formalPoint, formalPointMv, formalPointMv_equation
- formalDelta, deltaQuot, deltaQuotQuot factorization
- X_sub_X_regular (non-zero-divisor)
- diagDiffQuot_formalW
- formalAddZ_mul_ww (addZ identity)
- formalAddZ_dvd_cube_of_noZeroDivisors (domain proof)
- formalAddX_dvd_cube_of_noZeroDivisors (domain proof via addX_eq')
- formalAddY_dvd_cube_of_noZeroDivisors (domain proof via negAddY_eq')
- formalUCoeff_map, formalU_map, formalW_map (naturality chain)
- formalPointMv_map_comp, formalAddXYZ_map (projective naturality)
- formalAddX_dvd_cube, formalAddY_dvd_cube, formalAddZ_dvd_cube (transport)
- univWeierstrassCurve, univEval, univEval_map
- normalizedAddX/Y/Z definitions, formalGroupLaw definition

### 4 SORRY remaining
1. normalizedAddY_constantCoeff = 1 (sign fixed from -1)
2. formalGroupLaw_constantCoeff = 0
3. formalGroupLaw_lin_coeff_X = 1
4. formalGroupLaw_lin_coeff_Y = 1

### Proof strategy for remaining sorries
- Use coefficient extraction: coeff_{(3,0)} of (X₀-X₁)³·q = constantCoeff(q)
- Raw fact: coeff_{(3,0)}(formalAddY) = 1 (CAS verified)
- Infrastructure in FormalGroupW_Coefficients.lean: coeff_subst_X, coeff extraction chain

### Downstream files
- FormalNsmulDirect.lean: 0 sorry (tangent = n, bypasses FormalGroup.assoc)
- FormalGroupWiring.lean: scaffold connecting FormalGroupW → FormalNsmulDirect
- SeamE1_FormalBridge.lean: 1 sorry (formal group → separability bridge)
- SeamE1_SeparabilityCore.lean: 1 sorry (n≥4 case — use formal group route, not EDS descent)
