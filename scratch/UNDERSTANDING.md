# FormalGroupW — Weierstrass formal group construction

## Status: COMPLETE (0 sorry, 0 custom axiom)
Commit: 67a7e09 (2026-06-25)
Build: verified clean via lake env lean

## What it proves
- formalGroupLaw W : MvPowerSeries (Fin 2) R — the formal group law
- F(0,0) = 0 (constantCoeff)
- coeff_X(F) = 1 (lin_coeff_X)
- coeff_Y(F) = 1 (lin_coeff_Y)

## Infrastructure built
- 3 divisibility proofs (addX/Y/Z via domain proof + universal ring transport)
- Full naturality chain (formalUCoeff_map → formalW_map → formalAddXYZ_map)
- Coefficient extraction via coeff_{(3,0)} of (X₀-X₁)³·q = constantCoeff(q)
- normalizedAddY_constantCoeff = 1 (CAS-verified, sign bug fixed from -1)

## Downstream files (all 0 sorry)
- FormalNsmulDirect.lean: tangent [n] = n (bypasses FormalGroup.assoc)
- FormalGroupWiring.lean: connects FormalGroupW → FormalNsmulDirect
- FormalGroupW_Coefficients.lean: extraction infrastructure

## Path to Mazur mainline
FormalGroupW → FormalNsmulDirect → tangent bridge → separability → Torsion.lean
Remaining real sorries: FormalBridge(1) + SeparabilityCore(1) + Torsion(3) = 5
