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
FormalGroupW -> FormalNsmulDirect -> tangent bridge -> separability -> Torsion.lean
Remaining real sorries: SeparabilityCore(1) + Torsion(3) = 4

## SEAM1 Sorry Status (2026-06-26)

### FormalBridge sorry: CLOSED (commit 7aaef13)
preΨ_deriv_ne_zero_at_nontorsion_root now delegates to SeparabilityCore.
The extra hcurve/hY hypotheses were unused.

### SeparabilityCore sorry: 1 remaining (n >= 4 rootwise separability)
n = 3 base: PROVEN (Bezout certificate, Res = -81*Delta^2)

### New infrastructure
- SeamE1_EvenDescent.lean (0 sorry): divisor of squarefree poly is squarefree;
  rootwise separability descends via even factorization preΨ(2k) = preΨ(k) * cof
- SeamE1_CofactorNonzero.lean (WIP): Somos-based proof that cofactor != 0 at
  roots of preΨ(k) when Psi3(x) != 0. Math verified, Lean tactic issues remain.

### Mathematical analysis
- Even n = 2k at roots of preΨ(k): handled by IH + cofactor nonvanishing
  - Psi3 != 0 case: 2*Psi3*pe(k-2)^2 = 0 contradiction (char != 2)
  - Psi3 = 0 case (3|k): Res(Psi3, Psi2Sq^4+preP4^2) = 16*Delta^8 != 0
- Even n at cofactor roots: OPEN (needs cofactor separability or dual-number proof)
- Odd n: reduces to even 2n via divisibility descent
- Best approach per ChatGPT: dual-number no-infinitesimal-kernel proof (all-at-once)
