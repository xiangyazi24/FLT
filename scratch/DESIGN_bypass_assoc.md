# Design: Bypass FormalGroup.assoc for the tangent bridge

## Key insight (2026-06-25)

FormalGroup R requires associativity. But the tangent bridge only needs:
- F(0,0) = 0
- coeff_X(F) = 1
- coeff_Y(F) = 1

The proof chain formalNsmul_coeff_one → separability does NOT use assoc.

## Plan

1. Define formalNsmul_W directly from formalGroupLaw W (no FormalGroup wrapper):
   formalNsmul_W W 0 = 0
   formalNsmul_W W (n+1) = subst ![formalNsmul_W W n, X] (formalGroupLaw W)

2. Prove coeff 1 (formalNsmul_W W n) = n using only:
   - formalGroupLaw_constantCoeff (= 0)
   - formalGroupLaw_lin_coeff_X (= 1)
   - formalGroupLaw_lin_coeff_Y (= 1)

3. Use this for the tangent bridge → separability

## Sign bug fix needed

normalizedAddY_constantCoeff = 1, NOT -1.
CAS verified: negAddY deg-3 = -(X0-X1)^3, so formalAddY = (X0-X1)^3 * (1+...)

Changes needed:
- normalizedAddY_constantCoeff: -1 → 1
- normalizedAddY_isUnit: isUnit_one.neg → isUnit_one
