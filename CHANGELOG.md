
## 2026-06-24: Bridge1Even -- preΨ'_root_Ψ₂Sq_ne' structure (b3f5814)
- New file: scratch/Bridge1Even.lean (332 lines)
- Main theorem: WeierstrassCurve.preΨ'_root_Ψ₂Sq_ne'
- Proven (0-sorry): eval lemma, odd nonvanishing, odd closed form, helpers, D!=0, main assembly
- Named sorries (5): 1 Bezout cert (known) + 4 even closed form ring identities

## 2026-06-24: ProjectiveFormula -- Z-component projective bridge (ATOM 3a + 3b)
- New file: scratch/ProjectiveFormula.lean
- ATOM 3a (addZ_divPoly_eq): addZ(![C X, y, 1], ![φ_m, ω, ψ_m]) = ψ_{m-1} * ψ_{m+1}
  - Raw polynomial identity, no coordinate-ring quotient needed
  - Proof: unfold φ_m definition and ring
- ATOM 3b (dblZ_divPoly_eq): dblZ_W.toPoly(![φ_m, ωP_m, ψ_m]) = ψ_{2m}
  - Requires Invertible 2 (char ≠ 2)
  - Uses W.toPoly to lift curve to R[X][Y] (dblZ depends on a₁, a₃)
  - Proof: expand negY, apply ωP normalization identity via linear_combination
- Supporting infrastructure: toPoly, ψTwoMulQuotP, ωP, two_mul_ψ_mul_ωP
- Status: 0 sorry, 0 custom axioms
- Note: X-component (addX) requires Weierstrass equation (Equation P), not attempted
## 2026-06-24 (cont) — BRIDGE-1 CLOSED + ω_n infrastructure + projective formula Z-components

- `4e49710` **BRIDGE-1 WIRED** into SeamE1_Core: `preΨ'_root_Ψ₂Sq_ne` sorry DISCHARGED.
  SeamE1_Core now has 1 sorry (bridge-2 only). Module-system wiring: Bridge1HCD + Bridge1Even
  converted to `module` files with `public` exports. scratch.SeamE1 3012 jobs green.
- `eac5bdf` **Bridge1Even 0-sorry**: all 6 ring-identity sorries closed. Odd closed forms by induction,
  even closed forms by D²=-4C³ substitution + oddSign factor + C-power consolidation + push_cast;ring.
  Ψ₃/Ψ₂Sq coprimality cert imported from KeystoneResultantCerts.
- `ff5cc53` **Projective formula Z-components** (ProjectiveFormula.lean, 0 sorry):
  - addZ_divPoly_eq: addZ(P, R_m) = ψ_{m-1}·ψ_{m+1} (by definition of φ, one-line `ring`)
  - dblZ_divPoly_eq: dblZ(R_m) = ψ_{2m} (via ω normalization + `linear_combination`)
  - Infrastructure: toPoly, ωP, ψTwoMulQuotP
- `fc1479d` Projective X-component m=1 proved (ProjectiveFormulaXY.lean), m=2 framework (1 sorry)
- `4c2c69b` **ω_n definition** (OmegaDivPoly.lean, 0 sorry):
  - ψTwoMulQuot via complEDS₂ (Mathlib EDS complement)
  - ωProto with Invertible(2:R)
  - Normalization identity: 2·ψ_n·ω_n = ψ_{2n} - ψ_n²·(a₁φ+a₃ψ²)


