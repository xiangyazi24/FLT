# SEAM2 WIRING — xRep + global Kummer biquadratic + xRep_add_of_xRep_sub (certs + glue both in hand)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build). Work in a NEW file scratch/Seam2Wired.lean. Do NOT edit built files or the
old scratch/Seam2.lean (superseded WIP). This wires the de-risked algebra into the projective primitive.

## BOTH HALVES ARE PROVEN/DESIGNED — read them
- scratch/Seam2Proto.lean — COMPILES, 0 sorry. The completed-square affine certificates:
  `YsqCoord_sq_of_equation`, `YsqCoord_negY`, `addX_eq_completed_square_formula_of_ne_x` (+ subX variant),
  `differential_addition_affine_sum_cert`, `differential_addition_affine_prod_cert`. IMPORT and USE these.
- scratch/SEAM2_dm3_glue.md — the project-local glue DESIGN (dm3, verified NO genuine Mathlib blocker):
  xRep definition, xRep_zero/xRep_some/xRep_neg_same, and the Point.add → W.slope/W.addX rewrite layer via
  EXISTING Mathlib `WeierstrassCurve.Affine.Point.add_of_X_ne` / `add_of_Y_eq` / `Affine.negY`. Follow it.
- scratch/SEAM2_dm3_skeleton.md — the overall structure (projective Kummer identities, case split).

## GOAL
Create scratch/Seam2Wired.lean, import Seam2Proto + FLT.EllipticCurve.Torsion, drive `lake build` to
GREEN with as few sorries as possible (target 0; honest NAMED seam only if a sub-step needs something
genuinely absent — dm3 found none). Build, in order:
1. `xRep : (W⁄ℚ).Point → P1Q` per dm3's design (0 ↦ [1:0]); `xRep_zero`, `xRep_neg_same` (x(−P)~x(P)).
2. The Point.add rewrite lemmas: for `P=some x₁ y₁`, `Q=some x₂ y₂`, x₁≠x₂, rewrite `(P+Q)` and `(P−Q)`
   x-coords to `W.addX … (W.slope …)` via `Affine.Point.add_of_X_ne` + `negY` (dm3 gives the exact path).
3. `xRep_add_sub_kummer_biquadratic` (the global projective identity pair) by case split on the points
   (0/0, affine x₁≠x₂ using the Seam2Proto certs + the add rewrites, affine x₁=x₂ via `Affine.Y_eq_of_X_eq`
   ⇒ δ=0 and Z₊=0 or Z₋=0 ⇒ both sides 0 by ring, 2-torsion subsumed).
4. `xRep_add_of_xRep_sub` (the SEAM2 export) from the SUM identity (δ≠0 ⇒ Z₋≠0): the robust formula
   x(P+Q) = [sumNum·Z₋ − D·X₋ : D·Z₋], via `ring_nf; linear_combination hsum`.
5. Report whether xRep_add_of_xRep_sub matches the signature the keystone (Torsion.lean's
   nsmul_eq_zero_iff_ΨSq_eval / the x-only diff-add seam) actually consumes — quote the keystone's
   expected signature and note any adapter needed. Do NOT edit Torsion.lean this round; just report fit.

## RULES
- NO axiom-escape. Reuse Seam2Proto's proven certs (import, don't re-prove). Use EXISTING Mathlib point API
  per dm3 (add_of_X_ne, add_of_Y_eq, negY) — dm3 confirmed no Mathlib gap, so grind name/alias mismatches.
- When done: `grep -n "sorry\|admit\|axiom" scratch/Seam2Wired.lean` + `lake env lean scratch/Seam2Wired.lean`,
  PASTE BOTH VERBATIM, exact sorry count, and which of 1-4 closed. Report the keystone-signature fit (step 5).
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named genuinely-missing Mathlib decl.
