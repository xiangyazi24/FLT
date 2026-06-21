# SEAM2 PROTOTYPE — de-risk the x-only diff-add algebra (CLOSEABLE-NOW certs)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build). Work in a NEW file scratch/Seam2Proto.lean. Do NOT edit built files or the
existing scratch/Seam2.lean (the old WIP scaffold) — this is an isolated algebra prototype.

## CONTEXT
SEAM2 = the x-only differential-addition primitive for the Mazur keystone. A fresh, cleaner design (the
completed-square / Kummer-biquadratic route) is in scratch/SEAM2_dm3_skeleton.md — READ IT. It avoids the
old `xRep_add_of_xRep_sub` division approach. Per the design, the polynomial ALGEBRA is CLOSEABLE-NOW with
explicit small `linear_combination` certificates; only the project-local xRep/Point.add glue is missing.

## GOAL (de-risk ONLY — like the A6 resultant prototype)
Create scratch/Seam2Proto.lean and drive `lake build` to GREEN with 0 sorries on these PURE-ALGEBRA lemmas
(no elliptic-curve points, no xRep — just ℚ variables + W : WeierstrassCurve ℚ and its b-invariants):

1. `YsqCoord_sq_of_equation` : (2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆, given W.Equation x y.
   (via `linear_combination 4 * hxy` after unfolding b₂/b₄/b₆ and equation_iff.)
2. `YsqCoord_negY` : (2*(negY x y) + a₁x + a₃) = −(2y + a₁x + a₃)  (by ring; unfold Affine.negY).
3. `addX_eq_completed_square_formula_of_ne_x` (PROTOTYPE FIRST, the riskiest of these):
   W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
     (((Y₁ − Y₂)/(x₁ − x₂))² − b₂)/4 − x₁ − x₂   where Yᵢ = 2yᵢ + a₁xᵢ + a₃, x₁≠x₂.
   (via slope_of_X_ne + field_simp[sub_ne_zero.mpr hx] + ring) — plus the subX variant with negY x₂ y₂.
4. `differential_addition_affine_sum_cert` :
   (x₁−x₂)²(xp+xm) = 2x₁x₂(x₁+x₂)+b₂x₁x₂+b₄(x₁+x₂)+b₆,  where xp/xm are the completed-square formulas,
   given Y₁²=fY x₁, Y₂²=fY x₂.  (via `linear_combination (1/2)*hY₁ + (1/2)*hY₂` after field_simp.)
5. `differential_addition_affine_prod_cert` :
   (x₁−x₂)²·xp·xm = x₁²x₂² − b₄x₁x₂ − b₆(x₁+x₂) − b₈.
   (via `linear_combination q₁*hY₁ + q₂*hY₂ + q₃*W.b_relation`; the explicit q₁,q₂,q₃ are in the skeleton.
    If field_simp normalizes oddly, use the cleared-form variant `16(x₁−x₂)²(...)=0` with subst.)

All five are CLOSEABLE-NOW per the design. The exact b-invariant unfoldings / Mathlib API names
(WeierstrassCurve.b₂/b₄/b₆/b₈, b_relation, Affine.equation_iff, Affine.negY, Affine.slope_of_X_ne,
Affine.addX) may need local adjustment — RESOLVE by building.

## RULES
- NO axiom-escape; 0 sorries is the target for these 5 algebra lemmas. If a `linear_combination` certificate
  needs a sign/coefficient tweak (e.g. −4 vs 4, or field_simp normalization), grind it — these ARE provable
  identities (the design verified the math).
- Do NOT touch Point/xRep wiring this round — that is the next (separate) step and needs project-local glue.
- When done: run `grep -n "sorry\|axiom" scratch/Seam2Proto.lean` + `lake env lean scratch/Seam2Proto.lean`,
  PASTE BOTH VERBATIM, state the exact sorry count. Report which of the 5 closed.
- Unbounded grind. Only legitimate stop: a certificate is mathematically wrong (then say which + the residual).
