# SEAM2 build-ready skeleton (dm3 round-2, hand-pasted recovery 2026-06-21)

x-only differential addition `xRep_add_of_xRep_sub` on a general Weierstrass curve.
KEY: the global primitive is a PAIR of homogeneous Kummer biquadratic identities (NOT a single
division formula) — handles Z=0/∞/P=Q/P=-Q/2-torsion WITHOUT division. Completed-square coord
Y = 2y + a₁x + a₃ ⇒ Y² = 4x³ + b₂x² + 2b₄x + b₆ = fY.

## Affine identities (x₁≠x₂)
(x₁-x₂)²(x₊+x₋) = sumAff = 2x₁x₂(x₁+x₂) + b₂x₁x₂ + b₄(x₁+x₂) + b₆
(x₁-x₂)²·x₊·x₋  = prodAff = x₁²x₂² − b₄x₁x₂ − b₆(x₁+x₂) − b₈

## Explicit certificates (CLOSEABLE-NOW)
- YsqCoord_sq_of_equation: (2y+a₁x+a₃)² = fY x   via `linear_combination 4 * hxy` (hxy = Equation).
- YsqCoord_negY: YsqCoord x (negY x y) = −YsqCoord x y   via `ring`.
- addX_eq_completed_square_formula_of_ne_x: W.addX x₁ x₂ (slope x₁ x₂ y₁ y₂) =
    ((Y₁−Y₂)/(x₁−x₂))²−b₂)/4 − x₁ − x₂  via slope_of_X_ne + field_simp + ring. (PROTOTYPE FIRST.)
  subX variant (with negY x₂ y₂): same with (Y₁+Y₂).
- sum cert: (x₁-x₂)²(xp+xm)=sumAff  via `linear_combination (1/2)*hY₁ + (1/2)*hY₂`.
- product cert: (x₁-x₂)²·xp·xm=prodAff via `linear_combination q₁*hY₁ + q₂*hY₂ + q₃*W.b_relation`
  q₁ = Y₁²−2Y₂² − b₂x₁²+4b₂x₁x₂−2b₂x₂² + 2b₄x₁+b₆ − 4x₁³+8x₁²x₂+8x₁x₂²−8x₂³
  q₂ = Y₂² − 4b₂x₁²+4b₂x₁x₂−b₂x₂² − 4b₄x₁+2b₄x₂−b₆ − 16x₁³+8x₁²x₂+8x₁x₂²−4x₂³
  q₃ = 4x₁²−8x₁x₂+4x₂²
  (if field_simp normalizes oddly, use the cleared variant: 16(x₁-x₂)²·(...)=0 with subst then linear_combination.)

## Projective Kummer (global seam), δ = X₁Z₂−X₂Z₁, D = δ²:
D(X₊Z₋ + X₋Z₊) = sumNum · Z₊Z₋ ;  D·X₊X₋ = prodNum · Z₊Z₋  (sumNum/prodNum = homogenized sumAff/prodAff)
Functional formula (δ≠0 ⇒ Z₋≠0): x(P+Q) = [sumNum·Z₋ − D·X₋ : D·Z₋]  (the robust default; product form
[K₁₂Z₋ : D·X₋] needs extra X₋≠0). Derive xRep_add_of_xRep_sub from the SUM identity via
`ring_nf at hsum ⊢; linear_combination hsum`.

## MISSING-PROJECT-API (the only real gap — "the riskiest remaining seam is the Point.add→W.slope/W.addX layer, NOT the polynomial identity")
- xRep : (W⁄ℚ).Point → P1Q  (project-local projective x-rep)
- xRep_zero = [1:0], xRep_neg_same (x(−P)~x(P))
- Point.add → W.addX/W.slope unfolding/rewrite lemmas; the Point constructor `cases`
- xRep(P−Q).Z ≠ 0 from δ≠0

## BUILD ORDER (prototype-first, per the skeleton §14)
1. addX_eq_completed_square_formula_of_ne_x  (+ subX variant)  ← prototype FIRST
2. YsqCoord_sq_of_equation, YsqCoord_negY
3. differential_addition_affine_sum_cert, differential_addition_affine_prod_cert  (the two certs)
4. xRep_add_sub_kummer_affine_ne_x  (affine nondegenerate, glues 1-3)
5. project-local xRep + Point.add rewrites → global xRep_add_sub_kummer_biquadratic (case split: 0/0, x₁≠x₂, x₁=x₂ via Y_eq_of_X_eq, 2-torsion)
6. xRep_add_of_xRep_sub  (export; from the sum identity)
Resultant route NOT recommended (larger certs than completed-square).
