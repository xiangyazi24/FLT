# card_E_R_torsion_le — Proof Design (Fable oracle, 2026-07-02)

## Target sorry

```lean
theorem card_E_R_torsion_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    Set.Finite {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ∧
      Set.ncard {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ≤ 2 * n
```

## Architecture

```
(E⁄ℝ).Point
  │ Point.map (algebraMap ℚ ℝ)     [Mathlib, injective]
  ▼
(E.map (algebraMap ℚ ℝ)).Point
  │ variableChangePoint (toShortNF)  [S0, injective, u=1]
  ▼
shortW(A,B).Point
  │ componentBitHom                  [S1-S3, surjective onto ZMod 2]
  ▼
ZMod 2       ker = E(ℝ)⁰ (identity component)
  │
  │ θ : ker → AddCircle(2T)         [S4-S8, injective AddMonoidHom]
  ▼
AddCircle(2T)
  │ card_torsion_le_of_isSMulRegular [Mathlib: |n-torsion| ≤ n]
  ▼
|E(ℝ)⁰[n]| ≤ n, then coset trick → |E(ℝ)[n]| ≤ 2n
```

## S0: Variable Change Point Hom (in progress)

Injective `AddMonoidHom` for u=1 VariableChange. ~200 lines.
- Point map: (x,y) ↦ (x-r, y-s(x-r)-t)
- Template: Mathlib's Point.map + baseChange_* formulas
- Key: equation_iff_nonsingular (Δ≠0) avoids separate Nonsingular transport

## S4: σ integral definition + basic properties

Define σ(x) = ∫_{Ioi x} dt/√f(t), NOT as ∫_e^x.

**Why σ, not τ:** τ(x) = ∫_e^x has T-jumps at O and (e,0) that don't vanish mod 2T.
σ measures from ∞, giving 2T-jumps only (killed by AddCircle).

Key facts:
- g(t) = (√f(t))⁻¹ (junk extension: f<0 → sqrt=0 → 0⁻¹=0)
- σ(x) = ∫_{Ioi x} g (Bochner set integral)
- T = σ(e) > 0
- IntegrableOn g (Ioi e): split at e+1
  - Near e: g ≤ C·(t-e)^{-1/2}, use intervalIntegrable_rpow'
  - Near ∞: g ≤ (t-e)^{-3/2}, use integrableOn_Ioi_rpow_of_lt
- StrictAntiOn σ (Ici e)
- 0 < σ(x) < T for x ∈ (e,∞)
- ContinuousOn σ (Ici e)
- σ → 0 at Filter.atTop
- HasDerivAt σ (-g x) x for x > e (via FTC)
- Fact (0 < 2*T) instance

**2026-07-06 update:** `FLT/Assumptions/MazurProof/RealTopologyS4.lean`
now starts S4 using the same cubic as S3,
`shortCubic A B x = x^3 + A*x^2 + B*x`.  It defines
`rightIntegrand`, `sigma`, and `halfPeriod`, and proves:
- `IsRightSigmaRoot`
- `shortCubicRootFactor`
- `shortCubic_eq_sub_mul_rootFactor`
- `shortCubicRootFactor_at_root`
- `exists_rootFactor_pos_nhdsGT`
- `exists_rootFactor_gt_half_deriv_nhdsGT`
- `exists_shortCubic_lower_bound_near_root`
- `half_cube_le_shortCubic_of_large`
- `tailThreshold`
- `half_cube_le_shortCubic_of_tailThreshold_le`
- `shortCubic_pos_of_tailThreshold_le`
- `rightIntegrand_pos_of_tailThreshold_le`
- `sqrt_eq_rpow_half`
- `inv_sqrt_eq_rpow_neg_half`
- `half_mul_cube_rpow_neg_half`
- `rightIntegrand_le_const_mul_rpow_tail`
- `rightIntegrand_aestronglyMeasurable_restrict_Ioi`
- `rightIntegrand_integrableOn_Ioi_tailThreshold`
- `rightIntegrand_integrableOn_Ioi_of_tailThreshold_le`
- `exists_rightIntegrand_integrableOn_Ioi`
- `rightIntegrand_aestronglyMeasurable_restrict_Ioo`
- `integrableOn_Ioo_sub_rpow_neg_half`
- `rightIntegrand_le_root_model_near`
- `rightIntegrand_integrableOn_near_root`
- `shortCubic_nonneg_of_sq_eq`
- `y_eq_sqrt_or_eq_neg_sqrt_of_sq_eq_shortCubic`
- `shortW_y_eq_sqrt_or_eq_neg_sqrt`
- `rightIntegrand_pos_of_right`
- `rightIntegrand_ne_zero_of_right`
- `rightIntegrand_pos_of_gt_root`
- `rightIntegrand_nonneg`
- `rightIntegrand_continuousOn_Ioi_of_right`
- `rightIntegrand_continuousOn_Ioi_of_ordered_roots`
- `rightIntegrand_continuousAt_of_gt_root`
- `rightIntegrand_continuousAt_of_right`
- `shortCubic_hasDerivAt`
- `sqrt_shortCubic_hasDerivAt_of_pos`
- `rightIntegrand_intervalIntegrable_of_ordered_roots_of_le`
- `rightIntegrand_intervalIntegrable_of_right_of_le`
- `rightIntegrand_integrableOn_Ioi_root`
- `halfPeriod_pos`
- `sigma_pos_of_right`
- `sigma_lt_halfPeriod_of_right`
- `strictAntiOn_sigma_Ioi`
- `sigma_hasDerivAt_of_right`
- `neg_sigma_hasDerivAt_of_right`
- `tendsto_sigma_atTop`

This file checks on `uisai2` with 0 sorries.  The tail and near-root
integrability arguments now use the same `rpow` route recommended by ChatGPT
Q3554/Q3557/Q3561: convert `1/sqrt` to exponent `-(1/2)`, compare by
`Real.rpow_le_rpow_of_nonpos`, use `integrableOn_Ioi_rpow_of_lt` at infinity,
and use `intervalIntegral.intervalIntegrable_rpow'` plus
`IntervalIntegrable.comp_sub_right` near the root, then split `Ioi e` at
`a = e + δ/2` and `R = max a (tailThreshold A B)`.  The derivative
`sigma_hasDerivAt_of_right` rewrites the tail integral locally as
`∫_x^b g + ∫_{Ioi b} g` and applies
`intervalIntegral.integral_hasDerivAt_left`, giving `σ'(x) = -g(x)` on
the right component.  Positivity of
`halfPeriod` and `sigma` uses `setIntegral_pos_iff_support_of_nonneg_ae`;
`sigma < halfPeriod` and strict antitonicity use
`intervalIntegral.integral_interval_add_Ioi`.  The atTop limit of `sigma`
uses `MeasureTheory.tendsto_integral_Ioi_zero`.

## S5: θ definition + injectivity

θ : ker(componentBitHom) → AddCircle(2T):
- θ(O) = 0
- θ(x, y<0) = mk(σ(x))        [lower branch: σ ∈ (0,T)]
- θ(x, y>0) = mk(-σ(x))       [upper branch: ≡ mk(2T-σ) ∈ (T,2T)]
- θ(e, 0) = mk(T)              [bottom 2-torsion]

Equivalently: θ(x,y) = if 0 ≤ y then mk(-σ x) else mk(σ x)
(Works at y=0 since σ(e)=T, -T≡T mod 2T.)

θ(-P) = -θ(P) definitional (negation flips y-sign).

Injectivity via Ico-representatives in [0, 2T):
- Use AddCircle.coe_eq_coe_iff_of_mem_Ico
- 4×4 case bash: cross cases killed by disjoint ranges,
  diagonal by StrictAntiOn.injOn for σ

**2026-07-06 update:** `FLT/Assumptions/MazurProof/RealTopologyS5.lean`
now checks on `uisai2` with 0 sorries.  It defines:
- `ComponentKer`
- `thetaRep : ComponentKer → ℝ`, using the fundamental interval `[0,2T)`
- `thetaCandidate : ComponentKer → AddCircle (2*T)`

The checked S5 interface now includes:
- kernel/branch location lemmas:
  `componentKer_some_not_lt`, `componentKer_some_eq_or_gt`,
  `componentKer_some_gt_of_ne`,
  `componentKer_some_y_eq_zero_of_x_eq_root`,
  `componentKer_some_y_branch_of_gt`
- branch formulas:
  `thetaRep_some_root`, `thetaCandidate_some_root`,
  `thetaRep_some_upper`, `thetaCandidate_some_upper`,
  `thetaCandidate_some_upper_eq_neg_sigma`,
  `thetaRep_some_lower`, `thetaCandidate_some_lower`
- AddCircle representative control:
  `thetaRep_mem_Ico`,
  `thetaCandidate_eq_iff_thetaRep_eq`
- injectivity support:
  `sigma_injective_of_right`,
  `componentKer_some_y_eq_sqrt_of_gt_of_nonneg`,
  `componentKer_some_y_eq_neg_sqrt_of_gt_of_neg`,
  `thetaRep_some_lower_pos_lt_halfPeriod`,
  `thetaRep_some_upper_halfPeriod_lt`,
  `thetaRep_injective`,
  `thetaCandidate_injective`

This completes the non-additive θ candidate and its injectivity.  The remaining
hard analytic/topological task is S6-S8: prove additivity of this candidate
modulo `2*T`, then package it as an injective `AddMonoidHom` for the checked S9
harvest.

## S6-S8: θ additivity (the crux)

Fix Q ∈ ker, Q ≠ O. Vary P = (x, +√f(x)) on upper branch, x ∈ (e,∞).

**Junction set F_Q ⊆ (e,∞), |F_Q| ≤ 3:**
- J1: P = -Q (sum → O). Lift jump = 2T. ✓ killed by AddCircle.
- J2: x₃ = e (sum → (e,0)). Lift jump = 2T. ✓ killed.
- J3: P = Q (doubling). NO jump — removable singularity.

**Per-piece constancy (S8 payoff):**
On each interval of (e,∞) \ F_Q:
- x₃(x) is smooth rational, y₃ has constant sign (IsPreconnected)
- S8 identity: dx₃/dx · (1/y₃) = 1/y₁
- ⇒ HasDerivAt (lift of defect) 0 x
- ⇒ constant by `constant_of_has_deriv_right_zero`

**Junction crossing (one-sided limits):**
- J1: σ(x₃) → 0 (x₃ → ∞), both limits = θ(Q)
- J2: σ(x₃) → T, mk(T) = mk(-T) by coe_period
- J3: chord → tangent, continuous (√f differentiable at x_Q)

**Bootstrap for degenerate cases:**
- Lower branch: apply to (-P, -Q), negate
- P = O: trivial
- P = (e,0): limit from x → e⁺
- Degenerate Q (2Q ∈ {O, (e,0)}): group-algebra via auxiliary generic R

**2026-07-06 update:** `FLT/Assumptions/MazurProof/RealTopologyS6.lean`
now checks on `uisai2` with 0 sorries and pins down the remaining S6-S8 seam:
- `thetaPeriod A B e = 2 * halfPeriod A B e`
- `ThetaCandidateAdditive`: the exact pointwise additivity proposition for
  `thetaCandidate`
- `thetaDefect`: the AddCircle-valued additivity defect, with zero-left/right
  checks
- `thetaDefect_eq_zero_iff` and
  `thetaCandidateAdditive_iff_defect_zero`
- `thetaCandidateHom`: packages `thetaCandidate` as an `AddMonoidHom` once
  `ThetaCandidateAdditive` is supplied
- `thetaCandidateHom_injective`
- `exists_injective_thetaHom_of_thetaCandidate_additive`
- right-branch parameterization infrastructure:
  `shortW_nonsingular_of_sq_eq_of_y_ne_zero`,
  `shortW_nonsingular_sqrt_of_pos`,
  `shortW_nonsingular_neg_sqrt_of_pos`,
  `shortW_nonsingular_root_of_deriv_pos`,
  `rootPoint`, `rootKerPoint`, `thetaCandidate_rootKerPoint`,
  `upperRightPoint`, `lowerRightPoint`,
  `upperRightKerPoint`, `lowerRightKerPoint`,
  `thetaCandidate_upperRightKerPoint`,
  `thetaCandidate_lowerRightKerPoint`,
  `componentKer_eq_rootKerPoint_of_some_x_eq_root`,
  `componentKer_eq_upperRightKerPoint_of_some_nonneg`,
  `componentKer_eq_lowerRightKerPoint_of_some_neg`,
  `neg_upperRightPoint_eq_lowerRightPoint`,
  `neg_lowerRightPoint_eq_upperRightPoint`,
  `neg_upperRightKerPoint_eq_lowerRightKerPoint`,
  `neg_lowerRightKerPoint_eq_upperRightKerPoint`,
  `thetaCandidate_lowerRightKerPoint_eq_neg_upper`

Thus the current remaining formal target is exactly:
prove `ThetaCandidateAdditive` for the S5 candidate.  Once that theorem is
closed, the S6 interface gives the injective additive hom required by the S9
harvest without additional cardinality work.

**2026-07-06 update 2:** `FLT/Assumptions/MazurProof/RealTopologyS7.lean`
now checks on `uisai2` with 0 sorries.  It starts the S7 local chord-calculus
layer, importing only S4:
- `chordM`, `chordX`, `chordY`
- `chordDivDiff`
- `shortCubic_sub_eq_mul_chordDivDiff`
- `shortCubicDeriv_eq_chordDivDiff_add`
- `chordM_mul_sub_eq`
- `chordM_mul_y_add_eq_chordDivDiff`
- `chord_deriv_key`
- `chord_slope_deriv_expr`
- `chord_deriv_identity_from_slope_expr`
- `chord_deriv_identity_algebra`
- `hasDerivAt_chordX_signed`
- `hasDerivAt_chordX_upper_sqrt`
- `hasDerivAt_chordX_lower_sqrt`
- `shortW_slope_eq_chordM`
- `shortW_addX_eq_chordX`
- `shortW_addY_eq_chordY`
- `chordY_sq_eq_shortCubic_chordX`
- `sqrt_shortCubic_chordX_eq_chordY_of_chordY_pos`
- `sqrt_shortCubic_chordX_eq_neg_chordY_of_chordY_neg`
- `rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_pos`
- `neg_rightIntegrand_chordX_mul_chordY_div_eq_inv_y_of_chordY_neg`
- `hasDerivAt_neg_sigma_comp_chordX_signed`
- `hasDerivAt_sigma_comp_chordX_signed`
- `hasDerivAt_neg_sigma_comp_chordX_signed_of_chordY_pos`
- `hasDerivAt_sigma_comp_chordX_signed_of_chordY_neg`

The checked endpoint is the algebraic differential identity
`x₃'(x) = y₃/y` in chord coordinates, expressed as a derivative-slope formula,
plus the actual `HasDerivAt` statements for a signed branch and for the
upper/lower sqrt branches.  It also proves the coordinate bridge
`shortW.slope/addX/addY = chordM/chordX/chordY` in the nonvertical case, proves
the chord output lies back on `shortW`, converts the output sign to the correct
sqrt branch, and simplifies the composed `sigma`/`-sigma` derivatives to
`1/y`.

**2026-07-06 update 3:** `FLT/Assumptions/MazurProof/RealTopologyS8.lean`
checks by local single-file `lake env lean
FLT/Assumptions/MazurProof/RealTopologyS8.lean` and is imported by the
top-level `MazurProof.lean`.  `uisai2` is visible over Tailscale but SSH does
not currently complete a usable login from this Mac mini, so this S8 update has
not been reverified by remote build.  It records:
- `sqrt_shortCubic_eq_y_of_y_pos`
- `sqrt_shortCubic_eq_neg_y_of_y_neg`
- `hasDerivAt_neg_sigma_of_y_pos`
- `hasDerivAt_sigma_of_y_neg`
- `hasDerivAt_neg_sqrt_shortCubic_of_pos`
- `shortW_point_add_eq_chord`
- `upperRightPoint_add_eq_upperRightPoint_of_chordY_pos`
- `upperRightPoint_add_eq_lowerRightPoint_of_chordY_neg`
- `lowerRightPoint_add_eq_upperRightPoint_of_chordY_pos`
- `lowerRightPoint_add_eq_lowerRightPoint_of_chordY_neg`
- `thetaCandidate_upperRight_add_some_of_chordY_pos`
- `thetaCandidate_upperRight_add_some_of_chordY_neg`
- `thetaCandidate_lowerRight_add_some_of_chordY_pos`
- `thetaCandidate_lowerRight_add_some_of_chordY_neg`
- `thetaDefect_upperRight_some_of_chordY_pos`
- `thetaDefect_upperRight_some_of_chordY_neg`
- `thetaDefect_lowerRight_some_of_chordY_pos`
- `thetaDefect_lowerRight_some_of_chordY_neg`
- `thetaDefect_upperRight_upperRight_of_chordY_pos`
- `thetaDefect_upperRight_upperRight_of_chordY_neg`
- `thetaDefect_upperRight_lowerRight_of_chordY_pos`
- `thetaDefect_upperRight_lowerRight_of_chordY_neg`
- `thetaDefect_lowerRight_upperRight_of_chordY_pos`
- `thetaDefect_lowerRight_upperRight_of_chordY_neg`
- `thetaDefect_lowerRight_lowerRight_of_chordY_pos`
- `thetaDefect_lowerRight_lowerRight_of_chordY_neg`
- `hasDerivAt_real_theta_defect_lift_zero`
- `hasDerivAt_thetaDefectLift_upper_upper`
- `hasDerivAt_thetaDefectLift_upper_lower`
- `hasDerivAt_thetaDefectLift_lower_upper`
- `hasDerivAt_thetaDefectLift_lower_lower`
- `eq_on_of_hasDerivAt_zero_of_isOpen_isPreconnected`
- `thetaDefectLift_upper_upper_const_on`
- `thetaDefectLift_upper_lower_const_on`
- `thetaDefectLift_lower_upper_const_on`
- `thetaDefectLift_lower_lower_const_on`
- `thetaDefectLift_upperSqrt_upper_const_on`
- `thetaDefectLift_upperSqrt_lower_const_on`
- `thetaDefectLift_lowerSqrt_upper_const_on`
- `thetaDefectLift_lowerSqrt_lower_const_on`
- `thetaDefect_upperRight_some_const_on_of_chordY_pos`
- `thetaDefect_upperRight_some_const_on_of_chordY_neg`
- `thetaDefect_lowerRight_some_const_on_of_chordY_pos`
- `thetaDefect_lowerRight_some_const_on_of_chordY_neg`

This closes the local derivative-zero calculation for all four input/output
branch sign cases and upgrades it to local constancy on any open preconnected
admissible interval.  It also specializes these interval constancy statements
to the actual right-branch functions `+√f` and `-√f`, so future additivity work
does not need to reprove the branch derivative facts.  It now also has the
point-level bridge from the Mathlib group law to `chordX/chordY`, plus
`thetaCandidate(P(x)+Q)` rewrites for a fixed affine `Q=(a,b)` in all four
right-branch input/output sign cases.  It also rewrites the AddCircle-valued
defect itself to the corresponding real lift expression once `thetaCandidate Q`
is represented by a real `qtheta`, specializes those rewrites to the four
standard right-branch `(±√f(a))` choices for `Q`, and upgrades the local real
lift constancy to actual AddCircle-valued local constancy of
`thetaDefect(P(x),Q)` for arbitrary fixed affine `Q`.  The remaining hypotheses
are the genuine local-admissibility conditions: `x>e`, nonvertical chord,
post-addition `x₃>e`, and constant output branch sign.  The next target is
global transport across admissible intervals plus endpoint/root/tangent cases
to prove `ThetaCandidateAdditive`.

## S9: Harvest

1. θ injective hom ⇒ E⁰[n] ↪ AddCircle(2T)[n]
2. |AddCircle(2T)[n]| = n (Mathlib: card_addOrderOf_eq_totient + sum_totient,
   or directly card_torsion_le_of_isSMulRegular)
3. Finiteness transfer: Set.Finite.of_finite_image
4. componentBitHom fiber argument: |E(ℝ)[n]| ≤ 2·|E⁰[n]| ≤ 2n

**Trap:** Nat.card of infinite sets = 0. Must establish finiteness BEFORE cardinality.

**2026-07-06 update:** S9 is now implemented in
`FLT/Assumptions/MazurProof/RealTorsionBound.lean` and checks on `uisai2`.
The completed pure harvest lemmas are:
- `addCircle_nTorsionSet_finite_ncard_le`
- `nTorsionSet_ncard_le_of_injective_addMonoidHom`
- `nTorsionSet_ncard_le_of_injective_addCircle`
- `component_ker_nTorsionSet_to_ambient`
- `nTorsionSet_ncard_le_two_mul_of_component`
- `nTorsionSet_ncard_le_two_mul_of_component_ker`
- `nTorsionSet_ncard_le_two_mul_of_component_theta`
- `shortW_nTorsionSet_ncard_le_of_componentTheta`
- `shortW_nTorsionSet_ncard_le_of_componentKer_embeds_addCircle`

Thus S4-S8 only need to supply, for the checked S3 character
`componentBitHom`, an injective additive hom
`theta : componentBitHom.ker →+ AddCircle T`; the exact checked harvest
hypothesis is
`∃ T, ∃ theta : componentBitHom.ker →+ AddCircle T, Function.Injective theta`.
The period positivity is still needed for the analytic construction, but not
for the Mathlib torsion count.

**2026-07-07 update:** ChatGPT Q3740/Q3741 both recommend the same global
route for `ThetaCandidateAdditive`: fix `Q`, prove branchwise local constancy
away from finitely many bad points, normalize the constant by the `x → ∞`
identity limit, and cross vertical/tangent/root-output points by continuity
rather than by using them as basepoints.

New checked Lean infrastructure:
- `RealTopologyS4.tendsto_sigma_nhdsGT_root`: `sigma x → halfPeriod` as
  `x → e+`.
- `RealTopologyS6.tendsto_addCircle_sigma_nhdsGT_root` and
  `tendsto_addCircle_neg_sigma_nhdsGT_root`: both branch theta formulas tend to
  the root theta value in `AddCircle`.
- `RealTopologyS6.tendsto_thetaCandidate_upperRightKerPoint_nhdsGT_root` and
  `tendsto_thetaCandidate_lowerRightKerPoint_nhdsGT_root`: total wrappers for
  branch `thetaCandidate` root limits.
- `RealTopologyS9`: upper/lower defect wrappers on `Set.Ioi e`, total `atTop`
  wrappers, locally-constant-on-ray implies constant, and locally constant plus
  zero `atTop` limit implies defect zero on the whole ray.

Checked locally:
- `lake build FLT.Assumptions.MazurProof.RealTopologyS6`
- `lake build FLT.Assumptions.MazurProof.RealTopologyS9`
- `lake build FLT.Assumptions.MazurProof`

Checked remotely:
- `REMOTE_BUILD_SERVER=uisai2 remote-build.sh flt` completed successfully.

## S10-S11: ThetaCandidateAdditive (planned, 2026-07-07)

Three-round Fable+ChatGPT dual-oracle planning produced the following plan.

### Architecture: 4 parallel files

1. **S10Audit** (~50-100 LOC): prerequisite audit — ComponentKer closure,
   slope bridge, S8/S9 interface shapes.
2. **S10TailAnchor** (~150-250 LOC): atTop algebra.
   Key identity: `(chordX-a)·(x-a)² = f'(a)·(x-a) - 2b·(y-b)`.
   Proves: `chordX → a`, `chordY → b`, `defect → 0` as `x → ∞`.
3. **S10Seams** (~300-600 LOC): three seam-limit lemmas at bad points.
   - Vertical (P=-Q): `chordM² → ∞`, `chordX → ∞`, `σ → 0`, defect → 0.
   - Doubling (P=Q): slope quotient → tangent via `HasDerivAt.tendsto_slope`.
   - Output-root (x₃=e): rational continuity + `σ → T`, `mk(±T)` coincide.
4. **S10FiniteBridge** (~250-450 LOC): pure topology.
   Finite bad set + matching one-sided limits → IsLocallyConstant on Ioi e.
5. **S11Skeleton** (~150-300 LOC): axiom-first assembly.
   Upper branch → lower branch (negation) → root (commutativity) → O (trivial)
   → ThetaCandidateAdditive.

### Bad set (group-theoretic, ≤ 3 points)
`{x | P(x)=Q} ∪ {x | P(x)=-Q} ∪ {x | P(x)+Q=root}`.
Each is a subsingleton. For Q=(e,0): bad set is **empty**.

### Key oracle insights
- atTop anchor is the uniform decoupler (can't use neg symmetry alone — circularity)
- Bridge lemma, NOT global continuity (Point has no topology; Cantor counterexample
  without finite bad set hypothesis)
- Conjugate identity `λ = (f(x)-f(a))/((x-a)(√f(x)+b))` removes 0/0 at doubling
  (Fable R2), but adds a fake pole risk — use locally only

### Estimated LOC: 950-1800 (most likely ~1200)

## Estimated LOC (full project)

| Step | LOC | Status |
|------|-----|--------|
| S0 | ~200 | In progress (subagent) |
| S4 | 813 | Done (0 sorry) |
| S5 | 563 | Done (0 sorry) |
| S6 | 583 | Done (0 sorry) |
| S7 | 478 | Done (0 sorry) |
| S8 | 1300 | Done (0 sorry) |
| S9 | 212 | Done (0 sorry) |
| S9 harvest | 310 | Done (1 sorry: `card_E_R_torsion_le`) |
| S10-S11 | ~1200 | Planned |
| **Total** | **~5660** | |
