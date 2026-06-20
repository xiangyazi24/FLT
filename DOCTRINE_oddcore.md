# DOCTRINE — discharge obstruction_curve_20a4 (last sorry: odd_core)

## Goal (one sentence)
Close the single remaining sorry `zphi_descent_step_odd_core` (ZPhiDescentStep.lean:301)
so that `zphi_descent_step` is 0-sorry/0-axiom → `no_denominator_quartic` →
`num_abs_le_one` → `obstruction_20a4`, discharging the axiom
`obstruction_curve_20a4_points_degenerate`.

## State (verified)
- odd case back-half: left5/right5 PROVEN 0-axiom in ZPhiDescentOddFinal.lean (commit d271fa6).
- even case: even_square_leg_descent_core + zphi_descent_step_even_core PROVEN (commit 42dc66b).
- ONLY remaining sorry: zphi_descent_step_odd_core front-half (Pellian split for odd q).

## Avenues (ranked)
(a) [PRIMARY, IN FLIGHT] Codex (session 019ee381) fills odd_core mirroring the proven
    even twin even_square_leg_descent_core + reusing left5/right5. Terminal: compiles 0 sorry.
(b) If Codex stalls on the factor split: dispatch sub-lemma "A·B=5q⁴, q odd, A,B coprime →
    branch A=5m⁴/B=n⁴ or A=m⁴/B=5n⁴" to ChatGPT; I assemble the rest.
(c) De-private left5/right5/coeff_identity_* in ZPhiDescentOddFinal, import into
    ZPhiDescentStep, fill odd_core back-half via them; I write the front-half factor split.
(d) Fallback: I write odd_core fully myself, inlining even-twin structure w/ odd bookkeeping.

## Terminal condition (whole run)
obstruction_curve_20a4_points_degenerate discharged: the consuming theorem derives it,
#print axioms ⊆ {propext, Classical.choice, Quot.sound}. One commit per avenue closed.

## DISCOVERED upper chain (2026-06-20 audit) — full path to discharge
After odd_core closes zphi_descent_step (0 sorry), wire up:
(W1) DenominatorQuartic.lean:22 has STUB `axiom zphi_descent_step` — replace by importing
     ZPhiDescentStep.zphi_descent_step → no_denominator_quartic becomes 0-axiom.
(W2) ObstructionComplete.lean:16 `axiom num_abs_le_one` — prove from no_denominator_quartic
     (cover trick: u=p/q, p=±square via valuation, reduce to quartic t²=a⁴+a²b²-b⁴).
     Helpers already present: neg_one_case_false, coprime_pow_three_qsq_q_sub_one,
     no_int_sq_between_consecutive, rat_sq_int_den_one, rat_eq_num.
(W3) ObstructionComplete other 3 axioms (int_solutions_20a4, coprime_sq_dvd,
     isSquare_of_isSquare_cube) — PROVEN in sibling files; import to discharge.
(W4) obstruction_20a4 → original axiom obstruction_curve_20a4_points_degenerate.
NOTE: num_abs_le_one (W2) is INDEPENDENT of odd_core — workable in parallel NOW.
