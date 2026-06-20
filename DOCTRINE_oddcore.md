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

## MAIN GOAL COMPLETE (2026-06-20) + next avenues
obstruction_curve_20a4_points_degenerate DISCHARGED (commit 5e6a0a2, #print clean).
Remaining MazurProof custom axioms (11):
- Axioms.lean: rational_torsion_two_invariant_factors, weil_pairing_primitive_root, no_rational_point_of_order_ge_17
- DescentBridge: Z2xZ10_gives_non_degenerate_E20_point (the OTHER half — group theory side)
- DescentBridgeN12: obstruction_curve_N12 (w²=(u-1)(u-2)(u+2), FULL 2-torsion u∈{1,2,-2}; degen u∈{-2,0,1,2,4}) + Z2xZ12
- DescentBridgeN14, N16: same shape
- ObstructionCurve: E20_rational_points_complete
- TorsionFinite: mordell_weil_fg
NEXT AVENUE: obstruction_curve_N12 (full-2-torsion complete 2-descent — different from 20a4 partial torsion). Then N14/N16. The obstruction_curve_* family is the same SHAPE (rank-0 point bound) → reusable descent skeleton once N12 done.
INTEGRATION FOLLOW-UP (needs Xiang direction — touches shared lakefile.toml): fold the 7 scratch deps into a build-graph lean_lib so lake build verifies the discharge (currently verified via lake env lean + prebuilt oleans).

## 2026-06-20 — TWO axioms discharged + N14/N16 templates
DONE: obstruction_curve_20a4 (partial-2-torsion, 2-isogeny quartic descent) +
      obstruction_curve_N12 (full-2-torsion, Ljunggren quartic descent z²=x⁴+14x²y²+y⁴).
Both #print-verified 0 custom axiom.

NEXT obstruction_curve avenues (templates identified):
- N14: w²=u³+u²-2u = u(u+2)(u-1). FULL 2-torsion (like N12), degenerate = the 3 roots {-2,0,1}
  only (no non-torsion rational pts). → mirror N12 (Ljunggren-style); the Pellian constant
  differs from 48 — derive it. Possibly SIMPLER than N12 (no extra-point cases → fewer
  squareclass triples need Lemma A/B; mostly the descent + torsion-only conclusion).
- N16: w²=u³-u²-u = u(u²-u-1). PARTIAL 2-torsion (u²-u-1 irreducible, like 20a4). Only u=0
  reachable ({-1,1} give w²<0, vacuous). → mirror 20a4 (no_denominator_quartic-style quartic
  descent on the cover); likely the EASIEST remaining (single reachable point).

REUSABLE MACHINERY (all 0-axiom, committed): ZPhiDescentStep (5q⁴ Pellian), Ljunggren14
(48y⁴ Pellian), FourthPowerSplit, CoprimeFactorSplit, PythagoreanDescentTail, SquareStep014
(Lemma B), FourSquaresAP (Lemma A), the clear_denominators + squareclass-assembly pattern.

CHECKPOINT NOTE: held next Codex grind here — 2-axiom milestone + gamma sims (Xiang research)
CPU-starved by overnight Codex/compiles. Resume N14 (or N16, easiest) on next push.
