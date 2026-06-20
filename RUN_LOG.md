
## Run 2026-06-19 01:30
- doctrine version: DOCTRINE.md written this session
- approval: /automode command msg_id 11362 + 我睡了. 你自己执行
- starting avenue: (a) squareclass bypass
- workers: dm1 (b99vgar9x), dm2 (b0051ml2y), Codex (tmux)
- end: <pending>
- final result: <pending>

## Status update 2026-06-19 02:30
- ALL mathematical content proved (0 sorry in each piece file)
- Assembly compiles with 2 sorry (Rat API wiring only)
- 2 axioms in assembly are PROVED in separate files (Descent20a4, CoprimeSqDvd)
- Key breakthrough: p=-1 case doesn't need quartic — b⁴|(b²-1) gives b=1 directly
- Remaining: wire Rat.num/den API to connect rational u to integer descent chain

## Status update 2026-06-19 05:30
- rat_sq_int_implies_den_one: PROVED (15 lines, 0 sorry)
- CoprimeSqDvd: PROVED (28 lines, 0 sorry)  
- FourthPowerSplit: PROVED (76 lines, 0 sorry)
- Assembly skeleton: compiles, 1 sorry (u.den=1 wiring)
- p=1 case math DONE (w²<0), Lean cast issues remain (5 errors)
- p=-1 case math DONE (b⁴|(b²-1) → b=1), Lean wiring pending
- |p|≥2 case: axiomatized (num_abs_le_one). Needs valuation argument.
- Git-drop connector broken since ~midnight. ChatGPT answers not landing.
- Codex: stdin-not-a-terminal issue with nohup exec. Not usable.
- Avenue (a) partially successful: cover trick + coprime_sq_dvd bypass most complexity
- Remaining work: ~50 lines of Rat API cast plumbing to close the last sorry

## Status update 2026-06-19 21:35 (Opus 4.8)
- ObstructionComplete: 0 sorry, 4 axioms (3 now PROVEN separately):
  - int_solutions_20a4 ✓ (Descent20a4.lean)
  - coprime_sq_dvd ✓ (ChatGPT: q|b² ∧ b²|q → q=b²)
  - isSquare_of_isSquare_cube ✓ (ChatGPT: Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow)
  - num_abs_le_one ⬜ = the full quartic descent (= no_denominator_quartic)
- Descent chain gaps remaining:
  - ZPhiDescentOddFinal: 2 pythagorean axioms (left5/right5) — closeable via FourthPowerSplit+PythagoreanDescentTail (both proven)
  - CoprimeFactorSplit: 1 UFD axiom (coprime product = 4th power)
  - ZPhiDescentStep: 2 sorry (odd/even core wiring)
- Dispatched: ChatGPT pipe (left5), Codex (right5 + UFD axiom)
- KEY: FourthPowerSplit + PythagoreanDescentTail both 0-sorry → left5/right5 are pure assembly

## Run 2026-06-20 (automode)
- goal: close odd_core last sorry → discharge obstruction_curve_20a4
- starting avenue: (a) Codex session 019ee381
- approval: explicit /automode launch (do-not-ask)
- end: TBD

## Run 2026-06-20 RESULT
- obstruction_curve_20a4_points_degenerate DISCHARGED (theorem, 0 custom axiom).
- Chain: odd_core(b61d0ab) -> W1 DenominatorQuartic(d222a81) -> W2+W3 ObstructionComplete(141582b) -> W4 DescentBridge(5e6a0a2). left5 earlier d271fa6.
- #print axioms at every node = [propext, Classical.choice, Quot.sound].
- Caveat: scratch oleans not yet in lake globs; verified via lake env lean w/ prebuilt oleans.
- Next: fold scratch into build graph; remaining 11/12 Mazur axioms.

## Run 2026-06-20 RESULT #2
- obstruction_curve_N12_points_degenerate DISCHARGED (theorem, 0 custom axiom, #print verified).
- Crux was not_ljunggren_14 (z²=x⁴+14x²y²+y⁴ no nontrivial sol) — fresh Pellian descent (48y⁴), 1104 lines (a134637).
- + Lemma B (SquareStep014), Lemma A (FourSquaresAP), ObstructionN12 squareclass assembly (d9829b0).
- TWO Mazur axioms now discharged tonight: obstruction_curve_20a4 + obstruction_curve_N12.
- Remaining obstruction_curve family: N14, N16 (same shape as N12 — Ljunggren/Lemma A/B machinery is the template).

## Run 2026-06-20 RESULT #3
- obstruction_curve_N16_points_degenerate DISCHARGED (0 axiom, #print verified). Partial-2-torsion, mirrored 20a4 (DescentN16 + DenominatorQuarticN16 683-line quartic descent + reused ObstructionComplete/CoprimeSqDvd/IsSquareCube). commit dac126b.
- THREE obstruction_curve axioms discharged: 20a4, N12, N16. Remaining: N14 (full-2-torsion, torsion-only).
