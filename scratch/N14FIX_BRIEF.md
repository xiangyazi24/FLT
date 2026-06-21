# N14 FIX — restore the green build of scratch/DischargeN14.lean (headline build is currently RED)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build).

## PROBLEM
`lake build FLT.Assumptions.MazurProof.TorsionBound` currently FAILS — not on the A6 work (that built
clean), but on `scratch/DischargeN14.lean`:
- `scratch/DischargeN14.lean:53:13: Unknown identifier _root_.obstruction_Q14`
- `scratch/DischargeN14.lean:41:34: unsolved goals` — goal `u ∈ {0, 4, 8}` from `w^2 = u^3 - 11u^2 + 32u`
  (the X1(14)=14a4 model) mapping to the rank-0 Q14 model `z^2 = v^3 + 22v^2 - 7v`.

This is the 14a4/A4 residual (the 2-isogeny descent to the rank-0 curve Q14). The descent helpers in
scratch/ObstructionQ14.lean / CoprimeFactorSplit.lean / ZPhiDescentOddFinal.lean were partially built
(right5 closed; left5 may remain). The reference `obstruction_Q14` is broken — find the actual exported
lemma in scratch/ObstructionQ14.lean (check its real name/namespace; it had a prior `ring_nf made no
progress` issue) and wire it correctly, OR if the obstruction lemma is not yet provable, leave ONE
clearly-NAMED `sorry` seam.

## GOAL
Make `lake build FLT.Assumptions.MazurProof.TorsionBound` GREEN again. Concretely:
1. Fix the `obstruction_Q14` identifier — locate the real lemma in scratch/ObstructionQ14.lean (grep for
   the Q14 rank-0 / X14-points-degenerate statement), fix the name/namespace/`_root_.` reference.
2. Close the unsolved goal `u ∈ {0,4,8}` — this is the X14 forward-map enumeration: the rational points of
   the 14a4 model have u ∈ {0,4,8} (the rank-0 Q14 descent forces it). Use the obstruction lemma + the
   curve equation. If the rank-0 enumeration is not fully proven, isolate it as the SINGLE named seam.
3. The build must be GREEN. If a genuinely-incomplete math piece remains (the Q14 rank-0 enumeration /
   left5), leave it as ONE clearly-named `sorry` (NOT a broken reference, NOT an axiom).

## RULES
- NO axiom-escape, NO broken references. Green build is the target; a clearly-named `sorry` seam is OK if
  the math piece is genuinely incomplete, but the file MUST compile.
- After: run `lake build FLT.Assumptions.MazurProof.TorsionBound 2>&1 | tail -5` and paste the result +
  `grep -n "sorry\|axiom" scratch/DischargeN14.lean scratch/ObstructionQ14.lean`. State exactly what is
  closed vs the named residual seam.
- Edit only scratch/DischargeN14.lean, scratch/ObstructionQ14.lean (+ the descent helper files if needed).
  Do NOT touch the A6 files or other built modules.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named missing piece left as one seam.
