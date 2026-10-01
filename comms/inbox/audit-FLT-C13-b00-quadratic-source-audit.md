# FLT same-witness quadratic marking: source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate: `N13MarkedQuadraticExistence.lean`, 568 lines. Exact snapshot hash and byte count are in `quadratic-source-audit.json`.

## Finding

No concrete mathematical, namespace, constructor-argument, or same-witness propagation issue found by source inspection. Compilation, tactic success, and axiom checks are NOT RUN.

The finite branch retains the literal finite quadratic closure. The horizontal reciprocal branch retains `E.data`, and its constant-term premise is discharged after rewriting `E.data_u` using the actual reciprocal equation. The vertical reciprocal branch retains `u`, `E`, and `huMem` in the same constructor; its nonzero-constant proof matches the identical `integralReciprocal a b`. Constructor and saturation-lemma argument order matches the pinned source. Distinct-split and repeated-root branches retain their respective concrete pair lines, obtaining zero infinity multiplicities from those same points. The exhaustive irreducible/nonirreducible dispatcher calls these strengthened local lemmas rather than dropping the added conjunct.

The final existential conjoins raw equality, generic class, affine saturation, and both zero generic infinity multiplicities on one `R`. It assumes no target compatibility or additive invariant. Direct forbidden proof tokens and forbidden class-equality/exact-spread-coherence dependencies were absent.

## Important scope boundary

For a balanced degree-two input, `dataOfSpecialRealization` still stores the original raw mark -1, while the actual line has positive infinity multiplicity zero. This intermediate theorem does not claim `HasGeometricMark`. The effective chamber wrapper must use the effective representative's mark -2 and preserve the new same-witness multiplicity certificate. This distinction was communicated to the author before integration.

Full integral principal comparisons, global chooser compatibility/fixed values, and B03 additivity remain outside this result. No remote publication was performed.
