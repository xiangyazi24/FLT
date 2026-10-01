# FLT C13 B00-EXIST r2: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate identities and checksums: `source-audit.json` alongside this report.

## Result

Source review found no mathematical contradiction, circular target assumption, or direct use of the prohibited class-equality or exact-spread-coherence claims. This is a source review, not a Lean certification. Compilation, tactic success, transitive axiom audit, and `#print axioms` are NOT RUN.

All 54 materialized source files were independently rechecked against the existing pinned inventory: bytes, SHA-256, and Git blob identities matched.

## Positive checks

- `N13EffectiveInfinityRepair.repair` applies the actual `N13MumfordInfinityBalance.plusStep` on the balanced upper wall. The source has `plusStep_nInf = nInf + degree - 3`; therefore the new marking is -1. Its residual degree is at most two.
- The correction is the exact source `cantorCorrectionUnit`, namely `(Y - plusLift)/normalize(plusFactor)`. `plusCorrection_order` is `3 - degree`. The affine principal relation has the correct direction: repaired ideal times correction principal ideal equals the original ideal. The residual ordinate has the required conjugate sign, `-plusLift` modulo residual `u`.
- Effective multiplicities are `nInf + 1` at positive infinity and `1 - degree - nInf` at negative infinity. The inequalities make both integers nonnegative; total degree is two; the raw positive marking is positive multiplicity minus two. On the repaired upper wall they are zero and `2 - residual degree`.
- Degree-zero and degree-one chart choices use actual infinity sections matching their marks. Degree-two chart data retain the residual affine graph. The explicit `withMark` operation does not claim to prove geometric compatibility.
- `HasInfinityMultiplicities` reads actual infinity ideals under both formal branch expansions. Tensor multiplication adds the two orders. The branch-zero/positive and branch-one/negative conventions agree with the pinned source.
- Finite affine closures have a relation `1 - t*a` in the infinity ideal, mapping to a power-series unit. Nonzero generic t-coordinate points map to ideals containing a series with nonzero constant coefficient in Q2. These correctly give zero generic infinity multiplicities, including escaping affine points.
- Point pairs, anchored point data, both infinity sections, and the inverse-infinity cusp pair are covered by the marking lemmas. Horizontal and vertical reciprocal chart wrappers are also supplied under polynomial membership and nonzero constant hypotheses. `reciprocal_constant_nonzero` correctly extracts the constant coefficient from the actual reciprocal equation and proves it equals the inverse of the original nonzero constant. Packaging these facts with the same arbitrarily selected quadratic Data witness remains to be done.

## Corrected source issue

The newly added `inverseInfinityData_geometricMark` initially lacked a known import route to its named witness. The author added an explicit `N13InverseInfinityWitnessClass` import before the recorded audit snapshot. The last reciprocal-polynomial lemma also initially used unqualified `X` and `C` without opening `Polynomial`; the author added the namespace open.

## Unproved obligations, not failures of the stated partial lemmas

`exists_repaired_data` states raw/class realization plus affine saturation. It does not assert a global `Chooser`, `point_compatible`, or integral tensor comparisons. `HasGeometricMark` is a genuine additional ideal condition, but is not integral separatedness. The following remain open: same-witness packaging of arbitrary quadratic marking; whole-chart extension of generic principal comparisons; global chooser point compatibility and fixed values; and B03 tensor normalization/additivity. Do not report B00 or B03 closed from these candidates.
