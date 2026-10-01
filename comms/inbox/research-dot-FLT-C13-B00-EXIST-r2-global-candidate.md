# FLT-C13-B00-EXIST r2: exact global-existence source candidate

- Repository: xiangyazi24/FLT
- Dispatch: 44b6fa4c9bbb43e65d0c136ab8e57bbfa8392402
- Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5
- Output branch: research-dot/flt-collaboration-20261001
- No project builds, dependency caches, or compiler/axiom checks were run. The lead owns compilation and acceptance.
- Own-branch commit/push is authorized. This is a source-only candidate delivery; lead compilation and acceptance remain pending.

## Result and verification boundary

The frozen 22 new source modules, 4,239 lines, culminate in:

`MazurProof.N13CalibratedChooser.globalExistenceTarget : N13CoherentChooserSpecification.GlobalExistenceTarget`

The target definition is unchanged. The candidate supplies the three exact prescribed values, the named rational-point comparisons, and integral tensor comparisons. No new axiom, sorry, comparison hypothesis, or special-code additivity hypothesis is introduced.

This is a complete *source candidate*, not a kernel-verified theorem. Independent source review of the principal-comparison stack has found no concrete mathematical or source-signature issue; the final named-point/calibration review and the transitive dependency check also found no concrete defect. Compilation and `#print axioms` are NOT RUN.

The six older candidates already compiled by the lead are not repeated or modified. The earlier first-batch report described intermediate open goals accurately at its timestamp; this report supersedes its current progress status.

## Construction

1. Repair the upper wall by the actual Cantor plusStep, preserving the generic class and retaining an exact principal correction. Repaired representatives have degree at most two, nInf at least -1, and degree+nInf at most one.
2. Construct the proper two-chart line from the repaired representative. Carry the actual infinity branch multiplicities on exactly the same witness as its raw generic datum and affine saturation.
3. Prove invertible ideals with nonzero domain-valued reduction are vertically saturated, by testing inverse-ideal sections. Primitive fraction presentations retain the exact removed powers of two.
4. Transport the same primitive fraction between the affine and infinity charts through the ordinary overlap, preserving nonzero reductions on both charts.
5. Prove actual two-branch finite-jet detection and simultaneous finite-jet lifting for the N13 infinity chart. These derive all-order ideal approximations, rather than assuming completion faithfulness or approximation hypotheses.
6. Combine actual branch equality and ordinary-overlap equality to get generic infinity ideal equality. Descend integrally by the proven saturation theorem.
7. Derive the sum of both infinity orders of the principal multiplier from graph-ideal norms and conjugation-fixed affine units. This retains both factors on each side of a tensor comparison.
8. Identify the actual ordinary-overlap branch maps with the named function-field Laurent maps and the actual infinity power-series maps. Prove the latter maps injective. The common primitive fraction therefore gives the correct order difference at both branches.
9. Use the positive oriented-quotient equation and the norm/degree sum to derive both actual branch principal ideal equations. The negative branch equation is proved, not assumed.
10. Descend the affine principal equation using primitive principal-ideal saturation and the pinned invertible-product saturation theorem.
11. Extract the multiplier from equality of generic class sums and assemble all four functions, their nonzero reductions, the affine ideal equation, the infinity ideal equation, and the single overlap fraction into `IntegralComparison`.
12. For arbitrary rational classes, use `N13MumfordInfinityBalance.classOf_surjective` directly, then base change and the repaired marked construction. Uniqueness/`normalizedMumford` is unnecessary for this existence step and was removed.
13. Certify the exact existing rational-point data, including integral and escaping affine points. Cancel a common invertible tensor factor to obtain single-line comparisons from the tensor theorem.
14. Certify the required inverse-infinity datum by the explicit graph u=X(X+1), v=1, nInf=-1, whose raw mark is -2 and actual branch multiplicities are (0,0). Override the uncalibrated choice at 0, AJ13 T, and -AJ13 T.

## Dependency caution

The two calibration-disjointness proofs currently use `N13SmallMumfordRigidity.classOf_injective` on balanced Mumford representatives. This is distinct from the previously flagged raw/special-coherence route. Its chain through `eq_of_class_eq`, `principal_is_constant`, affine factor extraction and the two-infinity pole-order theorem was traced through a 32-file project import closure with no prohibited or flagged declarations and no circular NormalFormData use. The new comparison proof never uses `exactSpreadLine`, `n13_class_eq_iff`, or arbitrary raw-data-to-special-class coherence.

The final lead check must compile in dependency order and inspect the endpoint's axioms, not merely scan the new module for forbidden declarations.

## Still open

- Compiler/elaboration acceptance and endpoint axiom audit for this entire candidate stack
- `degreeFourCode_eq_of_comparison`, the characteristic-two principal-divisor/code bridge
- B03 special-code additivity and downstream C13 endgame assembly

The exploratory 127-function/69-rational-supported Python check from the earlier report remains evidence for planning only. It is not a Lean proof of the degree-four bridge.

## Frozen source-review receipt

The final snapshot is identified by the full candidate SHA-256 manifest. Endpoint SHA-256: `514c47dedbefede319d8fd87d536d68d50b14790f053c3a34314629231c446c7`; named-point certificate: `fcf430dfdcfcd13677d6154ceab24b973f06c0ae3d430573a4be448dc0526c14`; surjectivity-only compatibility wrapper: `d51692d82deb3182fe88868a75ae4868fb2c659baeea095c6876d87f98b3cd47`. Independent source-review reports are supplied separately. Source-review success does not replace the lead’s compilation and axiom audit.

The earlier 974d3e96... historical snapshot is unchanged. A separate audited delta adds only explicit local classical decidability to the piecewise choice; the current manifest uses the corrected hash.
