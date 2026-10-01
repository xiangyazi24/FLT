# FLT marked effective-chart wrapper: source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate: `N13MarkedEffectiveData.lean`. Exact identity is in `effective-source-audit.json`.

No concrete source-level mathematical, signature, or namespace issue was found. Compilation and axiom checks remain NOT RUN.

The degree-zero branches match multiplicities (0,2), (1,1), and (2,0) with the actual chosen infinity sections. The degree-one branches match (0,1) and (1,0) with the appropriate infinity anchor. The affine point factor contributes zero generic infinity multiplicities in both cases.

The degree-two branch calls the strengthened quadratic existential and retains its particular witness and `hmarked`. It then reuses the same charts through `withMark R (E.nInf - 1)`. The effective chamber inequalities force `E.nInf = -1`, so the changed raw mark is -2, and the requested multiplicities both simplify to zero. This closes the same-witness packaging gap identified by the previous audit at source level.

The final `exists_marked_repaired_data` theorem combines the marked effective construction with `repair_class`. It proves raw equality for the repaired representative and generic class equality for the original balanced representative, plus affine saturation and actual two-branch multiplicities on the same Data witness. It does not assume its conclusion or a specialization-additivity invariant.

The final theorem does not explicitly include `HasGeometricMark` as a conjunct, but its raw equality recovers the stored mark, and the previously established positive-multiplicity arithmetic supplies that corollary. No global chooser point compatibility, full integral principal comparison, or B03 additivity result follows without additional work.
