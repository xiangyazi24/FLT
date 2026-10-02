# Actual W-chart norm/dimension prerequisite

## Intended integration

Add only `FLT/Assumptions/MazurProof/N25F_WChartNormDimension.lean` from this directory. The accepted `N25F_WChartQuotientFinite.lean` is imported, not edited. No existing divisor definition or norm algebra is replaced.

New theorem:

```lean
MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finrank_eq_natDegree_norm
    (a : W) (ha : a ≠ 0) :
  Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) =
    (Algebra.norm (Polynomial (ZMod 2)) a).natDegree
```

This is an actual numerical identity for the existing affine ring and its actual polynomial-base algebra. It has no basis, scalar-tower, module-free, or quotient-finiteness premise. The only element condition is nonvanishing, required by Mathlib's norm theorem.

## Actual-source checks

Read via GitHub connector at FLT commit `40efa26fea43fb0ed7d70db804f0d0dcdd71342b`:

- `N25F_NonBoundaryPrincipalDivisor.lean:19` defines `W := WChartQuotient`; it imports chart normalization at line 2. Blob `4cb645a429c94c736267ff2ec7f7e77463eb493d`.
- `RationalPointsN25QuotientTwoWOpenEvaluation.lean:51` defines `WChartQuotient := ChartQuotient (3 : Fin 4)`. Blob `8523290a73ebcd6ec25550578ca8b41c991d01c8`.
- `RationalPointsN25QuotientTwoWChartNormalization.lean` uses the same `ChartQuotient 3` carrier. Blob `13312dbe3c5cec7fdef9576da6ead94843ae5c3e`, unchanged from the previous accepted pin.
  - Lines 184–185: `rzAlgebraW` supplies the actual polynomial-base algebra by composing the existing plane-coordinate maps
  - Lines 198–199: `canonicalWChart_finiteRz` proves finite generation over that algebra
  - Lines 567–570: `canonicalWChart_isTorsionFree` proves torsion-freeness over the same polynomial base
  - Lines 573–574: `canonicalWChart_isDedekindDomain` supplies the actual domain structure
- Accepted `N25F_WChartQuotientFinite.lean` blob `1ac81106e1f048fb669e8fddfc5b666b5a54bd11` is preserved. Original local artifact SHA-256 remains `b93b4090ed99594fe85811c37aaec0f751dec5389fec9bd0cb4274d0c3dd6cd9`.

Connector URLs and blob IDs are recorded in `sources/CONNECTOR_SOURCES.json`.

## Pinned Mathlib ingredients

Mathlib commit `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, Lean `4.31.0-rc2`:

- `Mathlib/LinearAlgebra/FreeModule/Norm.lean:62`: `finrank_quotient_span_eq_natDegree_norm` identifies the quotient dimension with the polynomial norm degree for a nonzero element and a finite basis
- `Mathlib/LinearAlgebra/FreeModule/PID.lean:386`: `Module.free_of_finite_type_torsion_free'` obtains freeness from finite generation and torsion-freeness over the polynomial PID
- `Mathlib/LinearAlgebra/FreeModule/Basic.lean`: `Module.Free.chooseBasis` chooses an existing-module basis
- `Mathlib/LinearAlgebra/FreeModule/Finite/Basic.lean:28`: `Module.Free.ChooseBasisIndex.fintype` proves its index finite from finite generation
- `RingHom.ext_zmod` identifies the two binary scalar maps, and `IsScalarTower.of_algebraMap_eq'` builds the required tower without any added premise
- `Mathlib.Algebra.Field.ZMod` is explicitly imported so the generic microcheck has the binary field structure

## Verification boundary

`GenericNormDimension.lean` instantiates exactly the proposed proof under the structural hypotheses already supplied by the actual chart. It does not assume a basis, freeness, or scalar tower. Its microcompile is separate from compiling the FLT specialization. See `GENERIC_CHECK.log` and `MANIFEST.json` for the final check result.

`ActualWCheck.lean` is a suggested integration/audit driver. No FLT module compilation or aggregate axiom audit was run in this task. Actual specialization and aggregate acceptance remain lead-owned.

## Remaining mathematical frontier

The theorem provides the norm/dimension side of the weighted affine principal-divisor formula. It does not yet identify the actual weighted valuation sum with that norm degree, and it does not prove the projective product formula or remove the N25 custom axiom. The remaining affine obligation is the factorization/relative-norm degree comparison with actual binary residue degrees; boundary comparisons are later obligations.
