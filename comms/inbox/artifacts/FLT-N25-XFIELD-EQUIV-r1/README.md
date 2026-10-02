# Actual N25 coordinate-rigid fraction-field equivalence

## Result

Production candidate `N25F_XChartFractionEquiv.lean`, intended for
`FLT/Assumptions/MazurProof/N25F_XChartFractionEquiv.lean`, imports the
unchanged `N25F_XChartFractionInjective` candidate and proves in namespace
`MazurProof.N25F_XChartFractionEquiv`:

- `xFractionToFraction : FractionRing XChartRing →ₐ[ZMod 2] FractionRing W`
- `xFractionToFraction_algebraMap`, identifying its restriction with the
  existing coordinate-rigid `xChartToFraction`
- `fraction_qx_mem_range`, `fraction_qy_mem_range`, and `fraction_qz_mem_range`
- `wChart_algebraMap_mem_range` for every element of the actual W-chart ring
- `xFractionToFraction_surjective` and `xFractionToFraction_injective`
- `xChartFractionAlgEquiv : FractionRing XChartRing ≃ₐ[ZMod 2] FractionRing W`
- `xChartFractionAlgEquiv_algebraMap`, preserving the exact chart-map restriction
- `xChartToFraction_isFractionRing`

The last statement explicitly means:

```lean
letI : Algebra XChartRing (FractionRing W) :=
  xChartToFraction.toRingHom.toAlgebra
IsFractionRing XChartRing (FractionRing W)
```

It does not install a global competing scalar action. This is the
coordinate-rigid algebra structure required for the later scalar tower
through `xLocalToFraction`; it is not the structure induced by the unrelated
binary automorphism between the affine charts.

## Proof scope

The lift is `IsFractionRing.liftAlgHom` applied to the previously proved
injectivity theorem. Its field range contains `qx`, because the image of
`xW` is `1/qx`. Multiplying the images of `xY` and `xZ` by `qx` gives `qy`
and `qz`, using the existing actual nonvanishing theorem. Quotient
surjectivity and `MvPolynomial.induction_on` prove that every element of W
is in the range. The fraction representation proves surjectivity on
`FractionRing W`.

Finally, every W-function-field element is a quotient of images of elements
of X, by choosing a preimage in `FractionRing XChartRing`. Injectivity of the
chart map supplies the faithful scalar action, and `IsFractionRing.of_field`
gives the displayed fraction-ring structure.

All carriers, coordinates, quotient relations, and maps are the actual
source objects. No generation/surjectivity premise, new geometry assumption,
axiom, sorry, admission, or replacement ring is introduced. The previous
candidate files are unchanged. This file does not claim the local-ring
fraction-field theorem, a valuation theorem, the pole order, or a projective
product formula.

## Successful bounded check

`check-03` passed with:

- Lean 4.31.0-rc2
- Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`
- Exit code 0, 48.411276 seconds, 2,515,816 KiB peak child RSS
- One compiler thread, one CPU, 3072 MiB cap, 60-second timeout
- All eleven public declarations report only `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx` or custom axiom in the successful harness
- Only pre-existing style/fixture warnings remain

The exact successful source, raw log, and run metadata are retained as
`XChartFractionEquivCheck.lean`, `check-03.log`, and `check-03.json`.
The earlier failed checks are retained and are not acceptance evidence:
`check-01` exposed implicit-carrier inference issues; `check-02` exposed the
quotient induction API name and automatic simple-ring inference. Explicit
field carriers, quotient surjectivity, and an elementary field-map
injectivity proof resolved these.

## Verification boundary

This is an actual-source bounded harness, not a full FLT import-graph build.
The production body is included verbatim apart from one inserted section
parameter `[IsDedekindDomain W]`. This parameter stands for the accepted
source instance `canonicalWChart_isDedekindDomain` in
`RationalPointsN25QuotientTwoWChartNormalization.lean`, lines 573–574. The
prerequisite harness likewise uses its previously documented structural
parameters. No such parameter occurs in the new production candidate.

The unchanged prerequisite fixture contains 51 exact declarations from 11
accepted files, along with the actual map, chart equivalence, and injectivity
candidate bodies. Its 14 source snapshots were reverified against the
recorded Git blob SHA-1, SHA-256, and byte length for accepted FLT commit
`f0eb8381677bc483bddd93826871845030dd5c0e`.

`ActualXChartFractionEquivCheck.lean` is the pending full-import acceptance
check for the lead's pinned FLT checkout after integration. It has not been
run here. No accepted source was edited, and no remote write, commit,
integration, full build, or cache operation was performed by this task.

## Reproduction

The directory is self-contained for fixture reconstruction, with the
prerequisite bodies and exact source snapshots under `prerequisites/`.
Run only after obtaining the shared bounded-compiler slot:

```sh
python /workspace/shared/flt-n25-field-equivalence/prerequisites/make_check.py
python /workspace/shared/flt-n25-field-equivalence/make_check.py
python /workspace/shared/flt-n25-field-equivalence/run_check.py check-local \
  /workspace/shared/flt-n25-field-equivalence/XChartFractionEquivCheck.lean
```

The first two reconstruction steps were checked byte-for-byte against the
successful fixture. `validation.json`, `harness-inputs.json`, and
`MANIFEST.json` record the resulting hashes and the exact evidence boundary.

## Repository handoff

The remote evidence packet does not duplicate the unchanged predecessor
fixture/sources. Reconstruct `prerequisites/` from dot commit
00be9496255202155d8748f60621edbaec072d36 and its source-input manifest,
verifying all hashes in validation.json and harness-inputs.json. The included
complete successful harness also suffices for the bounded standalone check.
A separate identical-source .olean emission is queued to make subsequent
small checks incremental; it is not part of this packet's claimed evidence.
