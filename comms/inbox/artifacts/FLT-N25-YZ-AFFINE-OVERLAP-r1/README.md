# N25: the genuine Y/Z affine-overlap equivalence

## Result

`MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv` has type

```lean
Localization.Away yZ ≃ₐ[ZMod 2] Localization.Away zY
```

There are no extra hypotheses. These are the actual quotient chart rings and
actual coordinates `yZ = Z/Y` and `zY = Y/Z`, not proxy carriers or assumed
isomorphisms. No domain instance, field-valued point, or product formula enters
the proof.

The production candidate is `N25F_YZAffineOverlapEquiv.lean`. It imports the
preceding `N25F_YZOverlapMap` candidate for its public `yX` coordinate and actual
Y/Z chart definitions. Put it at
`FLT/Assumptions/MazurProof/N25F_YZAffineOverlapEquiv.lean` after its predecessor
imports (reported accepted in r10). No predecessor was edited, and nothing was pushed.

## Construction and API

1. Scale the universal Z-chart point by the inverse of `zY`, obtaining a
   Y-chart point in `Localization.Away zY`.
2. Scale the universal Y-chart point by the inverse of `yZ`, obtaining a
   Z-chart point in `Localization.Away yZ`.
3. Homogeneity of the actual quadric and cubic supplies the four relation
   proofs; evaluation descends through each actual quotient.
4. The mapped overlap coordinates are units, so each map lifts to the away
   localization.
5. Multiplication identities prove that each inverse coordinate maps to the
   opposite original coordinate.
6. Localization extensionality, followed by quotient polynomial-generator
   extensionality, proves both compositions are identities.

Public maps:
- `yChartToZYOpen`, with exact formulas for `yX`, `yZ`, and `yzW`
- `zChartToYZOpen`, with exact formulas for `zX`, `zY`, and `zW`
- `yzOpenToZYOpen`, `zyOpenToYZOpen`
- `yzAffineOverlapEquiv`

The equivalence and its inverse have `[simp]` lemmas for the original chart
algebra maps and inverse coordinates. Combined with the six coordinate lemmas,
these give the expected coordinate-rigid formulas for all three chart generators.

## Validation boundary

The current candidate and harness both set file-level
`set_option synthInstance.maxHeartbeats 200000`, matching the accepted
predecessors' full-import configuration. Only this header option changed; both
namespace bodies are byte-for-byte preserved, as recorded in
`configuration-sync.json`.

The earlier configuration passed twice under Lean 4.31.0-rc2 and Mathlib
`96fd0fff3b8837985ae21dd02e712cb5df72ec05`, using the authorized one-CPU,
3-GiB, 60-second shared compiler gate. Its source bytes, olean, logs, and receipts
are retained intact in `historical-before-synth-heartbeats/`. The synchronized
configuration passed `check-03` with a newly emitted reusable olean. Total
wrapper time was 167.82 seconds including shared-gate wait; the compiler itself
retained its 60-second bound. Peak child RSS was 2,463,576 KiB.
All 17 audited public declarations, including the equivalence, depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The checked harness imports the previous exact-definition Z-chart harness and
copies the original Y-ring/Y-coordinate declarations and public `yX` verbatim.
The entire production namespace body is byte-identical to the checked body.
The equivalence is unconditional in the harness as well as the production
candidate. See `source-provenance.json` and `validation.json` for hashes.

This is **not** a full-FLT-import build. The repository-import integration has
not been compiled here. The original exact-definition fixtures use base commit
`f0eb8381677bc483bddd93826871845030dd5c0e`. The parent reports that r10 accepted
all 14 preceding candidates at `0b2cfe016226552b61f3ef4074a05e48cec50560` and
requested this compile-configuration synchronization before delivery. No
predecessor edits or full build were performed for this synchronization.

## Reproduce

```sh
LEAN_PATH=/workspace/shared/flt-n25-zfield-equivalence:/workspace/shared/flt-n25-zfraction-injective \
  python /workspace/shared/flt-n25-affine-overlap-equiv/run_check.py recheck \
  -R /workspace/shared/flt-n25-affine-overlap-equiv \
  -o /workspace/shared/flt-n25-affine-overlap-equiv/YZAffineOverlapEquivCheck.olean \
  /workspace/shared/flt-n25-affine-overlap-equiv/YZAffineOverlapEquivCheck.lean
```

A reusable `YZAffineOverlapEquivCheck.olean` is included. To import it from a
successor harness, prepend this directory to the two directories in `LEAN_PATH`
and use `import YZAffineOverlapEquivCheck`.
