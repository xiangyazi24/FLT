# N25 X-chart map: bounded source-proof delivery

## Result and scope

New production candidate: `N25F_XChartFractionMap.lean` (180 lines, SHA-256
`cde468020a66eba45f0648fc4a8accabcce31bd6a67fb4aef7ce9566a8eb3134`).
Intended repository path: `FLT/Assumptions/MazurProof/N25F_XChartFractionMap.lean`.
Namespace: `MazurProof.N25F_XChartFractionMap`.

It constructs the actual algebra map

```lean
xChartToFraction :
  RationalPointsN25QuotientTwoWBoundaryChartArtin.XChartRing →ₐ[ZMod 2]
    FractionRing N25F_NonBoundaryPrincipalDivisor.W
```

and proves the three exact coordinate formulas:

- `xY ↦ algebraMap W (FractionRing W) qy / algebraMap W (FractionRing W) qx`
- `xZ ↦ algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qx`
- `xW ↦ 1 / algebraMap W (FractionRing W) qx`

All coordinates and chart carriers are the existing source definitions.
The new file adds no carrier, axiom, admission, or nonvanishing premise.
No accepted file has been modified.

The prerequisite `qx_ne_zero` is proved by evaluating the actual W-chart
quotient at the binary point `[1:1:0:1]`. Both canonical equations are checked
by kernel reduction (`decide`). Evaluation sends `qx` to `1`, so `qx` cannot
be zero. This proof needs no domain assumption.

One private chart-evaluation lift is reused for this binary point and for
the universal W-chart point mapped into its fraction field and scaled by
`qx⁻¹`. The fraction point satisfies the quadric and cubic by the existing
homogeneity and coordinate-map theorems. No claim of injectivity,
localization extension, DVR structure, boundary order, or product formula
is made.

## Source pin and instance

All FLT reads used the GitHub connector at accepted commit
`f0eb8381677bc483bddd93826871845030dd5c0e` in `xiangyazi24/FLT`.
`source-inputs.json` records 14 exact snapshots; their content bytes were
verified against the connector's Git blob SHA-1 as well as recorded with
SHA-256. `copied-declarations.json` identifies every copied declaration
used by the bounded harness and its exact lines and content hash.

The production file imports `N25F_NonBoundaryPrincipalDivisor`, hence the
accepted W-chart normalization and its imported
`RationalPointsN25QuotientTwoPlaneChartDomain`. The latter already declares
`canonicalWChart_isDomain : IsDomain (ChartQuotient 3)` at lines 721–725.
The production candidate relies on that existing instance and contains no
additional `[IsDomain W]` parameter.

## What was actually checked

The exact-pinned bounded sandbox uses Lean 4.31.0-rc2 and Mathlib
`96fd0fff3b8837985ae21dd02e712cb5df72ec05`, one CPU/thread, 3072 MiB cap,
60-second timeout, direct Lean elaboration, no broad `lake build`.

`XChartMapCheck.lean` reproduces 51 exact accepted declarations, including
the real coordinate structure, polynomial equations, affine quotient
presentations, universal-point facts, W/X aliases, and actual `qx/qy/qz`
and `xY/xZ/xW` coordinates. It then uses the production candidate body
unchanged except for an explicit ordinary section parameter
`[IsDomain W]` immediately before `xFractionPoint`.

The parameter is neither an axiom nor a hidden admission. It deliberately
stands for the accepted source's existing domain instance without building
the full FLT geometry dependency closure. Thus the map validation is
conditional feedback on that instance, not an unconditional full-import
FLT compilation. The earlier `qx_ne_zero` is checked without it.

Final check `check-02` passed:

- Exit code: 0
- Elapsed: 12.159 seconds
- Peak child RSS: 2,133,584 KiB
- Harness SHA-256: `bf7e0c8cbf8a686ce09bf423392dd4f9af15285f1022acf977faf52813dd8352`
- `qx_ne_zero`, `xChartToFraction`, and all three coordinate theorems emit
  only `propext`, `Classical.choice`, and `Quot.sound`
- No `sorryAx` appears in the successful check
- Two non-fatal style warnings remain

`check-02.log` and `check-02.json` are the raw successful evidence. The
initial failed check is retained honestly as `check-01.*`; it exposed
fixture extraction/import issues and overly broad coordinate simplification,
all corrected before the successful run.

To preserve the exact `Coordinates4` deriving clause, the two pinned support
modules `Mathlib.Tactic.ProxyType` and `Mathlib.Tactic.DeriveFintype` were each
compiled directly under the same bounds, with their dependencies already
cached. Both passed. Their logs, source hashes, timings, and memory usage
are in `support-proxy.*` and `support-fintype.*`. No recursive build ran.

## Remaining acceptance gate

`ActualXChartMapCheck.lean` is supplied for the lead's real FLT checkout.
It imports the production candidate, synthesizes the existing domain
instance, checks the exact coordinate signatures, and emits their axioms.
That full-import integration check has NOT been run here.

The original N25 projective boundary/product-formula bottleneck remains
open. The new map is the requested smallest concrete boundary producer;
injectivity and boundary local valuation transport are separate next steps.
