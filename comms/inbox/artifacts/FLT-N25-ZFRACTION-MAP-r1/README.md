# N25 coordinate-rigid Z-chart fraction map

## Result

`N25F_ZChartFractionMap.lean` is an additive production candidate for
`FLT/Assumptions/MazurProof/`. It imports the passed local predecessor
`N25F_ZChartWChartEquiv.lean` and the accepted normalization source. No
predecessor file is changed.

The candidate proves:

- `algebraMap_Rz_X`: the existing normalization algebra map from
  `Polynomial (ZMod 2)` to the actual W-chart sends `Polynomial.X` to `qz`
- `qz_ne_zero` and `fraction_qz_ne_zero`
- `zChartToFraction : ZChartRing →ₐ[ZMod 2] FractionRing W`
- `zChartToFraction_zX`: `zX ↦ map(qx) / map(qz)`
- `zChartToFraction_zY`: `zY ↦ map(qy) / map(qz)`
- `zChartToFraction_zW`: `zW ↦ 1 / map(qz)`

Here `ZChartRing` and `zW` are the actual accepted definitions from
`RationalPointsN25QuotientTwoWBoundaryZLocal`; `zX` and `zY` are the public
coordinate definitions in the passed Z/W equivalence predecessor. These
are precisely the quotient classes of the ambient X, Y, and W coordinates
on the Z chart. The function field is that of the fixed actual W ring.

## Why the denominator is genuinely nonzero

The accepted `rzAlgebraW` is the composition

`Polynomial F₂ → PlaneCoordinateRing → W`.

The first map sends the polynomial variable to `planeZ`, defined as
`AdjoinRoot.of planeSexticPolynomial Polynomial.X`. The accepted bridge
identity `planeCoordinateRingToCanonicalWChart_planeZ` sends this to
`canonicalWChartZ`. Unfolding the canonical point and quotient map identifies
that element with the actual `qz`.

The already established normalization instance
`canonicalWChart_isTorsionFree : Module.IsTorsionFree (Polynomial F₂) W`
then yields `FaithfulSMul` and injectivity of the coefficient map. Since
`Polynomial.X ≠ 0`, its image `qz` is nonzero. No binary-point witness is
claimed or used, and no new nonzero or algebra assumption is introduced
into the production candidate.

The universal W-chart point is mapped to `FractionRing W` and multiplied
by `map(qz)⁻¹`. Its Z coordinate is one, and homogeneity preserves both
canonical equations. The actual quotient universal property supplies the
coordinate-rigid algebra map and the three exact formulas.

## Verification scope

Accepted FLT source pin:
`xiangyazi24/FLT@f0eb8381677bc483bddd93826871845030dd5c0e`.

Lean `4.31.0-rc2`, Mathlib
`96fd0fff3b8837985ae21dd02e712cb5df72ec05`.

`ZChartFractionMapCheck.lean` copies 83 declarations verbatim from 14
accepted source files plus the two public coordinate definitions in the
passed local predecessor. The source-file Git blob hashes and SHA-256
hashes were checked. `source-inputs.json`, `copied-declarations.json`,
`make_check.py`, and `verify_sources.py` record the provenance and reproduce
the harness.

The exact coefficient algebra instances, the plane relation/elimination
proof, the quotient maps, and the bridge coordinate identity are included
with their source proofs. In particular, the coefficient-map identity is
checked without a placeholder hypothesis.

The harness inserts only two ordinary typeclass variables into the
otherwise unchanged candidate body:

1. `[Module.IsTorsionFree (Polynomial (ZMod 2)) W]` immediately before
   `qz_ne_zero`, standing for the accepted normalization instance at line 567
2. `[IsDomain W]` immediately before `zFractionPoint`, standing for the
   accepted W-domain instance

Those are explicit *harness parameters*, not axioms or production
assumptions. Their accepted proofs and the full imported FLT dependency
closure are not rebuilt here. The harness independently includes the
accepted nontriviality proof from the affine origin.

Final check `check-03` passed under the shared compiler gate:

- Exit code: 0
- Elapsed: 19.450 seconds
- Peak child RSS: 2,435,488 KiB
- One CPU, one compiler thread, 3,072 MiB Lean cap, 60-second timeout
- All eight printed declarations have only `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx`
- Four non-fatal style warnings: three unused harness section variables
  and one inherited `simpa` suggestion

The earlier failed logs `check-01` and `check-02` are retained. They exposed
missing focused-harness imports for characteristic-p and the ZMod field;
no production proof edit was required between these checks and the pass.

## Remaining gate and scope

`ActualZChartFractionMapCheck.lean` is supplied for the lead's real FLT
checkout. It imports the production candidate, synthesizes the accepted
instances, checks the unparameterized signatures and exact formulas, and
prints axioms. This full-import integration check has **not** been run here.

No injectivity theorem, equivalence of fraction fields, extension to a
boundary localization, valuation transport, or projective product formula
is claimed. No remote writes, broad build, or new algebra/nonvanishing
hypothesis was introduced. The other passed artifacts remain untouched.
