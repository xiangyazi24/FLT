# Actual N25 X-boundary DVR structure

## Production candidate

`N25F_XLocalDVR.lean` is intended for
`FLT/Assumptions/MazurProof/N25F_XLocalDVR.lean` at accepted FLT revision
`f0eb8381677bc483bddd93826871845030dd5c0e`.

It imports the two preceding candidates unchanged:

- `N25F_XChartWChartEquiv.lean`, supplying the explicit actual-chart equivalence
- `N25F_XChartFractionMap.lean`, supplying the coordinate-rigid map and `qx ≠ 0`

Its additional established import is
`RationalPointsN25QuotientTwoWBoundaryXLocal.lean`.

In namespace `MazurProof.N25F_XLocalDVR`, the new file proves:

- `xChartRing_isDedekindDomain : IsDedekindDomain XChartRing`
- `xW_ne_zero : xW ≠ 0`
- `xW_mem_xPrime : xW ∈ xPrime`
- `xPrime_ne_bot : xPrime ≠ ⊥`
- `xLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing XLocalRing`
- `xWGerm_ne_zero : xWGerm ≠ 0`

Every carrier and element is the actual accepted-source definition. There is
no substitute ring, axiom, admission, new structural hypothesis, or modification
of either earlier candidate. The Dedekind input is the accepted instance
`RationalPointsN25QuotientTwoWChartNormalization.canonicalWChart_isDedekindDomain`
(source lines 573–574), reached through the existing production imports.

The proof transports Noetherianity, Krull dimension at most one, and integral
closedness through the explicit X/W equivalence. Its nonzero point-prime proof
uses `xChartToFraction xW = 1 / algebraMap W (FractionRing W) qx`, so it does not
require injectivity of that map. The final DVR proof is Mathlib's theorem that
localizing a Dedekind domain at a nonzero prime gives a DVR.

## Scope

The accepted source already proves `Ring.ord XLocalRing xWGerm = 3`. This file
provides the missing actual-ring DVR structure and nonvanishing needed to use
that local order in discrete-valuation arguments. It does not itself construct
the coordinate-rigid local embedding into the W fraction field, prove its
fraction-field property, or prove the projective product formula.

## Bounded verification

`XLocalDVRCheck.lean` is reconstructed by `make_check.py`. It uses the same
51 verbatim accepted-source declarations as the preceding chart checks, plus
three exact source ranges containing the actual X-point evaluation, kernel,
maximality, localization, and germ definitions. Both preceding candidate
bodies and the new candidate body are included.

The harness inserts the ordinary parameter `[IsDedekindDomain W]` at three
scoped points that need the established W structure. This parameter represents
the accepted production instance without building its entire geometry import
closure. The unconditional chart equivalence, binary evaluation, and original
X-point definitions remain checked without that parameter. There is no such
parameter in the production candidate.

`source-inputs.json` records 15 exact-pin source snapshots. Each was verified
against the GitHub connector's Git blob SHA-1 and recorded with a SHA-256.
`copied-declarations.json` records the copied declaration/range hashes.

The bounded compiler is Lean 4.31.0-rc2 with Mathlib
`96fd0fff3b8837985ae21dd02e712cb5df72ec05`, one CPU, one compiler thread,
3072 MiB memory cap, and a 60-second timeout. No recursive or broad build,
remote write, commit, or integration was performed.

The corrected `check-02` passed:

- Exit code 0
- 31.94 seconds
- 2,761,568 KiB peak child RSS
- All six new declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` or custom axioms
- Harness SHA-256:
  `46e3df0732e97859f1ebcdfb247a7caf79a6985cb5280f76f469a3dd259e6a82`
- Production SHA-256:
  `0d777634f8bddeaf55250e1ab0b1cccdf54641eff167b86d9b2f134e0928adb3`

Only style and fixture-unused-section-variable warnings remain. Raw output
and run metadata are in `check-02.log` and `check-02.json`; all relevant file
hashes and the explicit conditional-check boundary are in `validation.json`.

The initial `check-01` failed on one extra explicit argument to the dimension
transport theorem and a missing `Mathlib.Algebra.Field.ZMod` fixture import.
Those diagnostics and the failed-run record are retained.

## Remaining acceptance gate

The entire FLT import graph was not built here. `ActualXLocalDVRCheck.lean`
provides a full-import acceptance check for the lead's pinned checkout,
including actual instance synthesis and compatibility with the established
order-three theorem. It must be run after accepting the two prerequisite
candidate modules. Conditional bounded feedback is not full-project acceptance.
