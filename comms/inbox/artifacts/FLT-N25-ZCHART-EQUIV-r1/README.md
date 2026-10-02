# Actual N25 Z/W chart algebra equivalence

## Deliverable

`N25F_ZChartWChartEquiv.lean` is the production candidate for
`FLT/Assumptions/MazurProof/N25F_ZChartWChartEquiv.lean` at FLT revision
`f0eb8381677bc483bddd93826871845030dd5c0e`.

The file proves in namespace `MazurProof.N25F_ZChartWChartEquiv`:

- Four exact coordinate-polynomial identities for
  `S(X,Y,Z,W)=(Y+Z+W,Y+Z,X,Z)` and `S⁻¹(X,Y,Z,W)=(Z,Y+W,W,X+Y)`
- Actual quotient algebra maps `wChartToZChart` and `zChartToWChart`
- All six coordinate formulas
- `zChartAlgEquivWChart : ZChartRing ≃ₐ[ZMod 2] W`
- `IsDomain ZChartRing` and `IsDedekindDomain ZChartRing`, transported through
  that equivalence from the established W-chart instances

`ZChartRing` and `zW` are the actual public definitions from
`RationalPointsN25QuotientTwoWBoundaryZLocal`. That source keeps `zX` and `zY`
private; this candidate defines public coordinate names with the same
`chartMap 2 (MvPolynomial.X 0/1)` formulas in its own namespace. It does not
replace the actual ring by a proxy.

There are no new assumptions in the production candidate: no `axiom`,
`sorry`, `admit`, `native_decide`, arbitrary embedding, or opaque geometric
class. The characteristic-two equality is mapped from `ZMod 2`, without
assuming `IsDomain` or nontriviality of the Z chart in advance.

This automorphism-induced chart equivalence changes coordinate functions.
It is not the coordinate-rigid inclusion of the charts in the same function
field and does not by itself discharge valuation compatibility or the global
principal-divisor/product-formula bridge.

## Verification method

`ZChartEquivCheck.lean` is a standalone exact-source harness. It copies 49
verbatim declarations from 11 independently fetched exact-pin FLT source
files, including the actual quotient and coordinate definitions. The complete
production proof body follows unchanged, except for an ordinary
`[IsDedekindDomain W]` variable immediately before the two final transport
instances. This variable stands for the existing W instance supplied by the
production imports, not a new production assumption. Every polynomial
identity, quotient map, inverse law, and algebra equivalence is unconditional
in this harness.

`source-inputs.json` records the exact GitHub blob SHAs, URLs, sizes, and
SHA-256 hashes. `copied-declarations.json` records individual declaration
ranges and hashes. `make_check.py` reconstructs the harness from those
snapshots and the production candidate. `run_check.py` records bounded
compiler timing, return code, peak child RSS, and the checked file hash.

The full FLT dependency graph is not installed here. The production file
still needs compilation under its full imports; a source-faithful harness
check is not a full-project build pass. No remote write or integration is
performed by this work.

## Check result

`check-01.log` and `check-01.json`: exit 0 in 13.59 seconds, with 2,428,904
KiB peak child RSS, one compiler thread/CPU, and the existing 60-second /
3 GiB cap. No warnings. All seven requested axiom audits report only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; the four polynomial
identities use only `propext` and `Quot.sound`. No `sorryAx` or custom axiom.

The unconditional actual quotient algebra equivalence, all coordinate
formulas, both inverse laws, and the transported domain/Dedekind instances
are therefore compiler-checked at the pinned Mathlib/Lean version in this
exact-source harness. The final transports are parameterized only in the
harness, because its excerpt omits the existing W-normalization proof.

`validation.json` records the candidate and tested harness hashes and the
precise check scope. The production candidate SHA-256 is
`6058bc2512b100dafc39a4c25356ed66c2491ede1ab8e73e45810979f6adbd23`.

## Required downstream acceptance

Compile `N25F_ZChartWChartEquiv.lean` under the complete pinned FLT imports,
then audit `zChartAlgEquivWChart`, `zChartRing_isDomain`, and
`zChartRing_isDedekindDomain` there. This local result supplies the actual
Z-chart ring structure needed for later boundary order work; it does not
claim the remaining principal-divisor/global product-formula theorem.
