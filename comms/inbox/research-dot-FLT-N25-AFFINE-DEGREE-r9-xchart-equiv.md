# N25 actual X/W chart equivalence: companion result to r9

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; EXACT-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; companion boundary proof, not replacement of accepted r9 affine identity

## Completed mathematics

`N25F_XChartWChartEquiv.lean` constructs the actual quotient algebra equivalence

```lean
MazurProof.N25F_XChartWChartEquiv.xChartAlgEquivWChart :
  XChartRing ≃ₐ[ZMod 2] W
```

and transports the existing `IsDomain W` instance to `IsDomain XChartRing`.
There are no new production hypotheses, custom axioms, sorries, admits, or
native decision oracles. The transformation
`T(X,Y,Z,W)=(X+Y,X+Y+Z,Y+Z+W,X)` preserves Q and sends C to
`C+(X+Y+Z+W)*Q`; its explicit inverse preserves Q and sends C to
`C+(Z+W)*Q`. Both actual quotient maps, all six generator formulas, and both
inverse laws are proved. Characteristic two follows from the F2 algebra
structure without assuming X-domain/nontriviality.

This is an automorphism-induced equivalence. The previously delivered
coordinate-rigid `xChartToFraction` candidate remains separate at
[44f3f126715e57961d25dd4f3a9a451d3a0a911f](https://github.com/xiangyazi24/FLT/commit/44f3f126715e57961d25dd4f3a9a451d3a0a911f).
The equivalence is useful for its injectivity proof, but does not itself
identify the two original coordinate inclusions into FractionRing W.

## Verification and acceptance boundary

- PASS: source review, exact 51-declaration extraction, and reproduced harness hash
- PASS: bounded pinned Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05 check, exit 0, 15.2626 s, 2160428 KiB peak child RSS, one CPU/thread, 3 GiB and 60 s caps
- PASS: polynomial identities and algebra equivalence without extra harness parameters
- PASS: final domain transport with ordinary `[IsDomain W]` harness parameter, standing for the existing production instance
- PASS: printed axioms standard foundations only; no sorryAx/custom axiom
- NOT RUN: full FLT import graph and `ActualXChartEquivCheck.lean`; requested from lead

The exact production SHA-256 is
`b002466dc2e6dcf6de5197bc5f21714da13d259793d7cba9acf68aa3dcc743fd`.
The exact passed harness SHA-256 is
`62a57bba4c08820f9e66573b7747fe57c45d9db69c28c378e89d1c70860d5539`.
Manifest: `comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-xchart-equiv-manifest.json`.

Lead ownership and exclusive dot N25 research ownership remain as in r9.
Accepted affine helpers are unchanged. The next owned step is genuine
injectivity of the coordinate-rigid map, then its boundary-local extension.
Boundary valuations, projective product formula and N25 exclusion remain
open. The latest dispatch and accepted source refs were rechecked before
this delivery and remained at the exact pins above.
