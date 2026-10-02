# N25 actual Z/W chart equivalence

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; EXACT-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; independent boundary prerequisite preserving accepted r9 work

## Completed mathematics

`N25F_ZChartWChartEquiv.lean` proves:

```lean
MazurProof.N25F_ZChartWChartEquiv.zChartAlgEquivWChart :
  ZChartRing ≃ₐ[ZMod 2] W
```

and exports actual Z-chart domain and Dedekind instances by transport from W.
The binary transform S(X,Y,Z,W)=(Y+Z+W,Y+Z,X,Z) preserves Q and sends C to
C+X*Q; its inverse preserves Q and sends C to C+Z*Q. Both actual quotient
maps, six coordinate formulas, and inverse laws are proved. Their parameters
are genuine chart quotient elements, not a replacement carrier. The source
keeps zX/zY private, so this module exposes its own names for the exact same
chartMap expressions. It uses the existing public ZChartRing and zW.

This is an automorphism-induced affine-chart equivalence. A coordinate-rigid
Z-chart field embedding and Z/YZ boundary valuations are still separate next
steps; this result does not assume or claim them.

## Actual verification

PASS: first-attempt pinned check, exit 0, 13.587 s, 2428904 KiB peak child RSS,
one CPU/thread, 3072 MiB cap, 60-second timeout, shared flock gate. No warnings.
The 49-declaration harness uses 11 exact-pin source files independently
refetched and checked against Git blob SHA-1 and SHA-256. The algebra
equivalence and polynomial identities are unconditional; only final domain
and Dedekind transports use the ordinary existing-W-Dedekind harness parameter.
Axiom audits contain only propext, Classical.choice, Quot.sound, no sorryAx.
No production premise, custom axiom, sorry, admit, or native_decide is added.

Lean 4.31.0-rc2, Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
Production SHA-256:
`6058bc2512b100dafc39a4c25356ed66c2491ede1ab8e73e45810979f6adbd23`.
Passed harness SHA-256:
`feae2ebd3182e949d8d606b893fae077146f27b5a63d932ebf4411c124461486`.

NOT RUN: full FLT imports and supplied `ActualZChartEquivCheck.lean`.
Lead acceptance remains required. Manifest:
`comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-zchart-equiv-manifest.json`.
Source snapshots can be obtained from their exact URLs and verified hashes
in `source-inputs.json`; they are not duplicated in the evidence packet.

No preceding candidate or accepted helper was modified. The X-boundary
fraction-field order is being proved independently against the actual
X-local DVR; the projective product formula and N25 exclusion remain open.
