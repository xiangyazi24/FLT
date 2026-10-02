# N25 first actual shared-field boundary order

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; INCREMENTAL-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; genuine boundary-order producer preserving accepted r9 work

## Completed mathematics

`N25F_XBoundaryOrder.lean` proves that the fixed FractionRing W is a fraction
field of the actual XLocalRing for the explicit coordinate-rigid local map.
It then defines the local length-order extension using existing `Ring.ordFrac`
and its signed additive coefficient on nonzero functions:

```lean
xBoundaryOrder : Additive ((FractionRing W)ˣ) →+ ℤ
```

The source theorem `Ring.ord XLocalRing xWGerm = 3` and the proved image
`xWGerm ↦ 1/qx` give the exact pole order:

```lean
xBoundaryOrder (Additive.ofMul (Units.mk0
  (algebraMap W (FractionRing W) qx) fraction_qx_ne_zero)) = -3
```

All five public declarations are in `MazurProof.N25F_XBoundaryOrder`:
`xLocalToFraction_isFractionRing`, `xLocalFractionOrder`, `xBoundaryOrder`,
`xLocalFractionOrder_xWGerm`, `xBoundaryOrder_qx`.
The source scalar tower is proved from `xLocalToFraction_algebraMap`; the
field and local DVR are the actual objects, with no chosen substitute or
opaque geometric hypothesis. Production adds no premise, axiom, sorry,
admit, native_decide, or product-formula assumption.

Dependencies are the unchanged field-equivalence candidate at
[ebadf93d13b02ec5fbffcac0036bb9a02cbaa591](https://github.com/xiangyazi24/FLT/commit/ebadf93d13b02ec5fbffcac0036bb9a02cbaa591)
and local embedding/DVR pair at
[ac7bb62b24aa0065b7e7d63fd726abdcae346ee7](https://github.com/xiangyazi24/FLT/commit/ac7bb62b24aa0065b7e7d63fd726abdcae346ee7).
The independent Z/W equivalence at
[6999499b1155d42c8ac17876012b3625d1a59b1e](https://github.com/xiangyazi24/FLT/commit/6999499b1155d42c8ac17876012b3625d1a59b1e)
is preserved and is not a dependency of this result.

## Precise bounded verification boundary

PASS: generic logarithm/inverse-order lemma (2.884 s), unchanged predecessor
module emission (49.164 s) and import smoke (3.151 s), and the new incremental
actual-source harness (18.391 s, exit 0, 2765412 KiB peak child RSS).
All five new public axiom audits report only propext/Classical.choice/Quot.sound.
The compiler remains one CPU/thread, 3072 MiB, 60-second cap; the outer flock
gate only serializes jobs. No memory or time limit was raised.
Lean 4.31.0-rc2; Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05.

The harness imports the verified exact-source field-equivalence .olean and
adds 13 verbatim original local definitions, the complete DVR/local-embedding
bodies, and this candidate. It transparently represents accepted W Dedekind
structure as a parameter. For the final two theorems only, it represents the
accepted exact theorem `Ring.ord XLocalRing xWGerm = 3` as an ordinary proof
parameter, rather than rebuilding its existing Artin-quotient proof closure.
`accepted-order-input.json` records its exact source body, line399, and hash.
The production proof directly uses that accepted theorem, adding no premise.

NOT RUN: full FLT import compilation and `ActualXBoundaryOrderCheck.lean`.
Lead acceptance remains required. Earlier failed diagnostics are retained
and explicitly excluded from acceptance evidence.

Candidate SHA-256:
`53b8a670cd8111e21c7d99bc72f47122b55deb4e46d6b3555d0a6f3c5cad84c9`.
Passed incremental source SHA-256:
`55e47150fc5d8fc502a9f1d52ef4523f15cc0aa9f820921b662abdc021552044`.
Manifest: `comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-xboundary-order-manifest.json`.

This gives one genuine boundary coefficient on the fixed function field.
The Z/YZ coefficients, full projective principal-divisor assembly, product
formula and N25 exclusion remain open. The next owned step is the concrete
Z-chart field map with source-derived qz nonvanishing. Acceptance and all
source integration remain with the lead.
