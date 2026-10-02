# N25 actual X-boundary local embedding

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; EXACT-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; new boundary prerequisite preserving accepted affine work

## Completed actual objects

`N25F_XLocalFractionEmbedding.lean` proves the actual point-local ring embeds
in the fixed W-chart function field, using the already delivered chart map
injectivity and the universal property of localization:

```lean
xLocalToFraction : XLocalRing →ₐ[ZMod 2] FractionRing W
xLocalToFraction_algebraMap (a : XChartRing) :
  xLocalToFraction (algebraMap XChartRing XLocalRing a) = xChartToFraction a
xLocalToFraction_injective : Function.Injective xLocalToFraction
xLocalToFraction_xWGerm :
  xLocalToFraction xWGerm = 1 / algebraMap W (FractionRing W) qx
```

All are in `MazurProof.N25F_XLocalFractionEmbedding`. The existing `xPrime`,
`XLocalRing`, and `xWGerm` definitions are unchanged. There is no new
production assumption, axiom, sorry, admission, or opaque geometry.

Required latest predecessor:
[00be9496255202155d8748f60621edbaec072d36](https://github.com/xiangyazi24/FLT/commit/00be9496255202155d8748f60621edbaec072d36),
which contains `N25F_XChartFractionInjective.lean` and records its map and
X/W-equivalence dependencies. This local embedding does not require the
separate pending DVR transport candidate.

## Verification boundary

PASS: generic localization proof (5.564 s); full 63-declaration actual-source
assembly including all three predecessor proof bodies and the actual local
prime/localization definitions (31.441 s, 2509768 KiB RSS, exit 0). Four public
axiom audits report only propext, Classical.choice, Quot.sound. One CPU/thread,
3072 MiB, 60-second bounds; Lean 4.31.0-rc2, Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05.

The accepted W Dedekind instance is transparently supplied as an ordinary
structural parameter in this source harness. The production imports supply
it; no premises are added to the production statement.

NOT RUN: full FLT import compilation and provided `ActualXLocalFractionCheck.lean`;
these await lead validation. Candidate SHA-256:
`f1cc3d83be175dbeb8388836f4e1546f0d0b658b7267f599b0d68faa2a2d548d`.
Passed harness SHA-256:
`fff0739f770eb78ceb704890fc32112728e32f3bd6c62166d67c8df8f2866738`.
Manifest: `comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-local-embedding-manifest.json`.

## Companion actual DVR result in this same packet

`N25F_XLocalDVR.lean` independently proves actual X-chart Dedekind structure,
xW nonzero, xW in xPrime, xPrime nonzero, the actual XLocalRing DVR instance,
and xWGerm nonzero. It depends on the map and chart-equivalence candidates,
not on chart injectivity or this local embedding. The existing source
`Ring.ord XLocalRing xWGerm = 3` remains unchanged.

PASS: its exact-definition harness (66 declarations and 3 original local
instances) and all six new axiom audits, exit 0, 31.941 s, peak child RSS
2761568 KiB, same pinned one-CPU/3072-MiB/60-second bounds. The accepted W
Dedekind instance is transparently a harness parameter; production adds none.
Only standard three axioms occur. Full imports are NOT RUN; the included
`ActualXLocalDVRCheck.lean` also requests compatibility with the accepted
order-three theorem. Candidate SHA-256:
`0d777634f8bddeaf55250e1ab0b1cccdf54641eff167b86d9b2f134e0928adb3`.

Coordinate-rigid fraction-field surjectivity/equivalence is now the next
owned prerequisite for transporting normalized valuations. Projective product formula and N25
exclusion remain open. Integration and acceptance remain with the lead.
