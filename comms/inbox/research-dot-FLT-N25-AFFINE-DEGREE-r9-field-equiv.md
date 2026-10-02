# N25 coordinate-rigid X/W function-field equivalence

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; EXACT-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; new boundary prerequisite preserving accepted r9 work

## Completed statement and coordinate structure

`N25F_XChartFractionEquiv.lean` proves the actual coordinate-rigid fraction-field
lift is bijective and packages:

```lean
MazurProof.N25F_XChartFractionEquiv.xChartFractionAlgEquiv :
  FractionRing XChartRing ≃ₐ[ZMod 2] FractionRing W
```

Its restriction to XChartRing is exactly the existing `xChartToFraction`.
The accompanying theorem `xChartToFraction_isFractionRing` proves:

```lean
letI : Algebra XChartRing (FractionRing W) :=
  xChartToFraction.toRingHom.toAlgebra
IsFractionRing XChartRing (FractionRing W)
```

No competing global scalar action is installed. The proof shows the field
range contains qx by inverting the image of xW, then qy and qz from the two
coordinate ratios. Induction on the actual quotient polynomial ring covers
W; fraction representation covers FractionRing W. No generation, surjectivity,
function-field, or product-formula premise is assumed.

The sole new import is the unchanged chart-injectivity candidate from
[00be9496255202155d8748f60621edbaec072d36](https://github.com/xiangyazi24/FLT/commit/00be9496255202155d8748f60621edbaec072d36).
The later local embedding and DVR pair at
[ac7bb62b24aa0065b7e7d63fd726abdcae346ee7](https://github.com/xiangyazi24/FLT/commit/ac7bb62b24aa0065b7e7d63fd726abdcae346ee7)
remain unchanged and combine with this field property in the next step.

## Actual verification

PASS: exact-source proof assembly and reconstruction, 14 source snapshots
and three unchanged prerequisite hashes reverified, all eleven public axiom
audits standard propext/Classical.choice/Quot.sound only. Check exit 0,
48.411 s, 2515816 KiB peak child RSS, one CPU/thread, 3072 MiB cap, 60-second
timeout. Pinned Lean 4.31.0-rc2 / Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05.

The harness supplies ordinary W-Dedekind structure standing for the accepted
source instance. Production adds no premise. Full FLT imports and
`ActualXChartFractionEquivCheck.lean` are NOT RUN and await lead validation.
No sorry, admit, custom axiom, or native_decide is introduced.

Production SHA-256:
`4809cd7b5d8db32b638c8339a287abf5eb2a1754dca2b174c808b6f9b7960f99`.
Passed harness SHA-256:
`f57fe127aafc8f04721675974801c323eba429977c69e55f8547d944ff20355b`.
Manifest: `comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-field-equiv-manifest.json`.

The next owned X-boundary step is the genuine fraction-field length order
`Ring.ordFrac`, using the actual local germ order three to derive the pole
order of qx. The other boundary charts and projective product formula remain
open. Lead integration and acceptance remain authoritative; no N25 root
axiom discharge is claimed.
