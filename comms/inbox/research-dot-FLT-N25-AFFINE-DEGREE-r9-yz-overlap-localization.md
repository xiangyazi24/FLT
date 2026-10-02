# N25 actual overlap-localization map

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: SOURCE-CANDIDATE; GENERIC-CHECK-PASS; ACTUAL-LOCAL/FULL-IMPORTS-NOT-RUN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 1eab90d583a58211846c1b69e24e5ed73a59ce4d
FIXTURE_SOURCE_BASE: f0eb8381677bc483bddd93826871845030dd5c0e
LAST_DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; next concrete overlap producer in the exclusive N25 lane

`N25F_YZOverlapLocalization.lean` supplies in its matching MazurProof namespace:

```lean
zYOpenToYZLocal : Localization.Away zY →ₐ[ZMod 2] YZLocalRing

zYOpenToYZLocal_invSelf :
  zYOpenToYZLocal (IsLocalization.Away.invSelf zY : Localization.Away zY) = yzZGerm
```

It also proves the exact algebraMap restriction. The construction uses the
previously proved actual unit image and the localization universal property;
there is no new premise or assumed isomorphism. The unchanged predecessor is
[295b9a6e6fbc0cae9e2fb60a8423dc9b48eccb9c](https://github.com/xiangyazi24/FLT/commit/295b9a6e6fbc0cae9e2fb60a8423dc9b48eccb9c).

PASS: complete generic-algebra feedback, 7.587 s, 2451940 KiB RSS, three new
standard-three axiom audits, one CPU/thread, 3072 MiB, 60-second bounds.
Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
The target algebra and unit condition are explicit fixture parameters, not
production assumptions. The actual YZLocalRing specialization/full imports
are NOT RUN; ActualYZOverlapLocalizationCheck.lean requests that gate.
No sorry, admit, custom axiom or native_decide is added.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-yz-overlap-localization-manifest.json.
The actual affine-overlap equivalence is the next owned proof, followed by
localization comparison for YZLocalRing. The full product formula and N25
exclusion remain open. Source integration and acceptance stay with the lead.
