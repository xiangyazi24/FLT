# N25 actual Z-chart field map and YZ-overlap unit prerequisite

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: TWO-CANDIDATES; Z-MAP-SOURCE-MICROCHECK-PASS; YZ-UNIT-GENERIC-PASS; FULL-IMPORTS-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; concrete boundary prerequisites preserving accepted r9 work

## 1. Actual Z-chart map: exact-source check PASS

`N25F_ZChartFractionMap.lean` proves in its matching MazurProof namespace:

- `algebraMap_Rz_X`: the established F2[z] algebra sends Polynomial.X to actual qz
- `qz_ne_zero` and `fraction_qz_ne_zero`, using accepted torsion-freeness
- `zChartToFraction : ZChartRing →ₐ[ZMod 2] FractionRing W`
- The exact zX↦qx/qz, zY↦qy/qz, zW↦1/qz formulas

The actual coefficient algebra, plane relation/elimination proofs, and bridge
coordinate identity are included in the source harness. In particular,
algebraMap_Rz_X is proved unconditionally, rather than supplied as a hypothesis.
The nonvanishing proof uses the existing normalization torsion-free instance;
no binary-point witness or new nonzero assumption is claimed. The map scales
the universal W-point and lifts through the actual Z-chart quotient.

The unchanged chart-equivalence predecessor is at
[6999499b1155d42c8ac17876012b3625d1a59b1e](https://github.com/xiangyazi24/FLT/commit/6999499b1155d42c8ac17876012b3625d1a59b1e).

PASS: 83-declaration exact-source harness, 14 accepted source files plus the
public predecessor coordinates, all source blob hashes checked, all eight
printed results standard-three axioms only. Exit 0, 19.450 s, 2435488 KiB peak
child RSS, one CPU/thread, 3072 MiB and 60-second bounds, shared flock gate.
The accepted torsion-free and W-domain instances are explicit ordinary
harness parameters; production imports supply them with no added premise.

Production SHA-256:
`811973b2ecc662a70eebe337f445910be9707a8598a4503edefddda40be2d784`.
Passed source SHA-256:
`6aecc9601b3be01dfdc253411a36b4c4b96ce7bf9766c1724ae758961a565dbe`.

## 2. Actual YZ-overlap unit: generic check PASS, specialization NOT RUN

`N25F_YZLocalZUnit.lean` defines the germ of the existing public coordinate yZ
in the existing YZLocalRing, and proves:

```lean
MazurProof.N25F_YZLocalZUnit.yzZGerm_isUnit : IsUnit yzZGerm
```

This is a direct use of the accepted actual evaluation yzPointEval_yZ=1:
yZ is outside the actual point prime, so localization makes it invertible.
No substitute local ring or chart-overlap isomorphism is assumed.

PASS: source review against the exact original definitions and the generic
localization/kernel proof at the pinned compiler (2.312 s, 2127632 KiB RSS,
standard-three only). NOT RUN: actual specialized module/full imports.
This packet deliberately makes the weaker verification claim for this tiny
candidate; `ActualYZLocalZUnitCheck.lean` requests the real-import check.
Production SHA-256:
`25aaa6a9a1e13f3798add495dc3256d87adf94e85ea4b07b2c6550b8ed61071f`.

## Shared acceptance boundary

Lean 4.31.0-rc2, Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
No production premise, custom axiom, sorry, admit, or native_decide added.
No earlier file changed. Both supplied full-import validation files are
NOT RUN and await lead acceptance. Manifest:
`comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-zfraction-map-manifest.json`.
Source snapshots are existing repository files at the manifest's exact pins;
they are not duplicated in this packet.

The next Z step is genuine map injectivity/fraction-field equivalence. The
YZ unit enables a later proof across its Y/Z chart overlap, which is still
open. The full boundary coefficient triple, projective product formula, and
N25 exclusion remain open; lead retains integration and final acceptance.
