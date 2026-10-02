# YZ local ring in the common function field

## Production candidate

`N25F_YZLocalFractionEmbedding.lean` constructs the actual map

`yzLocalToFraction : YZLocalRing →ₐ[ZMod 2] FractionRing W`

and proves, without new hypotheses:

- `yzLocalToFraction_injective`
- `yzLocalToFraction_isFractionRing`, for the explicit algebra structure induced by this map
- `yzLocalToFraction_algebraMap`, identifying the restriction to the actual Y chart with the proved Y/Z chart transition followed by the Z-chart common-field map
- `fraction_qy_ne_zero`
- `yzLocalToFraction_yX`: image of X/Y is qx/qy
- `yzLocalToFraction_yZ`: image of Z/Y is qz/qy
- `yzLocalToFraction_yzW`: image of W/Y is 1/qy
- `yzLocalToFraction_unique`: uniqueness among maps with the stated Y-chart restriction
- `yzLocalToFraction_yzZGerm`, `yzLocalToFraction_yzWGerm`: the coordinate identities for the existing named germs

The source also supplies the Z-open and Y-open common-field maps and their injectivity/fraction-field theorems.

The construction does not use the new YZ Dedekind or DVR instance. It uses the actual point's existing primality and Z/Y=1 evaluation, the accepted actual affine-overlap equivalence, and the accepted coordinate-rigid Z-chart field map. The Y chart itself is never assumed to be a domain. `Classical.choose` selects the universal localization extension from a proved existence theorem; the restriction and uniqueness theorems fix its coordinates. No arbitrary local-ring isomorphism or common-field-map assumption is introduced.

## What was actually checked

1. `GenericFractionExtension.lean`, receipt `generic-01.json`: PASS, 4.36 seconds, 2,190,648 KiB peak child RSS. Generic extension from an away-open fraction field to the canonical prime localization; standard-three axiom audit.
2. `AwayFractionCheck.lean`, receipt `away-03.json`: PASS, 11.13 seconds, 2,511,836 KiB peak child RSS. Actual curve equations and proved Y/Z overlap equivalence imported from the accepted emitted harness chain. Explicit zY≠0 premise for this isolated away-open check; three standard-three audits.
3. `CurvePointFractionCheck.lean`, receipt `point-04.json`: PASS, 17.53 seconds, 2,509,512 KiB peak child RSS. Actual curve equations and actual proved overlap equivalence, with a transparent arbitrary point `f : YChartRing →ₐ[ZMod 2] ZMod 2` and `hf : f yZ = 1`. This check proves zY≠0 from the point/equivalence, then proves the map, injectivity, fraction-field property, qy≠0, all three coordinate identities, and uniqueness. Nine audits are all exactly `[propext, Classical.choice, Quot.sound]`.

The emitted harness declares the previously established `[IsDedekindDomain W]` and `[Module.IsTorsionFree (Polynomial (ZMod 2)) W]` explicitly. These are fixture assumptions, not new production hypotheses.

## What remains unrun

The parameter-free production file has not been elaborated against the full actual FLT import closure. Its specialization uses the actual `yzPrime`, `YZLocalRing`, `yzPointEval`, `yzPointEval_yZ`, and existing named germs. `ActualYZLocalFractionEmbeddingCheck.lean` is supplied for that lead-side validation, including all 19 public declaration axiom audits. The two named-germ aliases are definitionally the checked coordinate identities but were not separately run against the full original germ declarations.

`make_production.py` records the specialization from the checked helper, away-map, and point-family proof bodies. `MANIFEST.json` contains SHA-256 hashes and the exact checked/unrun distinction.

## Resource discipline

Every compiler invocation used exactly one `with-compiler-slot` gate wrapping `check-lean`: one CPU, 3072 MiB Lean cap, 60-second compiler timeout, 180-second gate wait. All new Lean source/check headers set `synthInstance.maxHeartbeats 200000`. No broad build, cache update, or version change was performed. The compiler is Lean 4.31.0-rc2 and Mathlib is pinned to 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
