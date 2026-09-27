# FLT Codex run log — FLT task 01

Date: 2026-09-27
Repo: `/home/xhuan5/repos/flt-ai`

## ChatGPT questions

- Q8250, `flt1`: broad N25 frontier request, with `DOCTRINE.md` lines 1–140, the N25 entry from `MAZUR_MAP.md`, the relevant module list, and the exact obstruction declarations. Prompt: `/tmp/q_flt_n25_next.txt`. Status: pending.
- Q8252, `flt2`: compile-ready code for the first projective principal-divisor/product-formula step. Prompt: `/tmp/q_flt_n25_principaldivisor.txt`. Status: pending.
- Q8253, `flt4`: compile-ready code for the characteristic-three full closed-point grading. Prompt: `/tmp/q_flt_n25_threecarrier.txt`. Status: pending.
- Q8254, `flt3`: compile-ready code for the N25 adjunction seam connecting the degree-six hyperplane class to the canonical class. Prompt: `/tmp/q_flt_n25_adjunction.txt`. Status: pending.

All prompts were dispatched from the `flt` channel group. The answer integrations, target module build, and `#print axioms` check are pending.

## Tab-name rollover

After dispatch, the live status showed the `mbp` tab worker's desired FLT channels as `flt11`, `flt12`, `flt13`, and `flt14`. The legacy `flt1`–`flt4` entries remain only in bridge history; `/api/channels` currently lists no active FLT channel, and no fresh FLT heartbeats appear in `/api/status`. The four already-dispatched task IDs remain under their original names and are being harvested in place. Follow-up questions will wait until one of the new FLT channels is registered and ready.

## Recovered first-round answers and corrected source state

The four first-round tasks completed on their original channel names. Their task-bound answer commits were fetched read-only from `xiangyazi24/ask-gpt-git` and saved under `/tmp/flt_Q*.md`:

- Q8250 (`/tmp/q_flt_n25_next.txt`, task `ca73d7fa`, commit `9137cc2a7644533cebe0243b6c7c7dc9622d9b75`): recommended the pointwise boundary/local-order theorem. The current checkout already contains `wBoundaryHyperplaneDivisor_apply_eq_fullWLocalOrder` in `RationalPointsN25QuotientTwoWBoundaryLocalDivisor.lean`; the answer used an older source snapshot.
- Q8252 (`/tmp/q_flt_n25_principaldivisor.txt`, task `28190803`, commit `9a376da6c3b516f5d59fc152053518a09cb594d1`): supplied an abstract local-order packaging structure, without a concrete instance for the curve; not integrated.
- Q8253 (`/tmp/q_flt_n25_threecarrier.txt`, task `a4982cab`, commit `4b3cb1bec200b07e213dc9b6ef46bbb1c64a703f`): supplied the full characteristic-three orbit-carrier construction. Integrated in `N25F_Next.lean`, with the positive field degree indexed as `d + 1` following the local characteristic-two pattern.
- Q8254 (`/tmp/q_flt_n25_adjunction.txt`, task `09e0efd8`, commit `57a605e883141f26e932ec4f91988b5ec58c8139`): supplied a bounded-carrier interface and confirmed the remaining dualizing-sheaf and divisor/line-bundle comparison seams; not integrated.

## Updated tab names and follow-up tasks

Xiang confirmed the repaired FLT tabs are `flt11`–`flt14`. The bridge group also exposed `flt31`–`flt33`; automatic routing initially selected those for some follow-ups. Subsequent affinity-routed tasks targeted the repaired names, though the bridge later reassigned some pending tasks to `flt32`/`flt33`. Track by task ID and current bridge status; do not resubmit while any answer is in flight.

- Q8260, `/tmp/q_flt_n25_projective_divisor.txt`, task `86e933e7`: concrete projective divisor/product-formula step; currently processing on `flt31`.
- Q8261, `/tmp/q_flt_n25_three_carrier_audit.txt`, task `0a38b55a`: audit/fix the characteristic-three carrier code against local APIs; completed on `flt32`, answer retrieval pending.
- Q8262, `/tmp/q_flt_n25_adjunction_next.txt`, task `d7e60334`: next canonical/dualizing-sheaf theorem; currently pending on `flt33`.
- Q8263, `/tmp/q_flt_n25_height_one_equiv.txt`, task `1383476d`: upgrade the closed-point/maximal-ideal correspondence to height-one spectrum; currently pending on `flt31` after reassignment.
- Q8264, `/tmp/q_flt_n25_atom_sum_equiv.txt`, task `796fe97e`: split the full atom/divisor carrier into boundary and chart parts; submitted with affinity `flt13`, currently pending on `flt33` after reassignment.
- Q8265, `/tmp/q_flt_n25_three_bridge_followup.txt`, task `93e7436d`: transport the degreewise characteristic-three carrier to the existing degree-1-through-4 semantic bridge; submitted with affinity `flt12`, currently pending on `flt32` after reassignment.
- Q8266, `/tmp/q_flt_n25_local_order_degree.txt`, task `91c913d1`: package the existing pointwise W-order result with its degree-six effective divisor; submitted with affinity `flt14`, currently processing on `flt14`.

## Integrated module and checks

Created `N25F_Next.lean` with the full characteristic-three closed-point grading, using exact-period Frobenius orbits over `CommonField 3 (d + 1)` and an empty degree-zero fiber.

Build command:

```text
lake build FLT.Assumptions.MazurProof.N25F_Next 2>&1 | tail -5
```

Result: `Build completed successfully (8581 jobs).`

`lake env lean /tmp/flt_n25_next_axioms.lean` printed:

```text
'MazurProof.N25F_ThreeFullClosedPoints.fullClosedPointType25ThreeFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'MazurProof.N25F_ThreeFullClosedPoints.fullClosedPointGrading25Three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean FLT/Assumptions/MazurProof/MazurEndpointAudit.lean` still reports four custom axioms reachable from `MazurProof.mazur_torsion_bound`: `no_prime_order_ge_23`, `C13Sextic_affine_x_is_cuspidal`, `no_explicit_order25_obstruction`, and `no_raw_order49_tate_obstruction`. This helper does not yet discharge the N25 endpoint axiom.

## Q8262 answer review and current tab health

Q8262 arrived through the Drive fallback. Its proposed `globalCanonicalDifferentialModule25Two` duplicates work already present in this checkout: `globalKaehlerDifferentialModule` is the equalizer of the chart and overlap Kähler differential sheaves, and `globalKaehlerDifferentialIsoTwist`, `globalKaehlerDifferentialIsoAdjunctionTransitionLine`, and `globalKaehlerDifferentialIsoCurvePullback` are already defined in `RationalPointsN25QuotientTwoCanonicalDifferentialCech.lean`. No Q8262 code was integrated.

At the latest bridge check, worker `mbp` was online and tabs `flt11`–`flt14` were idle, but each reported `connector_state = disconnected`, no conversation URL, and no recent channel heartbeat (`last_seen_s = 0`). The bridge's safe allocator therefore cannot currently dispatch to those tabs. Existing work on `flt31`/`flt33` remains in flight or queued while worker `uisai2` is offline. No new GPT request was sent into this unhealthy state.

## Follow-up: affine principal divisor on the nonboundary carrier (2026-09-27)

Re-read Q8252 from `/tmp/flt_Q8252.md` (answer commit `9a376da6c3b516f5d59fc152053518a09cb594d1`). It gives a sound abstract package assuming finite support and local additivity, but does not construct the local orders for arbitrary rational functions or prove the projective product formula. No Q8252 code was copied into the development.

Added `N25F_NonBoundaryPrincipalDivisor.lean`. It upgrades the existing nonboundary-atom/maximal-ideal equivalence to `IsDedekindDomain.HeightOneSpectrum WChartQuotient`, identifies the residue degree, and reindexes the existing affine `CurveDedekindDivisor.principalDivisor` onto the nonboundary full-atom subtype. It does not claim boundary coefficients or the full projective degree-zero theorem.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
```

Result: `Build completed successfully (8642 jobs).`

Axiom check (`lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_nonboundary_axioms.lean`):

```text
fullNonBoundaryAtomEquivHeightOne depends on [propext, Classical.choice, Quot.sound]
residueDegree_fullNonBoundaryAtomEquivHeightOne depends on [propext, Classical.choice, Quot.sound]
nonBoundaryPrincipalDivisor depends on [propext, Classical.choice, Quot.sound]
nonBoundaryPrincipalDivisor_apply depends on [propext, Classical.choice, Quot.sound]
```

Bridge correction: the coordinator identified `http://127.0.0.1:18801` as the live endpoint. This shell inherits tmux window `dm`, so the exact command without a window override reports no `dm` channels. Setting `ASK_WINDOW=flt` selects the FLT group while leaving tab selection automatic. Q8278 (prompt `/tmp/q_flt_n25_atom_sum_equiv.txt`, task `b274ca6c`) was submitted to flt14; Q8279 (prompt `/tmp/q_flt_n25_three_bridge_followup.txt`, task `98bb2434`) was queued to flt14 after the four live flt tabs became busy. Both use GDrive delivery; their answer logs are `/tmp/ans_flt_n25_atom_sum_equiv_18801.txt` and `/tmp/ans_flt_n25_three_bridge_followup_18801.txt`.


### Run-directory and prompt freshness corrections

The axiom probe and an unsubmitted revised bridge prompt are stored under `/home/xhuan5/tmp/flt-ai/codex-20260927-n25/`, following the uisai2 scratch-path rule. The probe was rerun from there with `TMPDIR` set to the run directory and exited 0 with the same four standard-axiom results.

Q8279 uses the older `/tmp/q_flt_n25_three_bridge_followup.txt`, which says the characteristic-three full carrier is not defined. That premise predates `N25F_Next.lean` and is false in the current checkout. Do not integrate its proposed carrier construction; check any API observations against the current source. A corrected, current-source prompt is prepared at `/home/xhuan5/tmp/flt-ai/codex-20260927-n25/scripts/q_flt_n25_three_bridge_current.txt` and has not been submitted.

### Auto-push during ChatGPT dispatch

Inspection of `~/repos/ask-gpt-git/scripts/ask-gpt.py` showed its project auto-push path at lines 1611–1632: with a git-drop target, it pushes commits ahead of upstream unless `ASK_NO_PUSH=1`. Q8280 was launched without that guard, and the script reported `auto-pushed 2 commits (HEAD=30974b90e5)`. `git ls-remote xiang refs/heads/verify-sorry-restore` confirmed the remote branch now matches `30974b90e593c09cad9ce27c380f6294c17762ce`; the two pushed commits are `b95d04fb97` and `30974b90e5`. This conflicts with the lane card's no-push rule. No remote history rewrite was attempted. Future ChatGPT dispatches must include `ASK_NO_PUSH=1`.

### Live-tab queue rotation after Q8279

Q8280 (current-source prompt `/home/xhuan5/tmp/flt-ai/codex-20260927-n25/scripts/q_flt_n25_three_bridge_current.txt`, task `eb777156`) was dispatched to flt13 and entered processing. During routing, the bridge automatically moved older Q8264 and Q8265 work off stale flt31: Q8264's atom-sum task was processing on flt11, and Q8265's characteristic-three bridge task remained queued there. Consequently Q8278 repeats Q8264, and Q8279 repeats Q8265 with an outdated premise. Q8280 is the grounded current-source bridge task. Do not treat these overlapping prompts as independent results; verify each answer against the current checkout before integration.

Coordinator correction (lane-card rule 5): ask-gpt auto-push to Xiang’s `xiang` fork is intended to provide current source to ChatGPT; never push to `origin` and never force-push, and do not set `ASK_NO_PUSH=1`.
