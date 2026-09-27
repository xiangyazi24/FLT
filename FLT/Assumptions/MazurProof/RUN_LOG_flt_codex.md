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


## Q8264/Q8266 review and projective divisor carrier split (2026-09-27)

Read Q8264 (answer `947acbcc`) and Q8266 (answer `b4697292`). Q8264 supplied the boundary/nonboundary atom partition and induced signed-divisor Finsupp equivalence. Its suggested module reused `N25F_Next.lean`, already occupied by the characteristic-three carrier, and opened a namespace absent from the current source. Adapted it into `N25F_ProjectiveDivisorSplit.lean`, used the current `RationalPointsN25QuotientTwoWOpenPrimeSurjective` namespace, and opened the boundary-closed-point namespace. Removed unused imports of `CurveDivisorPicard` and `RationalPointsN25QuotientTwoWBoundaryLocalDivisor`; the latter first caused an unrelated typeclass-heartbeat timeout while compiling `WBoundaryXLocal`.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorSplit
```

Result: `Build completed successfully (8638 jobs).`

Axiom check (`lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_projective_split_axioms.lean`):

```text
boundaryNonBoundaryEquivFullAtom depends on [propext, Classical.choice, Quot.sound]
fullAtomEquivBoundaryNonBoundary depends on [propext, Classical.choice, Quot.sound]
fullDivisorEquivBoundaryCoefficientsChart depends on [propext, Classical.choice, Quot.sound]
```

Q8266 packages the existing `wBoundaryHyperplaneDivisor`, its already-proved degree-six certificate, pointwise `fullWLocalOrder` coefficients, and support. Its proposed unique-existence wrapper was not integrated; it does not advance the arbitrary-rational-function divisor bridge and was not compiled.

Q8282 asks for the local `Ring.ord` interpretation of affine principal-divisor coefficients; submitted to flt14, task `96aab523`, processing. ask-gpt auto-pushed three commits through the intended `xiang` remote at `HEAD=f9c36f9107`; no push to `origin` or history rewrite occurred. Q8283 requests a source audit of the Q8280 characteristic-three bridge answer; submitted to flt13, task `892c159b`, processing. Q8263 reported connector-delivery failure; no resend was made. At the latest check flt11 remained connected with one task processing, and no Q8263 answer file had appeared.


## Q8265 answer review (2026-09-27)

Read Q8265 answer `2f36c341`. Its bridge construction is based on the earlier carrier index `CommonField 3 d`; the current committed `N25F_Next.lean` uses `CommonField 3 (d + 1)`. Q8265 therefore does not typecheck against the current carrier as written. Q8280 supplies the corresponding current-index construction and Q8283 is auditing that code against the checkout. No Q8265 code was integrated.


## Q8261 carrier audit answer (2026-09-27)

Read Q8261 answer `e89b8a56`. It confirms the `d + 1` characteristic-three carrier shape and suggests more explicit elaboration in the subtype-finiteness proof. The current `N25F_Next.lean` was already built locally (`Build completed successfully (8581 jobs)`), and the answer could not compile this checkout. No code was changed; the suggested proof-style rewrite is unnecessary for the compiled source.

## Characteristic-three descent and closed-point bridge (2026-09-27)

Reviewed the returned Q8286/Q8287 static audits. Q8286's recovered Q8279 source consistently uses the actual `CommonField 3 (d + 1)` carrier, supports the degreewise fixed-field/orbit route, and does not claim compilation. Q8287 independently confirms the generic fixed-point equivalence uses the stored coefficient embedding. Both distinguish this point-set bridge from the actual Picard/Riemann--Roch conclusion. Q8285's source review found no current consumer requiring a scheme-level canonical/Kähler line; it identifies the F3 affine-chart Jacobian unit-ideal theorem as the next geometric interface, using `normalized_projective_point_not_singular`.

Q8283's task ledger reported a Drive drop, but the discovered full document ID resolves to a document containing only `ANSWER Q8283 4cdbd2fd` (24 bytes); `get_document`, text fetch, and revision inspection found no audit body. No Q8283 claim or code was integrated. An initial Q8288 dispatch created a ledger row but no bridge task; `/api/status` showed no matching in-flight ID. The same source-grounded recursion-depth prompt was then submitted successfully as Q8289.

Added `N25F_ThreeDegreeDescent.lean`, separating the coherent realization of `CommonField 3 (d + 1)` and the equivalence with the common-field Frobenius fixed-point subtype. The module retains the fixed-point value and periodicity projections. Q8291's static source audit found no name, type, or API correction.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ThreeDegreeDescent
```

Result: `Build completed successfully (8603 jobs).`

Axiom check (`lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_three_degree_descent_axioms.lean`):

```text
degreeToCommonFixedEquiv depends on [propext, Classical.choice, Quot.sound]
degreeToCommonFixedEquiv_val depends on [propext, Classical.choice, Quot.sound]
degreeToCommonFixedEquiv_periodic depends on [propext, Classical.choice, Quot.sound]
```

The first targeted build of `N25F_ThreeFullClosedPointBridge.lean` failed at the concrete `rfl` degree equalities and inverse-law `change` steps with maximum-recursion-depth errors. Q8289 proposed transporting exact ghost slots through an abstract grading equivalence via `Equiv.sigmaCongr` and `Equiv.cast`; this keeps quotient-backed closed-point fibers opaque during dependent transport. Split the fixed-field declarations into the new descent module, removed the unnecessary direct middle-Riemann--Roch import from the structural bridge, and replaced the concrete proof-erasing transport with that generic helper.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ThreeFullClosedPointBridge
```

Result: `Build completed successfully (8604 jobs).`

Axiom check (`lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_three_closed_point_bridge_axioms.lean`):

```text
degreeCurvePointEmbeddingToCommon12_minimalPeriod depends on [propext, Classical.choice, Quot.sound]
orbitClassEquivDegreeToCommon12 depends on [propext, Classical.choice, Quot.sound]
exactGhostSlotEquivCommon12ToFull depends on [propext, Classical.choice, Quot.sound]
fullClosedPointBridge25ThreeLE4 depends on [propext, Classical.choice, Quot.sound]
```

This closes the degree-at-most-four point-set classification bridge over the full characteristic-three carrier. It does not yet construct arbitrary rational-function projective divisors or discharge the actual Picard/Riemann--Roch inputs. Q8282's local `Ring.ord` bridge remains in flight. A source audit of Q8285's proposed characteristic-three polynomial derivative interface was dispatched for the next chart-Jacobian step.

## Nonboundary chart local order (2026-09-27)

Q8282 returned a 503-line proposed `N25F_ChartLocalOrder.lean`; Q8290's static audit confirmed the valuation sign, ramification direction, and cited Mathlib interfaces, and identified `ChartLocalRing25Two`'s local-prime instance as a likely elaboration risk. Materialized the draft at `FLT/Assumptions/MazurProof/N25F_ChartLocalOrder.lean`.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ChartLocalOrder
```

Result: failed. The first error is failure to synthesize `(fullNonBoundaryPrimeIdeal A).IsPrime` at the `Localization.AtPrime` alias (line 35); dependent ring/algebra instance failures cascade through the local-order declarations. The build log is `/tmp/n25_chart_local_order_build.log`. Q8290 was source-only and did not compile the module. A compile-fix question was prepared at `/tmp/q_flt_n25_chart_local_order_compile.txt`; all live FLT tabs were occupied at the latest status check, so it has not been dispatched or assigned a Q number. No axioms were checked because the module does not build.

## Nonboundary chart-local order follow-up (2026-09-27)

The earlier failure record above is superseded by the successful repair below. Q8303 (answer `9e513d25`, task `bb82cd40`, tab flt13) supplied three source-level changes to `N25F_ChartLocalOrder.lean`: install the indexed prime instance before `ChartLocalRing25Two`, move the local `P.IsPrime` instance before defining `O := Localization.AtPrime P`, and normalize the valuation through the canonical DVR maximal ideal. The current checkout uses Mathlib revision `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Q8310's source-only audit (answer `2ea1177c`) could not read this local module and raised a conditional classical-scope concern. The exact local module compiled successfully, so that concern required no source change. Its alternate-revision ramification warning was not applied to this pinned checkout.

Q8306 (answer `c8b84bdb`, task `8c3267cd`, tab flt14) supplied an additive hom wrapper around `localFractionOrder`. Q8307 (answer `7257b92f`, task `c6047a82`, tab flt33) supplied the criterion `localElementOrder A a = 0 ↔ a ∉ fullNonBoundaryPrimeIdeal A` for nonzero `a`. Both blocks were appended. The first build after appending exposed a missing namespace open for `fullNonBoundaryPrimeIdeal`; after adding that open, the targeted build passed.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ChartLocalOrder
```

Result: `Build completed successfully (8643 jobs)`. Full output is `/tmp/n25_chart_local_order_build4.log`.

Axiom probe: `lake env lean /tmp/n25_chart_local_order_axioms.lean`:

```text
MazurProof.N25F_ChartLocalOrder.globalFactorCount_eq_localElementOrder depends on [propext, Classical.choice, Quot.sound]
MazurProof.N25F_ChartLocalOrder.localElementOrder_eq_zero_iff_not_mem depends on [propext, Classical.choice, Quot.sound]
MazurProof.N25F_ChartLocalOrder.localFractionOrderHom depends on [propext, Classical.choice, Quot.sound]
MazurProof.N25F_ChartLocalOrder.nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder depends on [propext, Classical.choice, Quot.sound]
```

No new assumptions or proof placeholders were introduced. Q8317 (task `8b31e017`, flt31) requests the characteristic-three formal-Jacobian bridge; Q8318 (`4bc8b98a`, flt11) requests the affine-chart Jacobian bridge; Q8319 (`64b75224`, flt12) requests the function-unit criterion for local order; Q8320 (`ea7f28bc`, auto-queued on flt31 while the group was saturated) requests the projective principal-divisor degree-zero bridge. All four remain pending.

Q8304 (task `625d9bb3`, flt32) remains in processing for the characteristic-three effective-divisor counts. Q8305 (answer `99407791`, task `d4097b8c`, flt11) returned the physical-degree point decomposition module and is awaiting source review/build. Q8309 (task `aa11ce53`, flt14) remains in processing on the boundary function-field/local-order bridge. Q8311 (answer `3b6948d4`, task `b278330b`, flt12) returned the weighted projective-divisor degree split module and is awaiting source review/build.

## Projective divisor degree split (2026-09-27)

Read the returned Q8311 weighted projective-divisor degree module (`/tmp/gpt/flt/Q8311.md`, task `b278330b`). Materialized it as `N25F_ProjectiveDivisorDegree.lean`. The first targeted build failed in the single-add calculation and the explicit transported-degree formula. Q8321 (task `b874bd3b`, prompt `/tmp/q_flt_n25_projective_degree_compile.txt`) supplied exact proof repairs; Q8316 independently warned about the unrestricted simp site in `splitDegree_apply_components`.

Applied the product-projection rewrites after `hsplit`, replaced the definitional `simp [splitDegree, D]` with `rfl`, and composed the final component equalities directly. Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree
```

Result: `Build completed successfully (8639 jobs)`. Full output: `/tmp/n25_projective_divisor_degree_build2.log`.

Axiom probe: `lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_projective_divisor_degree_axioms.lean` printed only `[propext, Classical.choice, Quot.sound]` for the exported degree definitions and theorems, including `divisorDegree_eq_boundary_add_chart` and `splitDegree_apply`.

Q8312's source-only review confirms Q8303's earlier prime-instance placement is the required prerequisite for the support criterion and recommends no further change to that theorem. Q8308's source-only review finds no semantic patch needed for the additive local-order hom wrapper. Q8323 independently confirms the proposed Q8322 `Subtype.ext_iff.mp hPQ` repair is type-correct, without claiming a local build.

## Physical-degree decomposition and formal-Jacobian repair review (2026-09-27)

Materialized Q8305 (answer `99407791`, task `d4097b8c`) as `N25F_ThreePhysicalDegreeDecomposition.lean`. Q8322 (task `05e71cea`) proposed `Subtype.ext_iff.mp hPQ` for the injectivity branch. The targeted build rejected that one-line term: its result did not unfold through `exactPeriodicPointToAmbientThree` to the fixed-point embedding equality required by injectivity. Q8323 (answer `6072e474`) statically endorsed the one-line term but did not build this local source. Replaced the ambiguous projection with Q8322's explicitly typed `congrArg` on the target exact-period subtype. The targeted build then passed:

```text
lake build FLT.Assumptions.MazurProof.N25F_ThreePhysicalDegreeDecomposition
```

Result: `Build completed successfully (8582 jobs)`. Full output: `/tmp/n25_three_physical_degree_build3.log`.

Axiom probe: `lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_three_physical_degree_axioms.lean` printed only `[propext, Classical.choice, Quot.sound]` for the exported physical-field, point-embedding, exact-period, and closed-slot equivalences. Q8335 (task `3e41b06c`, prompt `/tmp/q_flt_n25_three_physical_degree_compile2.txt`) was sent with the exact failed diagnostic and the explicit fallback for follow-up; it remained pending when the successful build was recorded.

Q8330 (answer `57221e1c`, task `22c865a5`) independently audited Q8324's proposed formal-Jacobian repairs. It found the evaluated-numeral bridge and all six `Fin 4` comparisons type-correct at source level, with no statement or polynomial change, but did not run Lean. It noted the abbreviated compiler excerpt did not establish Q8324's claimed unused-`h2` diagnostic and that the original `hzero` binders already infer `Fin 4`; the replacement `by decide` proofs remain the substantive fix. The patch still needs local application and a targeted build.

Current compile/audit tasks: Q8329 (task `f60f302d`, prompt `/tmp/q_flt_n25_chart_local_unit_compile.txt`) requests a repair for `N25F_ChartLocalUnitCriterion`; Q8331 (task `71b9c6f9`, prompt `/tmp/q_flt_n25_projective_degree_repair_audit.txt`) audits Q8321's projective-degree proof repairs; Q8334 (task `2640dff1`, prompt `/tmp/q_flt_n25_projective_degree_semantic_audit.txt`) audits the degree formula's mathematical meaning. Q8325/Q8326 remain the independent affine-Jacobian and chart-unit source audits. These requests use the auto-allocator with no pinned tab.

## Characteristic-three formal Jacobian bridge (2026-09-27)

Q8317's returned code for `N25F_ThreeFormalJacobianBridge.lean` was materialized. Its prompt had one transcription error in a prose gradient component; the source module itself retains the existing `-P.z - P.w` component. The first targeted build exposed the polynomial-evaluation image of `2` and closed `Fin 4` comparison goals. Q8324 (task `14bdb2cb`) supplied a local evaluated-numeral equality and `by decide` comparisons; Q8330 (answer `57221e1c`) independently checked the correction against the supplied source and diagnostics. Applied those proof-only changes without changing equations, gradients, or theorem statements.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ThreeFormalJacobianBridge
```

Result: `Build completed successfully (8576 jobs)`. Full output: `/tmp/n25_three_formal_jacobian_build2.log`.

Axiom probe: `lake env lean /home/xhuan5/tmp/flt-ai/codex-20260927-n25/probes/n25_three_formal_jacobian_axioms.lean` printed only `[propext, Classical.choice, Quot.sound]` for all exported derivative, formal-minor, and normalized-point nonvanishing declarations.

Read Q8328 (answer `54fa41f5`), an X-boundary function-field comparison analysis. It gives the coordinate-transition orientation and identifies a real obstruction to mapping the W/X overlap localization into `XLocalRing`, since the overlap inverts `xW` while the local germ has order three and is not a unit. It explicitly lacks current-checkout evidence and does not prove the desired fraction-field equivalence. Its warning that order three alone does not establish `xWGerm ≠ 0` is retained. No Q8328 code was integrated.

Q8332 (answer `47051de4`) source-audited the Q8318 affine-chart Jacobian proposal. It identifies four coordinate-equation evaluation wrappers whose binders must be `[Field K]`, matching the current exported equation definitions, and recommends no broad refactor or added characteristic hypothesis. It did not build the module; the proposed module has not yet been materialized.

Current-source follow-ups from Q8328: Q8337 (task `475e88b3`, prompt `/tmp/q_flt_n25_x_boundary_prelim_current_audit.txt`) checks the overlap-to-local obstruction against the complete current X/W chart files; Q8338 (task `d45ba8c6`, prompt `/tmp/q_flt_n25_xwgerm_ne_zero.txt`) asks for a proof or exact blocker for `xWGerm ≠ 0`; Q8339 (task `e0696012`, prompt `/tmp/q_flt_n25_xchart_w_nonzero.txt`) checks the `[1:1:0:1]` witness for `xW ≠ 0` in the X-chart quotient. All were sent through the automatic FLT allocator without a pinned channel. Q8329 (task `f60f302d`) remains processing on the local-unit module repair; Q8331 (task `71b9c6f9`) remains pending on the projective-degree proof audit; Q8334 (task `2640dff1`) is in artifact grace-poll after terminal completion; Q8335 (task `3e41b06c`) remains pending on the physical-degree compiler mismatch follow-up. No task was resent.

## Latest FLT frontier updates (2026-09-27)

Q8347 (`/tmp/q_flt_n25_three_boundary_point_classification.txt`) returned a field-generic classification of characteristic-three normalized curve points with `w = 0`. The source definitions in `RationalPointsN25QuotientKummerThree.lean` and `RationalPointsN25QuotientKummerThreeProjective.lean` were checked locally. Materialized the proof as `N25F_ThreeBoundaryPointClassification.lean`; Q8350 was dispatched as an independent source/API audit and was still processing at build time.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.N25F_ThreeBoundaryPointClassification
```

Result: `Build completed successfully (8572 jobs)`. Full output: `/tmp/n25_three_boundary_point_classification_build.log`.

Axiom probe: `lake env lean /tmp/n25_three_boundary_point_classification_axioms.lean` printed:

```text
'MazurProof.N25F_ThreeBoundaryPointClassification.boundary_point_eq_three_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Read Q8341 and Q8343 audits for `N25F_ChartLocalUnitCriterion`. Applied the explicit prime argument, made the `FractionRing.algEquiv` call reducible, and corrected the localization witness destructuring to the flat triple. The targeted build still fails at `chartFractionRingEquiv`: Lean selects different `CommSemiring` and `Algebra` instances for the inferred equivalence. Full output: `/tmp/n25_chart_local_unit_build2.log`. Q8351 (`/tmp/q_flt_n25_chart_fraction_equiv_instances.txt`, task `2f6e0ef3`) requests a direct repair for the exact compiler error; Q8352 (`/tmp/q_flt_n25_chart_fraction_equiv_alt_construction.txt`, task `39f40f68`) independently asks for an explicit-instance or localization-equivalence construction. Both were still processing at log time.

Q8344 (`/tmp/q_flt_n25_three_wchart_d_regular.txt`) returned a proposed full-quotient regularity module in `/tmp/gpt/flt/Q8344.md`; it is source-only and has not yet been materialized or built. Q8345 (`/tmp/q_flt_n25_three_wopen_residue_degree.txt`) and Q8348 (`/tmp/q_flt_n25_three_xboundary_artin_equiv.txt`) remain in flight. No answer was treated as a successful build without local verification.
