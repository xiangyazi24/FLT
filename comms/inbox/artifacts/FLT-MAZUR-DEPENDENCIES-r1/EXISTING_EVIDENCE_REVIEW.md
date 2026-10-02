# Existing Mazur endpoint evidence review

Source-only review on 2026-10-02. Repository source pin: `4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3`. Dispatch reviewed: `c086d9370149c1030c750956d5ee0c408f5b1937`.

## Result

No committed current declaration-level emitted proof-dependency closure was located. The best located actual complete endpoint axiom output is dated 2026-08-20. A later September 27 run-log paragraph reports the same four custom axioms without a raw endpoint output block or traversal. Neither establishes the requested current list of sorryAx-containing reachable declarations at the source pin.

Lean, lake, project compilation, cache work, and local emission: **NOT RUN**. No remote writes. The recursive source tree was retrieved in full (1,465 entries, truncated=false); relevant audit sources, logs, ledgers, status notes, dispatch notes, and recent commit messages were inspected read-only. This is not a claim that every source file or every historical commit was exhaustively searched.

## Authoritative targets

- Full endpoint: `MazurProof.mazur_torsion_bound`, with conclusion `(torsionSet E).Finite ∧ (torsionSet E).ncard ≤ 16`.
- Numerical projection: `MazurProof.mazur_torsion_bound_ncard`.
- `MazurEndpointAudit.lean` imports TorsionBound and executes `#print axioms MazurProof.mazur_torsion_bound`.
- Do not substitute the older assumption `Mazur_statement` in `FLT/Assumptions/Mazur.lean`, nor the merely intermediate `mazur_cyclic_order_bound_assembled`.

Sources:
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/TorsionBound.lean
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/MazurEndpointAudit.lean
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/MAZUR_CHECKLIST.md#L3-L8

## Emitted evidence and limitations

The August 20 committed audit records:
- commands: `lake build FLT.Assumptions.MazurProof.MazurEndpointAudit`, then `lake env lean FLT/Assumptions/MazurProof/MazurEndpointAudit.lean`
- host uisai2, build success with 8,775 jobs
- actual displayed output for `MazurProof.mazur_torsion_bound`: `propext`, `Classical.choice`, `MazurProof.no_prime_order_ge_23`, `Quot.sound`, `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`, `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`, `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
- interpretation in the report: four custom axioms, no reachable sorryAx

This is a historical complete axiom-set output, not a current declaration-level traversal. A fresh `#print axioms` also only identifies terminal axiom dependencies; if sorryAx occurs, it does not by itself identify every enclosing reachable declaration containing or inheriting it.

Source:
https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/research-map/audits/2026-08-20-mazur-endpoint.txt

The September 27 run log, line 59, says the audit still reports the same four custom axioms. It is a later recorded observation but not the raw full endpoint output or the requested declaration closure:
https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/RUN_LOG_flt_codex.md#L40-L59

## Freshness of source-status documents

Path-filtered commit history at the source pin gives:
- audit text and claims.jsonl last modified by 69ef7a5341a648087fcc6b1bcb523d5205716381, 2026-08-21
- RESEARCH_MAP.md last modified by 248192e084c55d2ef651b5bba02306091a03a757, 2026-08-21
- MAZUR_CHECKLIST.md last modified by a1de864e23fd3809eadcda9437edefc5547e1df5, 2026-08-23
- FLT_MAZUR_STATUS.md last modified by 06a06ced236e93e70063df98a4f00d28320b8398, 2026-08-19

The map and machine ledger disagree in places: claims.jsonl still calls the N25 ambient/Čech comparison open, whereas RESEARCH_MAP.md calls it proved and moves to canonical/Picard work. September logs show further N25 progress. Neither should be treated as a current smallest-open-item oracle.

## Non-N13 open-gap shortlist, with provenance

The three non-N13 endpoint custom axioms named by historical output are still literal axiom declarations in current pinned source:
1. `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`
2. `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
3. `MazurProof.no_prime_order_ge_23`

This source observation does not replace an emitted current closure.

Sources:
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/CyclicExclusion25.lean
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/CyclicExclusion49.lean
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/CyclicOrderAssembly.lean

Historical small-gap candidate: `composition_identity_sorry` in RationalPointsN49Composition.lean, recorded by MZ-N49-COMPOSE as one literal placeholder. The map explicitly says it is only a reformulation and does not close N49; no current emitted endpoint membership is established for it.

The separate current source-only scan reports 407 non-N13-prefixed MazurProof Lean files (excluding CyclicExclusion13), fetched and hash-verified. It located only three literal sorry admissions in that scan scope: `KubertBridgeN16.kubert_C16_discriminant_data` (line 342), `KubertBridgeN16.EN16_point_of_Phi16_and_disc` (line 361), and `RationalPointsN49Composition.composition_identity_sorry` (line 96). It found no imports/text references to N49Composition in those files and reports that the current order-16 route does not consume the Kubert placeholder proofs. These are source-level observations, not a kernel traversal. **None of these declarations may be called the smallest emitted-reachable sorry gap until the lead supplies actual emitted dependency evidence at the pin.** An honest selection may be “no reachable sorry item established”; do not force one of the three into the endpoint closure.

The N25 historical frontier is actual Picard/Riemann–Roch/product-formula/geometric reduction/rank-zero/pullback-norm work. The uniform prime tail is a long-range formal-immersion/Eisenstein-ideal task, not a small tactic hole.

Sources:
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/RESEARCH_MAP.md
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/research-map/claims.jsonl
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/MAZUR_CHECKLIST.md#L231-L265

Important historical route conflict: the map still proposes closing all N49 Newton charts; N49_NEWTON_ANALYSIS.md's appended Q5293 report says seven binomial faces lift to genuine Q₂ points and a global input is needed. This is a reported mathematical finding, not kernel evidence. Do not select the stale local-closure plan as a proven available route.
https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/N49_NEWTON_ANALYSIS.md

## Ownership and latest verified status

- Lead is Opus coordinator acting for Xiang Huang; lead retains verification/integration authority.
- Latest dispatch requests independent non-N13 source work while lead compiles N13. It does not provide a current N25/N49 owner roster.
- October 1 N18 task explicitly says no lane owns N18 and assigns it to dot; October 2 receipt marks add_congr done, compiled unchanged, clean-three for AddCongr.add_congr and add_congr_wired at the exact source pin.
- FLT_MAZUR_STATUS.md's N25 “Don't touch” ownership warning is historical (last changed August 19), not a current assignment. It is a reason to coordinate before intruding into N25, not proof of a current lane.
- September 28 RUN_LOG_flt_codex.md records takeover from Codex for N25 work; September 30 entries shift to N13. No fresh N25/N49 ownership fact was found.

Sources:
- https://github.com/xiangyazi24/FLT/blob/c086d9370149c1030c750956d5ee0c408f5b1937/comms/outbox/research-dot-FLT-DOT-20261001-ack.md
- https://github.com/xiangyazi24/FLT/blob/c086d9370149c1030c750956d5ee0c408f5b1937/comms/outbox/lead-FLT-N13-ENDPOINT-r1.md
- https://github.com/xiangyazi24/FLT/blob/c086d9370149c1030c750956d5ee0c408f5b1937/comms/outbox/research-dot-FLT-N18-ADDCONGR-r2.md
- https://github.com/xiangyazi24/FLT/blob/c086d9370149c1030c750956d5ee0c408f5b1937/comms/outbox/research-dot-FLT-N18-ADDCONGR-receipt.md
- https://github.com/xiangyazi24/FLT/commit/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT_MAZUR_STATUS.md
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/RUN_LOG_flt_codex.md#L406-L428

## False-positive warnings

The 29e80dbc17c5fdf3a194618d65dc0676199e19f5 commit message says grep finds the word sorry in N18ReductionHom (2) and TateOrder16Cyclic (1). Those occurrences are comments, not proof admissions in the pinned files. N18ReductionHom packages its two missing geometric inputs as explicit hypotheses; it does not silently prove those constructions. The old DOCTRINE mention of N18GoodModelZParam.lean does not resolve to a file at this pin. KubertBridgeN16 has actual source placeholders, but their current emitted endpoint membership has not been established by this review.

Sources:
- https://github.com/xiangyazi24/FLT/commit/29e80dbc17c5fdf3a194618d65dc0676199e19f5
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/N18ReductionHom.lean#L13-L36
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/TateOrder16Cyclic.lean#L45-L57


## Conditional smaller cleanup candidate: the two Kubert placeholders

Independent source-only signature check at the pin found no mismatch in the proposed cleanup. This is preferable to the N49 composition identity as a small *source-cleanup* candidate, but it is not established as an emitted-reachable endpoint gap. Implementation remains held pending actual emitted root membership or an explicit separate cleanup assignment.

1. `KubertBridgeN16.EN16_point_of_Phi16_and_disc`: `RationalPointsX116.no_X116Datum` has type `¬ ∃ b c : ℚ, TateOrder16Cyclic.X116Datum b c`. The definition of `X116Datum` is exactly `b ≠ 0 ∧ c ≠ 0 ∧ KubertBridgeN16.tateM16 b c ≠ 0 ∧ KubertBridgeN16.Phi16 b c = 0`. Thus the existing arguments `hb, hc, hM, hPhi` provide `⟨b, c, hb, hc, hM, hPhi⟩`, yielding False; False.elim gives the unchanged existential conclusion. `eta` and `hDisc` are unnecessary for this contradiction, but remain in the original statement. This proves a vacuous implication; it does not construct the historically proposed geometric map.

2. `KubertBridgeN16.kubert_C16_discriminant_data`: destruct the supplied injection as `⟨f, hf⟩`, obtain `⟨P, hP⟩` from the already proved `KubertBridgeN16.point_addOrder16_of_zmod2_zmod16_injection E f hf`, and contradict `MazurProof.no_rational_point_of_order_16 E ⟨P, hP⟩`. Again False.elim yields the unchanged existential conclusion. The existing `DescentBridgeN16.no_Z2_cross_Z16_from_descent` already uses precisely this contradiction at lines 18–20.

An in-place added import is circular: `RationalPointsX116` imports `TateOrder16Cyclic`, which imports `KubertBridgeN16`; `CyclicExclusion16` imports `RationalPointsX116`. Before implementation, split the shared definitions and existing proved algebra/group-extraction core into a lower module, preserving fully qualified declaration names. Retarget `TateOrder16Cyclic` to that core; retain the two unchanged theorem statements and their callers in the upper Kubert wrapper, which can then import `CyclicExclusion16`. Audit the complete import graph before acceptance. No such code change was made here, and no elaboration/build/axiom check was run.

Verified source links:
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/KubertBridgeN16.lean#L336-L361
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/KubertBridgeN16.lean#L241-L249
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/TateOrder16Cyclic.lean#L224-L227
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/RationalPointsX116.lean#L588-L599
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/CyclicExclusion16.lean#L94-L111
- https://github.com/xiangyazi24/FLT/blob/4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3/FLT/Assumptions/MazurProof/DescentBridgeN16.lean#L15-L20
