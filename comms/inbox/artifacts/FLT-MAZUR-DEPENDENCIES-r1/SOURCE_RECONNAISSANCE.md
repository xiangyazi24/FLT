# Full Mazur next-gap reconnaissance: source-only, emitted closure pending

Source pin: `4c6a8b6feb2a4e487ed51c64852bd1ae98416ee3`  
Dispatch: `c086d9370149c1030c750956d5ee0c408f5b1937`  
Updated: October 1, 2026, 9:11 p.m. America/Chicago

## Result

The actual current declaration-level `sorryAx` proof-dependency closure has **not been emitted by dot** and has not yet been supplied by the lead. User instructions reserve project builds, cache operations, and kernel/emission checks to the lead. The ACK at `14f6915573ff62b78c50aae4ac1b05111a84d4c2` requests the actual output and its source/olean provenance.

Therefore this report does **not** claim an emitted closure, a clean endpoint, or a smallest confirmed reachable admission. It records current source evidence and a conditional exact-statement cleanup plan, so work can proceed promptly after the runtime evidence arrives.

## Authoritative endpoint and available emitted evidence

`MazurProof.mazur_torsion_bound` in `TorsionBound.lean` proves rational torsion finiteness together with the cardinality bound. `MazurEndpointAudit.lean` prints that declaration's axioms. The numerical wrapper is `MazurProof.mazur_torsion_bound_ncard`.

The best complete emitted output found is the committed `research-map/audits/2026-08-20-mazur-endpoint.txt`. It reports four custom axioms and no `sorryAx`. A September 27 run-log paragraph summarizes the same four-axiom status; neither supplies a fresh declaration-level traversal at the current pin. Historical output is not relabeled as a current emission. See `EXISTING_EVIDENCE_REVIEW.md` for exact links, commit dates, and source/ownership limitations.

## Bounded current source inventory

All **407** `.lean` files in `FLT/Assumptions/MazurProof/` whose filenames do not start with `N13`, excluding `CyclicExclusion13.lean`, were read through the GitHub connector at the exact source pin. Each returned Git blob matched the pinned recursive tree; there were no failed reads.

This filename-based scope is an inventory, **not** an actual proof closure or even a complete non-N13 dependency partition. Generic helper files used by N13 may also be present. It does not cover all Lean files elsewhere in the repository or Mathlib. Nested comments and ordinary string literals were removed before matching the exact code tokens `axiom`, `sorry`, `admit`, and `sorryAx`.

The three literal `sorry` sites are:

| Declaration | File/line | Current source evidence |
| --- | --- | --- |
| `MazurProof.KubertBridgeN16.kubert_C16_discriminant_data` | `KubertBridgeN16.lean:342` | Old noncyclic bridge; current source contains a direct placeholder |
| `MazurProof.KubertBridgeN16.EN16_point_of_Phi16_and_disc` | `KubertBridgeN16.lean:361` | Old geometric bridge; current source contains a direct placeholder |
| `MazurProof.RationalPointsN49Composition.composition_identity_sorry` | `RationalPointsN49Composition.lean:96` | Composition shortcut helper; no textual references/importers were found elsewhere in the scanned files |

The lexical source scan also finds five custom-axiom declarations:

- `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`, `CyclicExclusion25.lean:47`
- `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`, `CyclicExclusion49.lean:43`
- `MazurProof.no_prime_order_ge_23`, `CyclicOrderAssembly.lean:102`
- `MazurProof.mazur_prime_torsion_bound`, `CyclicOrderReduction.lean:31`
- `MazurProof.mordell_weil_fg`, `TorsionFinite.lean:14`

The first three have direct uses in the active cyclic assembly's displayed source. The latter two are historical alternatives in source; import presence does not establish their inclusion in the final proof term. These are custom axioms, not necessarily `sorryAx` declarations, and the task must not silently conflate the two classes.

The accepted N18 files contain none of the scanned admission tokens. `N18ReductionHom` and `TateOrder16Cyclic` raw word matches are comments. All of these statements are source-level only.

## Smallest conditional source-cleanup candidate

The N49 composition helper is syntactically compact but not the best justified next endpoint task: current scanned source has no incoming references to it, and an exact division-polynomial composition proof is a real separate mathematical task. Historical map labels do not establish current endpoint relevance or ownership.

A smaller proof obligation is the old `KubertBridgeN16.EN16_point_of_Phi16_and_disc` statement. Its existing hypotheses already contain precisely a `TateOrder16Cyclic.X116Datum`:

`hb : b ≠ 0`, `hc : c ≠ 0`, `hM : tateM16 b c ≠ 0`, `hPhi : Phi16 b c = 0`.

Current `RationalPointsX116.no_X116Datum` proves that such data cannot exist. After arranging acyclic imports, the unchanged target proposition has the source candidate proof:

```lean
  exact (MazurProof.RationalPointsX116.no_X116Datum
    ⟨b, c, hb, hc, hM, hPhi⟩).elim
```

The extra `hDisc` premise remains in the original statement even though this proof does not use it; no hypothesis or conclusion is changed.

The other old Kubert admission also has a short source plan. The existing proved injection-to-order16 theorem gives a rational point of order 16, contradicting the existing `MazurProof.no_rational_point_of_order_16`:

```lean
  rcases hE with ⟨f, hf⟩
  obtain ⟨P, hP⟩ := point_addOrder16_of_zmod2_zmod16_injection E f hf
  exact (MazurProof.no_rational_point_of_order_16 E ⟨P, hP⟩).elim
```

**Import-cycle gate:** direct imports of the exclusions into the current unsplit `KubertBridgeN16` would create a cycle, because `TateOrder16Cyclic` imports that module for its `tateM16`/`Phi16` definitions. A candidate implementation must first move the unchanged definitions and already-proved elementary core below the cyclic route; `TateOrder16Cyclic` would import that core, and the final legacy Kubert file could then import the proved exclusions and close the two exact statements. This is a plan only, not an implemented or compiled refactor.

The active cyclic route's visible calls use the Kubert polynomial definitions, not the two admitted bridge theorems. `DescentBridgeN16` already follows the proved order-16 contradiction route. Therefore these admissions may be cleanup-only and are **not selected as reachable endpoint gaps** without actual emitted evidence. No current separate owner was identified from the dispatches inspected; that is not proof of exclusive lane ownership.

## Next action and stopping gate

1. Await the lead's actual current `#print axioms` and declaration-level proof traversal, with emitter command/version and source/olean freshness evidence.
2. Identify which non-N13 declaration, if any, actually contributes `sorryAx` to the authoritative endpoint. Preserve the exact fully qualified target and statement.
3. If the Kubert declarations are included and unowned, the exact-statement split/closure above is ready for source implementation and lead compilation. If they are absent, do not present their cleanup as endpoint progress.
4. If no non-N13 `sorryAx` contributor remains, report that actual result and distinguish the still-open custom-axiom boundaries. Ask the lead which independent arithmetic lane is intended rather than inventing a reachable admission or touching historically contested N25 work.

No Lean/project/build/cache operation, endpoint emission, candidate source mutation, main-branch update, PR, release, or deployment is performed by this reconnaissance.
