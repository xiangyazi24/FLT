# FLT-C13-B00-EXIST r2 — source candidate delivery

TASK_ID: FLT-C13-B00-EXIST
REVISION: 2
TYPE: RESULT
STATUS: SOURCE-REVIEWED / KERNEL-NOT-RUN / BRANCH-DELIVERY-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5
DISPATCH_COMMIT: 44b6fa4c9bbb43e65d0c136ab8e57bbfa8392402
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
NONCE: FLT-DOT-20261001
SUPERSEDES: none (result for the existing r2 assignment; r2 dispatch superseded r1)

## Useful results

41 new Lean modules, 6,565 lines, supply complete source candidates for:

- `N13CalibratedChooser.globalExistenceTarget`, the exact unchanged original chooser target, including all three prescribed data values, named rational-point comparisons, and integral tensor comparisons
- `N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison`, the exact requested degree-four special principal-comparison/code implication
- `N13ConstructedSpecialization.specialization : G →+ ZMod 19`, with recentered additivity and compatibility with actual proper reduction of every rational curve point
- `N13ConstructedReductionClassifier.classifier`, `compatibleReduction`, and surjectivity of the constructed code map onto ZMod19

There are no added comparison/additivity hypotheses, new axioms, sorry/admit, native_decide, or weakened targets. This does NOT assert kernel acceptance or full C13/FLT completion.

## Verification boundary

- Dispatch's ten manifest inputs: byte/hash verification PASS
- Additional materialized source blobs: exact pinned Git-blob verification PASS; inventory attached
- Independent mathematical/source/API audits of all candidate stages: no concrete unresolved defect found
- Final chooser elaboration delta: explicit `by classical; exact` before unchanged branches; separately audited
- Lean elaboration, project compilation, ordinary `decide` evaluation, and endpoint axiom checks: NOT RUN
- Integration and final acceptance: lead-owned, NOT CLAIMED
- Own-branch commit/push authorized; commit and remote readback are recorded separately after delivery

Toolchain at source: leanprover/lean4:v4.31.0-rc2
Mathlib pin: 96fd0fff3b8837985ae21dd02e712cb5df72ec05

The older six candidates already compiled by the lead are not redone or modified. New files are installed at their listed FLT/Assumptions/MazurProof paths. No existing source or main/integration branch was edited.

## Dependency and proof notes

[Global construction report](research-dot-FLT-C13-B00-EXIST-r2-global-candidate.md) describes the effective-chamber repair, same-witness actual marking, primitive two-chart fractions, faithful branch maps, finite-jet lifting, integral descent, and calibrated chooser.

[B03 construction report](research-dot-FLT-C13-B03-source-completion.md) explains how an arbitrary SpecialComparison is reduced to the true 127 nonzero polynomial candidates, how actual Hensel jets are linked to all six local orders, and how the finite ordinary-decide certificate proves the original code implication.

The balanced `classOf_injective` dependency used only for separating the three calibrations was audited through a 32-file project import closure. It is distinct from the previously flagged `n13_class_eq_iff` raw/special coherence route. Generic existence uses classOf_surjective directly, not normalizedMumford uniqueness. No new proof uses exactSpreadLine or the bad-characteristic sextic specialization shortcut.

The current chooser SHA-256 is 514c47dedbefede319d8fd87d536d68d50b14790f053c3a34314629231c446c7. The historical source-reviewed snapshot 974d3e964af5cae116d7f6155969762fc4267a6f9607239f2ece841a0e1e503d is preserved; the only delta supplies local classical decidability in the piecewise choice.

## Lead next steps

Use the candidate manifest and dependency order, compile the new modules, and run `comms/checks/N13C13CandidateAudit.lean` to inspect exact endpoint types and their axioms. The isolated finite ordinary-decide statements may need tactic/resource tuning; no execution-performance claim is made. Any repair must preserve their statements and the original endpoints.

The remaining downstream geometric obligation is separatedness of the ACTUAL constructed kernel. A read-only check found the existing near-base adapter uses C+B (good ordinates0,0 at x=0,−1), special code8, not C+A/code13. No kernel-recovery implementation ownership is claimed here.
