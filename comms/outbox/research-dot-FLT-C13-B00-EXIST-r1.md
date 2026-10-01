TASK_ID: FLT-C13-B00-EXIST
REVISION: 1
TYPE: TASK
STATUS: OPEN
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: a6290bc36c3549d89239da82b13b1f59ebd0388e
SCOPE: (1) prove MazurProof.N13CoherentChooserSpecification.GlobalExistenceTarget; (2) the B03 bridge you named
  degreeFourCode_eq_of_comparison (statement as in your comms/inbox/research-dot-FLT-C13-B03-lane.md), then specialization additivity.
ACCEPTANCE: complete proofs as new files under FLT/Assumptions/MazurProof/ (uncompiled is fine; the lead compiles). If a piece is genuinely
  missing, state it as an exact Lean lemma with a math proof sketch, no sorry/axiom stand-ins.
SUPERSEDES: none
NONCE: FLT-DOT-20261001

## Receipt for FLT-C13-B03-PLAN r1 (your 41773751c4)
All 6 candidates compiled on the lead side and are committed on verify-sorry-restore (lake build OK, #print axioms standard only):
N13SpecialCodeRecenter (unchanged), N13SpecialCuspCodeChecks (two norm_num -> decide), N13TwoChartTensorCompatibility (unchanged),
N13CoherentChartComparison (unchanged), N13CoherentDegreeZeroChooser (unchanged), N13CoherentChooserSpecification (unchanged).
Thank you — 5 of 6 compiled with no edit.

## Notes
- Use whatever tools/approach you like; only the proof-integrity rules matter (no statement changes, no sorry/axiom/True, new files only).
- Priority: (1) first. Your B00 notes say Data.infinityOrder is not tied to the generic infinity chart, degree-one nInf=1 needs a
  correction and degree-two marking needs a repair — please do those repairs as concrete new constructions.

## Input manifest (at SOURCE_COMMIT)
```json
{"source_commit": "a6290bc36c3549d89239da82b13b1f59ebd0388e", "files": [
  {"path": "FLT/Assumptions/MazurProof/N13SpecialAbelCodeQuotient.lean", "encoding": "utf-8", "bytes": 4984, "sha256": "89aa5cc8938f8210044d169a43e5eaf363a8aa9f9bcbd2e6847e1fed9a2bd317"},
  {"path": "FLT/Assumptions/MazurProof/N13InverseInfinityWitnessClass.lean", "encoding": "utf-8", "bytes": 6421, "sha256": "3a6f466b30639f60a8d43f8265319ecf8ab2aed131ad2c1d74a38aeb0196f88e"},
  {"path": "FLT/Assumptions/MazurProof/N13TwoChartPicardRealization.lean", "encoding": "utf-8", "bytes": 11991, "sha256": "1c3631df108c3d64669026f0630bc25b6d8e7be52d0857ceb5ab1b1474601b9e"},
  {"path": "FLT/Assumptions/MazurProof/N13TwoChartLineTensor.lean", "encoding": "utf-8", "bytes": 22140, "sha256": "e969baf707a84719a623b04e356461806592a19ff7bdf29958e3071e99bf0f59"}
]}
```
