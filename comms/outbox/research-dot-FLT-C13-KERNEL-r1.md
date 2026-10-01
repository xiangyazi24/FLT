TASK_ID: FLT-C13-KERNEL
REVISION: 1
TYPE: TASK
STATUS: OPEN
REPO: xiangyazi24/FLT
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5
SCOPE: Answer to research-dot-FLT-C13-kernel-scope-query: neither kernel lane is owned by any active worker (the Qwen lane is
  only compiling your C13 candidates from 2561ea7c66; Codex is out). Both are assigned to dot:
  (K1) MappedSpecialFamily and (K2) FirstJetDoublingCompatibility for N13RationalKernelDoublingAdapter
  (FLT/Assumptions/MazurProof/N13RationalKernelDoublingAdapter.lean). Use your reading: basePair (x=0, good y=0), (x=-1, good y=0),
  literal special divisor C+B / code8 (not the inverse-infinity C+A / code13 datum), translation AJ13 C + AJ13 B with the raw mark -2
  → balanced mark -1 shift made explicit. Build on 2561ea7c66 (B00/B03 candidates) where useful; the lead compiles them now and
  will report errors back.
ACCEPTANCE: source design + uncompiled Lean candidates in new modules (no edits to existing lead files), no sorry/axiom in what you
  claim complete, statements of existing declarations unchanged. The lead compiles, runs #print axioms, integrates.
WRITE_SCOPE: research-dot/flt-collaboration-20261001
OUTPUT: comms/inbox/research-dot-FLT-C13-KERNEL-r1.md (+ candidate modules on your branch)
SUPERSEDES: none

## Input manifest (at SOURCE_COMMIT)
```json
{"source_commit": "887d29cd9eb9b60a6e5ec438ff919a74ccda41e5", "files": [
  {"path": "FLT/Assumptions/MazurProof/N13RationalKernelDoublingAdapter.lean", "encoding": "utf-8", "bytes": 18568, "sha256": "c7b957e195e1aff5503ccc64222b1853799418570c004d591737f9865a38ad0e"},
  {"path": "FLT/Assumptions/MazurProof/N13MumfordFormalTransitionJet.lean", "encoding": "utf-8", "bytes": 16616, "sha256": "c2efa95e21d11b91eb43e8567350e1bb6234f1538ca68e1087e16c6cea4e98f7"},
  {"path": "FLT/Assumptions/MazurProof/N13ConcreteGraphRecovery.lean", "encoding": "utf-8", "bytes": 23645, "sha256": "9968e2edf8a05dea1f493b397b88c3895be553e092c079133190477beb7484ad"},
  {"path": "FLT/Assumptions/MazurProof/N13SpreadRationalPointReduction.lean", "encoding": "utf-8", "bytes": 2485, "sha256": "b0dad650f1dacf71564fbe9c16848d2839351894851f40932d1bab21e217c19c"},
  {"path": "FLT/Assumptions/MazurProof/N13TwoAdicAbelChartSection.lean", "encoding": "utf-8", "bytes": 6653, "sha256": "bca21651e3f45500b2b1a96d39c6167f02222a2b30b0e206f45b451304016b40"}
]}
```
