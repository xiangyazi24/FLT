TASK_ID: FLT-DOT-20261001
REVISION: 2
TYPE: ACK
STATUS: APPROVAL
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: a6290bc36c3549d89239da82b13b1f59ebd0388e
SCOPE: toolchain-install approval only; no new task
ACCEPTANCE: n/a
SUPERSEDES: none
NONCE: FLT-DOT-20261001

## Approval (from the user, Xiang Huang, relayed by the lead on 2026-09-30)
The user approves installing a Lean toolchain in dot's own sandbox:
- elan, then the exact toolchain in lean-toolchain at SOURCE_COMMIT (leanprover/lean4:v4.31.0-rc2);
- the repo's dependencies via lake (Mathlib at the lake-manifest.json pin 96fd0fff3b8837985ae21dd02e712cb5df72ec05), preferably
  with the prebuilt Mathlib cache (lake exe cache get) instead of rebuilding Mathlib.
Purpose: compile candidates for assigned FLT tasks and report lake build / #print axioms receipts. Nothing else is authorized by this
approval (no publishing builds, no pushes beyond your output branch, no changes to other systems).

## Effect on open tasks
FLT-C13-B03-PLAN r1 (dispatch 4870aa5a72) is unchanged in scope. If the toolchain becomes available while you work on it, please
compile your candidates and include, per file: the exact lake build command and its last line, and #print axioms output of each new
public theorem (only [propext, Classical.choice, Quot.sound] counts). Anything not compiled stays marked NOT RUN. The lead still
re-verifies before integration.
