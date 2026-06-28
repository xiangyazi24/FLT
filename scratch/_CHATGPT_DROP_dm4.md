# Q2095 (dm4): ai-scratch remote state before pushing local commits

Date: 2026-06-28.

Repository: `xiangyazi24/FLT`.

Requested question: before pushing the local `ai-scratch` branch with roughly 20 new local commits today, verify:

1. whether the full build passes on `uisai2`;
2. whether there are uncommitted local changes;
3. the current `sorry` count;
4. what the remote currently has versus what the local checkout likely has.

## Executive answer

I can read the GitHub remote through the connector, but I **cannot** read the `uisai2` local worktree or run `lake build` there from this connector session.

So the hard local facts are:

```text
full build on uisai2:       NOT verified by this connector session
local uncommitted changes:  NOT visible from GitHub remote
local sorry count:          NOT directly measurable without local grep/build access
```

What I **can** verify from GitHub:

```text
remote repository:          xiangyazi24/FLT
remote ai-scratch exists:   yes
remote ai-scratch HEAD:     848ffbf5163603f16828def879890e51e5cc3725
remote HEAD commit message: Fix API errors in num_abs_le_one Lean drop
remote combined statuses:   none reported
remote workflow runs:       none reported for this commit
```

The remote `ai-scratch` branch therefore does **not** provide evidence of a passing build. It has no status checks or workflow runs attached to the visible remote head.

Most importantly: if your local branch really has approximately 20 new commits from today, then those commits are probably **not** on remote `ai-scratch` yet. The remote head visible through GitHub is still:

```text
848ffbf5163603f16828def879890e51e5cc3725
```

That head is the commit your local push should advance from, unless your local `origin/ai-scratch` is stale or you already pushed from another machine.

## Remote branch comparison

Connector comparison result:

```text
base: main
head: ai-scratch
status: diverged
ahead_by: 115
behind_by: 30
main/base commit: e0fc4b3ab63b56994a3326298ecabf28f5ab8a97
merge base:       c541ddcef7c95308113bed83c0c9460926bcb706
```

So remote `ai-scratch` is not a small fresh branch relative to `main`: it is already a long-lived divergent scratch branch, 115 commits ahead of `main` and 30 commits behind `main`.

Connector comparison against the `scratch` branch:

```text
base: scratch
head: ai-scratch
status: diverged
ahead_by: 115
behind_by: 439
scratch/base commit: 62e615497810b1d6f38f6a1ff812161cdac32ac6
merge base:          c541ddcef7c95308113bed83c0c9460926bcb706
```

So `scratch` and `ai-scratch` are both divergent descendants of the same old merge base. Do **not** infer from `scratch` that `ai-scratch` contains the latest handoff notes or local Lean work.

## Files remote `ai-scratch` adds relative to `main`

The remote branch currently adds the Mazur scaffold under:

```text
FLT/Assumptions/MazurProof.lean
FLT/Assumptions/MazurProof/Axioms.lean
FLT/Assumptions/MazurProof/CyclotomicLayer.lean
FLT/Assumptions/MazurProof/DOCTRINE.md
FLT/Assumptions/MazurProof/DescentBridge.lean
FLT/Assumptions/MazurProof/DescentBridgeN12.lean
FLT/Assumptions/MazurProof/DescentBridgeN14.lean
FLT/Assumptions/MazurProof/DescentBridgeN16.lean
FLT/Assumptions/MazurProof/DescentObstruction.lean
FLT/Assumptions/MazurProof/GroupTheory.lean
FLT/Assumptions/MazurProof/NoncyclicN10.lean
FLT/Assumptions/MazurProof/ObstructionCurve.lean
FLT/Assumptions/MazurProof/RootsOfUnity.lean
FLT/Assumptions/MazurProof/TorsionBound.lean
FLT/Assumptions/MazurProof/TorsionFinite.lean
FLT/Assumptions/MazurProof/UNDERSTANDING.md
```

It also adds many exploratory scratch files, including:

```text
scratch/CoprimeFactorSplit.lean
scratch/CoverPrimeDivisor.lean
scratch/DESIGN_NOTES.md
scratch/DenominatorQuartic.lean
scratch/Descent20a4.lean
scratch/DescentAssembly.lean
scratch/DescentMap.lean
scratch/DescentN14.lean
scratch/DescentN16.lean
scratch/E20GoodReduction.lean
scratch/E20_FiniteFieldCounts.lean
scratch/E20_TorsionOrder.lean
scratch/GitHubConnectorTest.lean
scratch/Isogeny20a4.lean
scratch/MazurSkeleton.lean
scratch/MazurTest.lean
scratch/ObstructionCurveTry.lean
scratch/ObstructionN10Complete.lean
scratch/PythagoreanDescentCore.lean
scratch/ROADMAP.md
scratch/RootsOfUnityQ.lean
scratch/Selmer20a4.lean
scratch/SelmerD2.lean
scratch/TorsionBoundV2.lean
scratch/TorsionSMul.lean
scratch/TorsionStructureExplore.lean
scratch/X1_13_PointCount.lean
scratch/X1_17_PointCount.lean
scratch/ZPhiDescentOddFinal.lean
scratch/ZPhiDescentStep.lean
scratch/_CHATGPT_DROP.lean
scratch/_CHATGPT_DROP_dm1.lean
scratch/_CHATGPT_DROP_dm1.md
scratch/_CHATGPT_DROP_dm2.lean
scratch/_CHATGPT_DROP_dm2.md
scratch/check_order10.py
scratch/order10_obstruction.py
```

## What remote `ai-scratch` contains in the Mazur scaffold

The current remote scaffold has the top-level import file:

```lean
import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.CyclotomicLayer
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.Axioms
import FLT.Assumptions.MazurProof.TorsionFinite
import FLT.Assumptions.MazurProof.TorsionBound
import FLT.Assumptions.MazurProof.DescentObstruction
import FLT.Assumptions.MazurProof.DescentBridge
import FLT.Assumptions.MazurProof.NoncyclicN10
```

Important remote facts from inspected files:

* `TorsionBound.lean` proves `full_rational_torsion_order_le_two` from `weil_pairing_primitive_root` plus the rational roots-of-unity lemma.
* `TorsionBound.lean` proves `mazur_torsion_bound` from the axiom seams and the finite case split.
* `Axioms.lean` defines `HasFullRationalTorsion`, `HasRationalPointOfOrder`, `HasTorsionStructure`, `TorsionStructureData`, and the main named axiom seams.
* `DescentObstruction.lean` contains `native_decide` local obstruction checks for the `20.a4` descent computations.
* `DescentBridge*.lean` files keep the noncyclic exclusions behind narrow bridge axioms.

## Remote axiom seams visible in `FLT/Assumptions/MazurProof/`

From the remote files I inspected, the visible MazurProof axiom declarations are:

```text
Axioms.lean:
1. rational_torsion_two_invariant_factors
2. weil_pairing_primitive_root
3. no_rational_point_of_order_ge_17

TorsionFinite.lean:
4. mordell_weil_fg

DescentBridge.lean:
5. obstruction_curve_20a4_points_degenerate
6. Z2xZ10_gives_non_degenerate_E20_point

DescentBridgeN12.lean:
7. obstruction_curve_N12_points_degenerate
8. Z2xZ12_gives_non_degenerate_N12_point

DescentBridgeN14.lean:
9. obstruction_curve_N14_points_degenerate
10. Z2xZ14_gives_non_degenerate_N14_point

DescentBridgeN16.lean:
11. obstruction_curve_N16_points_degenerate
12. Z2xZ16_gives_non_degenerate_N16_point

ObstructionCurve.lean:
13. E20_rational_points_complete
```

So the remote inspected Mazur scaffold has **13 visible axiom declarations** in the MazurProof files.

This is an axiom count over the inspected `FLT/Assumptions/MazurProof/` files, not a full `#print axioms` transitive dependency audit.

## Remote `sorry` count

I cannot run a full recursive local grep from GitHub connector state. From the remote MazurProof files inspected through the connector, I did not see any literal `sorry` occurrences. The visible proofs use `native_decide`, `norm_num`, `omega`, explicit axiom declarations, and ordinary theorem proofs.

Therefore the best connector-grounded statement is:

```text
remote ai-scratch MazurProof visible literal sorry count: likely 0
remote ai-scratch full-repo sorry count: not verified by connector
local uisai2 sorry count: not visible from connector
```

For the actual pre-push check on `uisai2`, run the commands in the next section and use the local result as authoritative.

## Exact local pre-push checklist for `uisai2`

Run this on `uisai2` in the FLT checkout:

```bash
git switch ai-scratch
git fetch origin

printf '\n=== branch/head ===\n'
git status --short --branch
git rev-parse HEAD
git rev-parse origin/ai-scratch || true

printf '\n=== local commits not on remote ===\n'
git log --oneline --decorate origin/ai-scratch..HEAD

printf '\n=== remote commits not in local ===\n'
git log --oneline --decorate HEAD..origin/ai-scratch

printf '\n=== uncommitted changes ===\n'
git status --porcelain=v1

printf '\n=== sorry count: MazurProof ===\n'
grep -RIn --include='*.lean' '\bsorry\b' FLT/Assumptions/MazurProof scratch | tee /tmp/flt_sorry_hits.txt
wc -l /tmp/flt_sorry_hits.txt

printf '\n=== axiom declarations: MazurProof ===\n'
grep -RIn --include='*.lean' '^axiom ' FLT/Assumptions/MazurProof | tee /tmp/flt_axiom_hits.txt
wc -l /tmp/flt_axiom_hits.txt

printf '\n=== full build ===\n'
lake build
```

If you want a stricter sorry scan that excludes comments only approximately, use:

```bash
grep -RIn --include='*.lean' '\bsorry\b' FLT/Assumptions/MazurProof scratch \
  | grep -v '^[^:]*:[0-9]*:[[:space:]]*--'
```

If `lake build` succeeds and `git status --porcelain=v1` is empty, then push:

```bash
git push origin ai-scratch
```

If the branch has no upstream configured:

```bash
git push -u origin ai-scratch
```

## What local likely has versus remote

Given your statement that local `ai-scratch` has roughly 20 new commits today, and given that the visible remote `ai-scratch` head is still:

```text
848ffbf5163603f16828def879890e51e5cc3725
```

the likely situation is:

```text
origin/ai-scratch: old remote head at 848ffbf5163603f16828def879890e51e5cc3725
local ai-scratch:  ahead by ~20 commits, containing today's Mazur/Weil-pairing work
```

But this is an inference from your local description plus remote state. The connector cannot prove it without access to your local `.git` directory.

The local command that will settle this exactly is:

```bash
git log --oneline --decorate origin/ai-scratch..HEAD
```

If it prints the ~20 commits, those are exactly what will be pushed.

## Recommended push gate

Do **not** push until these three local checks pass:

```text
1. lake build                       succeeds
2. git status --porcelain=v1        prints nothing
3. git log origin/ai-scratch..HEAD  shows the intended local commits only
```

Then push:

```bash
git push origin ai-scratch
```

After pushing, verify:

```bash
git fetch origin
git rev-parse HEAD
git rev-parse origin/ai-scratch
git log --oneline --decorate -1 origin/ai-scratch
```

The two SHA outputs should match your local HEAD.
