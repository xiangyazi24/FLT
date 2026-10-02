# Pinned lead receipt

Source: https://github.com/xiangyazi24/FLT/blob/1222d33fa09e5a00d29c6ad294f3dfb32baf26ce/comms/outbox/lead-FLT-N13-ENDPOINT-receipt-r5.md

Resolved full accepted source SHA: 22f88d43187caf0e57affcc6ded92cdf9b49714a.

The following is the lead's receipt, not a dot-run build or emission.

```text
TASK_ID: FLT-N13-ENDPOINT
REVISION: 5
TYPE: RECEIPT + EMITTED CLOSURE
STATUS: INTEGRATED — all 57 N13 modules compiled; C13 axiom discharged
REPO: xiangyazi24/FLT
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 22f88d4318
SUPERSEDES: lead-FLT-N13-ENDPOINT-status-r4.md

Lead-run results:
- lake build of the 27 remaining modules + FLT.Assumptions.MazurProof.TorsionBound: Build completed successfully (9103 jobs).
- #print axioms on all 137 public theorems of those 27 modules: every one [propext, Classical.choice, Quot.sound].
- Headers vs your 5d50b4f20c: 383/384 identical. Diffs: N13KernelBasePic `abbrev basePair : N13TwoAdicAbelChartPic.DiskPair`
  (ascription, same value); new public alias in N13CenteredPrincipalNumerator
  `MazurProof.N13TwoAdicAbelChartData.DiskPair.mumford P := N13TwoAdicAbelChartPic.DiskPair.mumford P` (your statements use P.mumford on
  ChartData.DiskPair, which did not elaborate); new private helper constantCoeff_map_coe; `open ... hiding` lines for ambiguous names.
- 22f88d4318: axiom CyclicExclusion13.C13Sextic_affine_x_is_cuspidal replaced by the theorem
  N13ConstructedRationalPointTheorem.affine_x_is_cuspidal (type identity checked with `example : type_of% @A := @B`).

EMITTED CLOSURE (fresh build, 22f88d4318):
'MazurProof.mazur_torsion_bound' depends on axioms: [propext, Classical.choice, MazurProof.no_prime_order_ge_23, Quot.sound,
 MazurProof.CyclicExclusion25.no_explicit_order25_obstruction, MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction]
No sorryAx. Remaining custom axioms: 3.

NEXT TASK: the custom-axiom boundary map from status r4, now on exactly these 3 axioms. For the nearest one, deliver the
dependency-ordered plan and compilable candidates (exact statements, no weakening), as you did for N13.

```
