# N25 actual Z-chart injectivity and common function field

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: TWO-CANDIDATES; BOUNDED-SOURCE-CHECKS-PASS; FULL-IMPORTS-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; genuine boundary field producers preserving accepted r9 work

## Completed exact production statements

`N25F_ZChartFractionInjective.lean` proves qz has no positive power equal to
one and that the actual coordinate-rigid Z-chart map is injective.
`N25F_ZChartFractionEquiv.lean` proves the field lift is bijective and supplies:

```lean
zChartFractionAlgEquiv : FractionRing ZChartRing ≃ₐ[ZMod 2] FractionRing W

zChartToFraction_isFractionRing :
  letI : Algebra ZChartRing (FractionRing W) :=
    zChartToFraction.toRingHom.toAlgebra
  IsFractionRing ZChartRing (FractionRing W)
```

The respective namespaces are MazurProof.N25F_ZChartFractionInjective and
MazurProof.N25F_ZChartFractionEquiv. The equivalence restricts exactly to the
existing coordinate-rigid zChartToFraction. No abstract embedding, assumed
surjectivity, competing global scalar action, or product formula is used.
The faithful polynomial algebra proves the power obstruction; finite residue
fields prove chart injectivity; actual coordinate generation proves field
surjectivity. Full derivations are in the included candidates.

The unchanged predecessors are the Z map at
[ec7da3d29290b8c56a9cc80b8081694abb2674c2](https://github.com/xiangyazi24/FLT/commit/ec7da3d29290b8c56a9cc80b8081694abb2674c2)
and chart equivalence at
[6999499b1155d42c8ac17876012b3625d1a59b1e](https://github.com/xiangyazi24/FLT/commit/6999499b1155d42c8ac17876012b3625d1a59b1e).

## Actual verification

PASS: injectivity assembled source check and .olean emission, 30.584 s,
2553612 KiB RSS, two new public audits standard-three only.
PASS: incremental field-equivalence check and .olean emission, 18.858 s,
2469712 KiB RSS, all eleven new public audits standard-three only.
Lean 4.31.0-rc2 / Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05,
one CPU/thread, 3072 MiB, 60-second limits and shared serialization gate.
The accepted W torsion-free/Dedekind instances are disclosed harness
parameters; no additional production premise appears.

NOT RUN: full FLT imports and ActualZFieldCheck.lean, which await the lead.
No custom axiom, sorry, admit, or native_decide is introduced. The earlier
fixture-comment parsing failure is retained and excluded from acceptance.

Production hashes:
- Injectivity: cb41282f78134c09c6dc34850ca3aabebba7658f4c6d88194758ed253005b38e
- Field equivalence: 30385e97e762506be42ad77698bbf2d8f025463f0044271ea5f30a9612732ad4

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-zfield-manifest.json.
The next owned step is the actual Z-local DVR/field order. YZ local overlap
comparison and the projective product formula remain open. Lead source and
dispatch were reread unchanged before this packet; no root exclusion or
full-project completion is claimed.
