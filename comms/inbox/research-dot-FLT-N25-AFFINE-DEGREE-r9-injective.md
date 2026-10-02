# N25 actual coordinate-rigid fraction-map injectivity

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 9
TYPE: RESULT-SUPPLEMENT
STATUS: CANDIDATE-READY; EXACT-SOURCE-MICROCHECK-PASS; FULL-IMPORT-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: f0eb8381677bc483bddd93826871845030dd5c0e
DISPATCH_COMMIT: aa4e9ffb506978cfebea5fe0ef173ebfa0588cd6
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; new boundary prerequisite, preserving all accepted r9 work

## Genuine completed statement

```lean
MazurProof.N25F_XChartFractionInjective.xChartToFraction_injective :
  Function.Injective N25F_XChartFractionMap.xChartToFraction
```

This proves injectivity of the actual coordinate-rigid map into FractionRing W,
with no extra production hypothesis. If its kernel were nonzero, the X-chart
Dedekind dimension bound and finite-type F2 structure would make the quotient
a finite field. The proven image xW=1/qx would then have finite positive order.
A genuine evaluation of W at [0:0:0:1] proves that no positive power of qx can
be one. Thus the kernel is zero. The proof also exports `originEval`,
`originEval_qx`, and `qx_pow_ne_one`.

Required unchanged candidate dependencies, in order:
1. `N25F_XChartFractionMap.lean` at [44f3f126715e57961d25dd4f3a9a451d3a0a911f](https://github.com/xiangyazi24/FLT/commit/44f3f126715e57961d25dd4f3a9a451d3a0a911f)
2. `N25F_XChartWChartEquiv.lean` at [2dcb8643f3cac5a726a7425d1890770c94c38a26](https://github.com/xiangyazi24/FLT/commit/2dcb8643f3cac5a726a7425d1890770c94c38a26)

The finite-type instance is synthesized from the actual quotient presentation;
X dimension is transported through the actual proved chart equivalence. No
proxy carrier, opaque geometric instance, product formula, or root exclusion
is assumed.

## Actual checks

PASS: separate generic finite-image lemma, source review, exact-source
harness containing 51 original declarations and all three candidate bodies.
The assembled check returned exit 0 in 28.168 s at one CPU/thread, 3072 MiB
and 60 s caps, peak child RSS 2503388 KiB. All four printed public results
use standard propext/Classical.choice/Quot.sound foundations only, with no
sorryAx/custom axiom. Exact Lean 4.31.0-rc2 and Mathlib
96fd0fff3b8837985ae21dd02e712cb5df72ec05.

The harness transparently represents accepted W structure with ordinary
IsDomain W and IsDedekindDomain W parameters. The origin evaluation and power
obstruction require neither; the production imports supply all required
instances, so the final production theorem has no additional premises.

NOT RUN: full FLT imports and the supplied `ActualXChartInjectiveCheck.lean`.
Lead validation and integration remain required. Production SHA-256:
`14281e0684021f327112b5d32e037d2d7cfa173f65290b828fb76407e491313b`.
Passed harness SHA-256:
`17097210b61b026376c6cbafa913bbf9353664d5bde14fc48b98875416e7a661`.

Manifest: `comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r9-injective-manifest.json`.
I continue the exclusive N25 lane with the actual XLocalRing field embedding
and local DVR structure. These downstream statements and the projective
product formula remain separate; N25 is not discharged.
