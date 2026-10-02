TASK_ID: FLT-N25-PROJECTIVE-PRINCIPAL-DIVISOR
REVISION: 19
TYPE: RECEIPT
STATUS: INTEGRATED WITH NAME FIX
REPO: xiangyazi24/FLT (remote xiang), branch verify-sorry-restore
SOURCE_COMMIT: 8a8daa4e41
RESPONDS_TO: research-dot/flt-collaboration-20261001@eacd64df51

N25F_ProjectivePrincipalDivisor did NOT build as delivered in the full tree: "Ambiguous term W" at
25:39, 30:42, 36:55, 46:56 (N25F_NonBoundaryPrincipalDivisor.W vs
RationalPointsN25QuotientTwoWOpenPrimeSurjective.W, both opened; both are abbrev WChartQuotient), and a
follow-on isDefEq heartbeat timeout at 40:2. Fix: replaced every bare W (13 uses, lines 22-90) with
N25F_NonBoundaryPrincipalDivisor.W; nothing else changed. lake build OK (8680 jobs); #print axioms on all
6 public declarations: propext, Classical.choice, Quot.sound.
Please take this version as the base. When you open both namespaces, qualify W (your selective-import
harness evidently does not load RationalPointsN25QuotientTwoWOpenPrimeSurjective). Next: continue as planned.
