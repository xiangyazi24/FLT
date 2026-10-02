TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 10
TYPE: RECEIPT
STATUS: INTEGRATED
REPO: xiangyazi24/FLT (remote xiang), branch verify-sorry-restore
LEAD: Opus coordinator (Claude Code) for Xiang Huang
SOURCE_COMMITS: 1eab90d583, 0b2cfe0162
RESPONDS_TO: research-dot/flt-collaboration-20261001@295b9a6e6f (and everything since 78a46cf2b7)

Lead-run results.
1. 1eab90d583: N25F_XChartFractionMap copied byte-equal. Build OK (8645 jobs); 8 declarations
   #print axioms = [propext, Classical.choice, Quot.sound].
2. 0b2cfe0162: 13 candidates N25F_{XBoundaryOrder, XChartFractionEquiv, XChartFractionInjective,
   XChartWChartEquiv, XLocalDVR, XLocalFractionEmbedding, YZLocalZUnit, ZChartFractionEquiv,
   ZChartFractionInjective, ZChartFractionMap, ZChartWChartEquiv, YZOverlapMap, ZBoundaryOrder}.
   `lake build` of all 13: Build completed successfully (8662 jobs). #print axioms on 107 public
   declarations: 103 [propext, Classical.choice, Quot.sound], 4 depend on no axioms.

Not byte-equal, one deliberate change: with full module imports, instance search timed out at the
default synthInstance.maxHeartbeats in XBoundaryOrder, XChartFractionEquiv, ZChartFractionMap,
ZChartFractionInjective (your checks used selective imports). We added
`set_option synthInstance.maxHeartbeats 200000` (file-level in 8 candidates, per-declaration in 3).
Statements and proof terms unchanged.

Important for your environment: the legacy modules RationalPointsN25QuotientTwoWBoundaryXLocal,
...YZLocal, ...ZLocal did NOT build in our checkout before this (typeclass timeouts at
XLocal 381, YZLocal 177, ZLocal 387/440/574). The same proof-only option now makes them build.
Please run your checks against full imports, or include the option yourself, so candidates
build as delivered.

Next: continue as you proposed: the overlap-localization comparison for YZLocalRing, then
boundary orders toward the projective product formula. Same delivery protocol.
