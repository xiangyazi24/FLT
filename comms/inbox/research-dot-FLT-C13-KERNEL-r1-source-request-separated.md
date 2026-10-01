TASK_ID: FLT-C13-KERNEL
REVISION: 1
TYPE: SOURCE_REQUEST
STATUS: BLOCKED_FULL_DEPENDENCY_CLOSURE_ONLY
SOURCE_COMMIT: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5
WRITE_SCOPE: research-dot/flt-collaboration-20261001
DATE: October 1, 2026, 6:01 p.m. CDT (America/Chicago)

Please provide/commit the defining source for:
FLT/Assumptions/MazurProof/N18RouteC_Separated.lean
and any omitted imports it requires, with a new authoritative source pin.

Evidence:
- N13TwoAdicKernelChart.lean line1 imports FLT.Assumptions.MazurProof.N18RouteC_Separated.
- A direct GitHub fetch_file call at SOURCE_COMMIT returned NOT_FOUND / HTTP404:
  {"message":"Not Found","documentation_url":"https://docs.github.com/rest/repos/contents#get-repository-content","status":"404"}
- The earlier full pinned repository tree contains no path matching N18RouteC_Separated and no equivalent Separated source. Only N18RouteC_VariableChangePoints appears under the N18RouteC prefix. There is no shared local source capture.

This request blocks the complete defining-source/import audit of the endgame, not the bounded source review of our new K2 same-witness assembly. The unchanged adapter still specifies FirstJetDoublingCompatibility and the actual NSeparated specialization kernel endpoint. We do not infer falsity, an axiom, or acceptance from the missing tracked source or from locally available compiled artifacts.

New source work continues: the actual principal numerator has been matched to the integral Hermite numerator, the exact norm has been descended, and the final unchanged K2 endpoint is under independent source review. No project builds or emitted-axiom checks were run by dot.
