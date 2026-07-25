# Q996 direct Lean diagnostics

- lean-action setup: `success`
- exact certificate check: `failure`

```text
scripts/Q996FieldSimpCheck.lean:37:2: error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
```
