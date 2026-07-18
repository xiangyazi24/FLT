# Codex Spec: prove `add_congr_good_weak` via transfer

## Target
File: `FLT/Assumptions/MazurProof/N18GoodModelAssembly.lean`, line 262.
Replace the `sorry` in `add_congr_good_weak` with a complete proof.

## Statement to prove
```lean
theorem add_congr_good_weak (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    2 * min
        (vpiGood (MazurProof.N18PackageII.zParamGood P))
        (vpiGood (MazurProof.N18PackageII.zParamGood Q)) ≤
      vpiGood
        (MazurProof.N18PackageII.zParamGood (P + Q) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood Q)
```

Where:
- `GoodPoint = E0GoodPoint = WeierstrassCurve.Affine.Point E0Good`
- `InFormalKernel P = P = 0 ∨ ordPi (xCoordGood P) < 0`
- `zParamGood(.some x y _) = -x/y`, `zParamGood(.zero) = 0`
- `vpiGood` = `ordPi` extended to `WithTop ℤ` (`⊤` at `0`)

## Strategy: Transfer from E0 via e0GoodEquiv

DO NOT port the 1278-line proof. Instead, transfer the ALREADY PROVED
`add_congr_wired` (in `N18AddCongrWired.lean:56`, sorry-free) from E0
to E0Good using the additive group isomorphism `e0GoodEquiv`.

### Key infrastructure already available

1. `e0GoodEquiv : E0Point ≃+ E0GoodPoint` (N18RouteC_GoodModel.lean:138)
   - Via variable change: `(X,Y) ↦ (u²X+r, u³Y+u²sX+t)`
   - `u = scale = a²-a-3`, `v(u) = 1` (since `scale = pi * changeS`, `v(changeS) = 0`)
   - `r = 3+a-a²` (integral, `v(r) ≥ 0`; note `r = -scale = -u`)
   - `s = 2-a²` (integral, `v(s) ≥ 0`)
   - `t = -8-2a+2a²` (integral, `v(t) ≥ 0`)

2. `add_congr_wired` (N18AddCongrWired.lean:56, sorry-free):
   ```lean
   theorem add_congr_wired (P Q : E0Point)
       (hP : P = 0 ∨ ordPi (xCoord P) < 0)
       (hQ : Q = 0 ∨ ordPi (xCoord Q) < 0) :
       zParam (P + Q) - zParam P - zParam Q = 0 ∨
       v (zParam P) + v (zParam Q) ≤
         v (zParam (P + Q) - zParam P - zParam Q)
   ```

3. `val_coords` (in N18AddCongrProof.lean or N18AddCongr.lean):
   For E0 point (x,y) with `v(x) < 0`: `v(x) = -2r`, `v(y) = -3r` where `r = ordPi(-x/y)`.

### The transfer route (4 steps)

**Step 1: Pointwise identity lemma**

For an affine point `(x,y)` on E0 with `y ≠ 0`, let `z = -x/y`, `w = -1/y`.
Under the variable change φ, the good-model formal parameter is:

```
zParamGood(φ(x,y)) = (u²z + r·w) / (u³ - u²s·z - t·w)
```

This is an exact algebraic identity (field_simp; ring).
Bonus: `r = -u`, so numerator = `u(uz - w)`. But the estimates work without this.

Put this lemma in a new file or at the top of Assembly. It needs:
- `hns : Nonsingular E0 x y` (to have a point)
- `hy0 : y ≠ 0` (to define z, w)
- Conclusion: exact identity relating `zParamGood(e0GoodEquiv P)` and `zParam P`.

**Step 2: δ-bound lemma**

Define `δ(P) := zParamGood(e0GoodEquiv(P)) - zParam(P) / u`.

For P in E0's kernel with `r := ordPi(zParam P) ≥ 2`:
- Numerator of `δ` has every term with `v ≥ 2 + 2r`
- Denominator has `v = 4` (since `v(u³) = 3`, dominating `v(u²sz) = 2+r ≥ 4`, `v(tw) = 3r ≥ 6`)
- So `v(δ(P)) ≥ 2r - 2 = 2·v(zGood(φP))`

State with abstract hypotheses: `v(u) = 1`, `v(r), v(s), v(t) ≥ 0`, `r ≥ 2`.

**Step 3: Widen add_congr_wired**

The existing `add_congr_wired` concludes with:
```
error = 0 ∨ v(zP) + v(zQ) ≤ v(error)
```

We also need: `P + Q = 0 ∨ ordPi(xCoord(P+Q)) < 0` (i.e., the sum stays in the kernel).

OPTION A: Add this as a conjunct to `add_congr_wired`. The proof's three branches
(inverse, tangent, distinct-x) already compute `x₃` and control its valuation
internally — this information just needs to be exposed.

OPTION B: Prove a separate `kernel_add_closed_E0` lemma for E0. For P, Q with
`ordPi(xCoord P) < 0` and `ordPi(xCoord Q) < 0`, show `P+Q = 0 ∨ ordPi(xCoord(P+Q)) < 0`.
This can be proved by case-splitting on the addition formula and using that
`v(x₁), v(x₂) ≤ -3` (since they come from E0Good kernel pullback with `r ≥ 2`, so
`v(x) = -2r ≤ -4`).

PREFER OPTION B (separate lemma, no touching the 1278-line file).

The specific bound needed: for points from E0Good's kernel, `r ≥ 2`, so `v(x) ≤ -4`.
For the distinct-x case:
- `x₃ = λ² + a₁λ - a₂ - x₁ - x₂` where `λ = (y₂-y₁)/(x₂-x₁)`
- `v(x₁), v(x₂) ≤ -4`, `v(y₁) = (3/2)v(x₁) ≤ -6`
- `v(λ) = v(y) - v(x) ≈ (1/2)v(x) ≤ -2`
- `v(λ²) ≤ -4`, `v(a₁λ) ≥ v(λ) ≥ -2` (weaker), `v(a₂) ≥ 0`
- `v(x₃) = min(v(λ²), v(x₁+x₂)) ≤ -4` (dominant terms are very negative)
  Even with cancellation: all correction terms `a₁λ, a₂` have strictly higher valuation.

**Step 4: Assembly**

With `m := min(r_P, r_Q) ≥ 2` (where `r = v(zGood)` on E0Good):

```
errorGood = (1/u) · errorE0 + δ(P+Q) - δ(P) - δ(Q)
```

- `v((1/u) · errorE0)`: wired gives `v(errorE0) ≥ r_P' + r_Q' = (m+1) + (m+1) = 2m+2`
  minus `v(u) = 1` → `v ≥ 2m+1 ≥ 2(m-1)`
  (or errorE0 = 0 → this term = 0 → `v = ⊤`)
- `v(δ(P)), v(δ(Q)) ≥ 2m - 2` (from step 2)
- `v(δ(P+Q)) ≥ 2r₃ - 2` where `r₃ = v(z_{P+Q}) ≥ m` (from wired + ultrametric)
  so `v(δ(P+Q)) ≥ 2m - 2`

All four terms have `v ≥ 2(m-1)`. Ultrametric gives `v(errorGood) ≥ 2(m-1) = 2·min(v(zGood_P), v(zGood_Q))`.

Target statement has `2 * min(...)` on the LHS. ✓

### Files to create/modify

1. **New file** `FLT/Assumptions/MazurProof/N18AddCongrGoodTransfer.lean`:
   - Import `N18AddCongrWired`, `N18RouteC_GoodModel`, `N18VpiWrapper`, `N18PackageII`
   - Pointwise identity lemma
   - δ-bound lemma
   - kernel_add_closed_E0 (for points with r ≥ 2)
   - Main assembly theorem proving `add_congr_good_weak`'s exact statement
   - Expected: ~200-350 lines

2. **Edit** `N18GoodModelAssembly.lean` line 262:
   - Replace `sorry` with `N18AddCongrGoodTransfer.add_congr_good_transfer P Q hP hQ`
   - Add `import FLT.Assumptions.MazurProof.N18AddCongrGoodTransfer`

### Valuation toolkit available
- `ordPi_mul`, `ordPi_add_ge`, `ordPi_neg`, `ordPi_one`, `ordPi_zero`
- `zero_le_ordPi_intCast`, `zero_le_ordPi_ringOfIntegers`
- `OrdGood` predicate (in N18AddCongrProof.lean) with `.add`, `.mul`, `.neg`, etc.
- `val_coords` (for E0): `v(x) = -2r`, `v(y) = -3r`

### Constraints
- 0 sorry, 0 axiom in the new file
- Must compile with `lake build` against the current lakefile
- Do NOT modify N18AddCongrProof.lean or N18AddCongrWired.lean
- Use `field_simp` + `ring` / `linear_combination` for algebraic identities
- Use `omega` for integer arithmetic on valuations
- Handle `P = 0` / `Q = 0` cases separately (trivial: `zParamGood 0 = 0`, `vpiGood 0 = ⊤`)

### Verification
```bash
rg -n '\bsorry\b' FLT/Assumptions/MazurProof/N18AddCongrGoodTransfer.lean
# Must return nothing

lake build FLT.Assumptions.MazurProof.N18GoodModelAssembly
# Must succeed (may timeout on large heartbeat — add `set_option maxHeartbeats 0` if needed)
```
