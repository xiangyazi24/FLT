# Codex Spec: prove `exists_good_reduction`

## Target
File: `FLT/Assumptions/MazurProof/N18GoodModelAssembly.lean`, line 86.
Replace the `sorry` in `exists_good_reduction` with a complete proof.

## Statement to prove
```lean
theorem exists_good_reduction :
    ∃ red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint,
      ∀ P : GoodPoint, P ∈ red.ker ↔ InFormalKernel P
```

Where:
- `GoodPoint = WeierstrassCurve.Affine.Point E0Good` (over `L = Q(ζ₉)⁺`)
- `RedPoint = WeierstrassCurve.Affine.Point reducedGoodCurve` (over `ZMod 3`, 7 elements)
- `InFormalKernel P = P = 0 ∨ ordPi (xCoordGood P) < 0`
- `E0Good`: `a₁ = a²-2, a₂ = -a²+2a+1, a₃ = a+1, a₄ = -a²+1, a₆ = 4a²-7a-3`
- `reducedGoodCurve`: `a₁ = 2, a₂ = 2, a₃ = 2, a₄ = 0, a₆ = 0` (over `ZMod 3`)

## Background

The number field is `L = Q[a]/(a³-3a-1)`, the maximal real subfield of `Q(ζ₉)`.
The uniformizer is `π = a - 1` with `ordPi(π) = 1`.
The residue field is `OL/π ≅ ZMod 3` with `a ↦ 1 (mod π)`.

E0Good has good reduction at π: `v(Δ(E0Good)) = 0` (discriminant is a unit at π).
Its coefficients are algebraic integers: `v(aᵢ) ≥ 0` for all `i`.

The residue map sends `a ↦ 1`:
- `a₁ = a²-2 ↦ 1-2 = -1 ≡ 2 (mod 3)`
- `a₂ = -a²+2a+1 ↦ -1+2+1 = 2 (mod 3)`
- `a₃ = a+1 ↦ 2 (mod 3)`
- `a₄ = -a²+1 ↦ 0 (mod 3)`
- `a₆ = 4a²-7a-3 ↦ 4-7-3 = -6 ≡ 0 (mod 3)`

These match `reducedGoodCurve` exactly.

## Strategy

### Step 1: Define the residue map on L

We need a function `res : L → ZMod 3` that sends `a ↦ 1` and is a ring
homomorphism on `OL` (the ring of integers of L).

The cleanest approach: use the Dedekind domain infrastructure. The prime
`primeAboveThree` (defined in `N18RouteC_ThreeAdic.lean:138`) gives
`p3 : IsDedekindDomain.HeightOneSpectrum OL`. The residue field of `OL`
at `p3` is `OL/p3.asIdeal ≅ ZMod 3`.

Alternatively, define `res` CONCRETELY:
- Every element of `L` is `c₀ + c₁a + c₂a²` for `c₀, c₁, c₂ ∈ Q`
- If `v(x) ≥ 0` then `c₀, c₁, c₂` can be taken integral
- `res(c₀ + c₁a + c₂a²) := (c₀ + c₁ + c₂ : ℤ) mod 3`

Use whichever approach compiles more easily.

### Step 2: Define the reduction map

```lean
noncomputable def reductionMap : GoodPoint → RedPoint
  | .zero => .zero
  | .some x y h =>
      if hx : ordPi x ≥ 0 then
        -- Both x, y have non-negative valuation (proved from curve equation)
        -- Reduce coordinates mod π
        .some (res x) (res y) (by ...)
      else
        .zero  -- near-origin point
```

Key facts needed:
1. **`v(x) ≥ 0 → v(y) ≥ 0`**: From the curve equation with integral coefficients.
   If `v(x) ≥ 0`, then RHS `= x³ + a₂x² + a₄x + a₆` has `v ≥ 0`.
   LHS `= y² + a₁xy + a₃y = y(y + a₁x + a₃)`. If `v(y) < 0`:
   `v(y²) = 2v(y) < v(y)`, so `v(LHS) = 2v(y) < 0 = v(RHS)`. Contradiction.

2. **Reduced coordinates satisfy the reduced curve**: The Weierstrass equation
   `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` reduces mod π to
   `ȳ² + 2x̄ȳ + 2ȳ = x̄³ + 2x̄²` (using the reduced coefficients).
   This is `reducedGoodCurve`'s equation.

3. **Reduced curve is nonsingular**: Already proved via `reducedGood_isElliptic`.
   The `Nonsingular` condition on the reduced point follows from the equation
   check + discriminant being a unit.

### Step 3: Prove `map_zero`
Trivial: `reductionMap .zero = .zero`.

### Step 4: Prove `map_add` (the hard part)

Need: `reductionMap (P + Q) = reductionMap P + reductionMap Q`.

**Case analysis on P and Q:**

**(a) P or Q = .zero:** Trivial.

**(b) Both integral (`v(x) ≥ 0` for both):**
The Weierstrass addition formula gives `x₃, y₃` as rational functions of
`x₁, y₁, x₂, y₂` and the curve coefficients. Reducing mod π:
`res(x₃) = f(res(x₁), res(y₁), res(x₂), res(y₂), res(a₁), ..., res(a₆))`
which is exactly the addition formula on `reducedGoodCurve`.

Sub-cases:
- x₁ ≠ x₂: secant line, `λ = (y₂-y₁)/(x₂-x₁)`, standard formula
- x₁ = x₂, y₁ = negY(x₁, y₂): inverse, P+Q = O
- x₁ = x₂, y₁ = y₂: tangent line, doubling formula

For each sub-case, need: res commutes with the operations.
CRITICAL: denominators in the addition formula must have `v ≥ 0` and
`res ≠ 0`. When `v(x₁), v(x₂) ≥ 0` and the reduced point is nonsingular,
the denominators are nonzero mod π.

**Approach for (b):** This is the HARDEST case. One option is to verify
ALL 7×7 = 49 point pairs on the reduced curve by `decide` and then show
the addition lifts. But a cleaner approach uses Mathlib's
`WeierstrassCurve.Affine.Point.map` if available (it maps points along
a ring homomorphism). Check if Mathlib has this.

If not available: construct `res` as a ring hom `OL →+* ZMod 3`, then
show `W.map res = reducedGoodCurve`, and use the functoriality of `Point.map`.

**(c) One integral, one near-O:**
`reductionMap(near-O) = O`. Need: `reductionMap(P + near-Q) = reductionMap(P)`.
Equivalently: `P + near-Q` is integral and has the same residue as `P`,
OR `P + near-Q` is near-O and `reductionMap(P) = O` (not generally true).

The first option is correct: adding a near-O point (infinitesimally close to O)
to an integral point P moves P by an infinitesimal amount — the reduction
doesn't change. This requires showing that the addition formula, when one
input has very negative `v(x)`, produces output with the same residue.

**(d) Both near-O:**
`reductionMap(P) = O, reductionMap(Q) = O`. Need: `reductionMap(P+Q) = O`.
i.e., `P + Q = O` or `v(x_{P+Q}) < 0` (near-O).

This is KERNEL CLOSURE. It can be proved from:
- The add_congr_good_weak estimate (if proved first), OR
- Direct computation on the addition formula, OR
- By proving it as a standalone lemma

### Step 5: Prove the kernel characterization
`P ∈ ker(red) ↔ InFormalKernel P`:
- (→): `red(P) = O`. If P = .zero, trivial. If P = .some x y h:
  by definition of `reductionMap`, either `v(x) < 0` (so InFormalKernel), or
  `v(x) ≥ 0` and `red(P) = .some (res x) (res y) _ = O`.
  But `.some _ _ _ ≠ .zero`, contradiction. So `v(x) < 0`.
- (←): `InFormalKernel P`. If P = 0, trivial. If `v(x) < 0`,
  `reductionMap(P) = .zero` by definition.

## Files to create/modify

1. **New file** `FLT/Assumptions/MazurProof/N18GoodReduction.lean`:
   - Import `N18RouteC_GoodModel`, `N18RouteC_Reduction`, `N18RouteC_ThreeAdic`
   - Define the residue map `res : OL → ZMod 3` (or use Mathlib's)
   - Define `reductionMap : GoodPoint → RedPoint`
   - Prove `map_zero`, `map_add`, kernel characterization
   - Export as `exists_good_reduction_proof`
   - Expected: ~400-800 lines

2. **Edit** `N18GoodModelAssembly.lean` line 86:
   - Replace `sorry` with the proof from the new file
   - Add the import

## Available infrastructure

- `ordPi`, `ordPi_mul`, `ordPi_add_ge`, `ordPi_neg` (N18RouteC_ThreeAdic.lean)
- `zero_le_ordPi_intCast c` for `c : ℤ` (integrality of integers)
- `zero_le_ordPi_ringOfIntegers` (N18RouteC_GoodModel.lean)
- `Reduction.RedPoint`, `Fintype RedPoint`, `redPoint_card : #RedPoint = 7`
- `Reduction.seven_nsmul : ∀ P : RedPoint, 7 • P = 0`
- `reducedGoodAffine`, `reducedGoodAffine_eq_true_iff`
- `E0Good_delta : E0Good.Δ = (-8) * goodDiscUnit` (good reduction)
- `p3 : HeightOneSpectrum OL`, `primeAboveThree` (the prime above 3)

## Constraints
- 0 sorry, 0 axiom
- Must compile with `lake build`
- Do NOT modify existing files except to add the import and wire the proof
- For finite ZMod 3 checks, use `decide` or `native_decide`
- If `map_add` is too hard to prove in full generality, consider:
  1. Proving kernel closure as a separate lemma first
  2. Using the finite 49-pair check for integral+integral case
  3. Breaking into very small sub-lemmas

## Verification
```bash
rg -n '\bsorry\b' FLT/Assumptions/MazurProof/N18GoodReduction.lean
# Must return nothing

lake build FLT.Assumptions.MazurProof.N18GoodModelAssembly
```
