# Q2092 (dm1): Mazur torsion theorem session handoff

Date: 2026-06-28  
Source inspected: `xiangyazi24/FLT`, branch `ai-scratch`  
Delivery file: `scratch/_CHATGPT_DROP_dm1.md` on branch `scratch`

## Executive summary

Today’s `ai-scratch` branch has a substantial Mazur torsion-bound scaffold under

```text
FLT/Assumptions/MazurProof/
```

The main theorem now has the right high-level shape:

```lean
theorem MazurProof.mazur_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

It is proved in `TorsionBound.lean` from explicit axiom seams rather than hidden `sorry`s.  The current source is therefore a clean axiom-seam scaffold: the Lean proof path from the seams to `|E(ℚ)_tors| ≤ 16` is closed, and the remaining work is to discharge named mathematical inputs.

Current inspected metrics across `FLT/Assumptions/MazurProof/`:

| Metric | Current value |
|---|---:|
| `sorry` count in MazurProof Lean files | `0` |
| raw `axiom` declarations in MazurProof Lean files | `13` |
| source files in `FLT/Assumptions/MazurProof/` added relative to `main` | `16` |
| branch diff `main..ai-scratch` | `115` commits ahead, `30` behind |
| files changed in `main..ai-scratch` diff | `53` |

Important caveat: I computed the counts by direct GitHub connector inspection of the files under `FLT/Assumptions/MazurProof/`. I did not run a local `lake build`, because this handoff pass used the GitHub connector rather than a local clone.

## 1. Files added/changed in today’s session

The branch diff `main..ai-scratch` reports the following MazurProof files as added.  These are the important source files for the formal scaffold.

| File | Role |
|---|---|
| `FLT/Assumptions/MazurProof.lean` | Top-level import hub for the Mazur proof scaffold. |
| `FLT/Assumptions/MazurProof/Axioms.lean` | Defines the main opaque predicates and the global axiom seams used by the torsion-bound proof. |
| `FLT/Assumptions/MazurProof/CyclotomicLayer.lean` | Documents/collects the cyclotomic interface: primitive root in `ℚ` forces order `≤ 2`. |
| `FLT/Assumptions/MazurProof/DOCTRINE.md` | Axiom-discharge campaign plan and worker split. |
| `FLT/Assumptions/MazurProof/DescentBridge.lean` | N=10 descent bridge from obstruction curve degeneracy to no `ℤ/2 × ℤ/10`. |
| `FLT/Assumptions/MazurProof/DescentBridgeN12.lean` | N=12 bridge with the same pattern. |
| `FLT/Assumptions/MazurProof/DescentBridgeN14.lean` | N=14 bridge with the same pattern. |
| `FLT/Assumptions/MazurProof/DescentBridgeN16.lean` | N=16 bridge with the same pattern. |
| `FLT/Assumptions/MazurProof/DescentObstruction.lean` | `native_decide` local obstruction checks for the 2-isogeny descent on the N=10 curve. |
| `FLT/Assumptions/MazurProof/GroupTheory.lean` | Proved finite group/ZMod embedding lemmas, including `(ZMod m)^2 ↪ ZMod m × ZMod n` when `m ∣ n`. |
| `FLT/Assumptions/MazurProof/NoncyclicN10.lean` | Wrapper proving N=10 and N=12 noncyclic exclusions from the bridge files. |
| `FLT/Assumptions/MazurProof/ObstructionCurve.lean` | Concrete 20.a4/20a1 curve data, visible rational points, explicit addition table, and rational-points-complete axiom. |
| `FLT/Assumptions/MazurProof/RootsOfUnity.lean` | Fully proved rational roots-of-unity lemmas; no axioms and no sorries. |
| `FLT/Assumptions/MazurProof/TorsionBound.lean` | Main proof of `mazur_torsion_bound` from the axiom seams. |
| `FLT/Assumptions/MazurProof/TorsionFinite.lean` | Reduces torsion finiteness to a Mordell-Weil finite-generation axiom and proves the module-theoretic torsion-finite step. |
| `FLT/Assumptions/MazurProof/UNDERSTANDING.md` | Architecture notes, dependency graph, and discharge order. |

The branch diff also reports a large `scratch/` work area.  The files are mostly exploratory Lean code, Python checks, and handoff/drop documents supporting the N=10/N=12/N=14/N=16 obstruction and denominator descent work:

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

Recent `ai-scratch` commit heads I inspected include:

| Short SHA | Commit message | Main touched file(s) visible from the commit/diff |
|---|---|---|
| `848ffbf` | `Fix API errors in num_abs_le_one Lean drop` | `scratch/_CHATGPT_DROP_dm2.md` |
| `8f993e5` | `Add axiom-free Lean draft for num_abs_le_one descent bound` | `scratch/_CHATGPT_DROP_dm2.md` |
| `14f18b5` | `Update zphi even-core proof drop` | `scratch/_CHATGPT_DROP_dm1.md` |
| `0f4b437` | `Add rational to integer bridge for 20a4` | `scratch/_CHATGPT_DROP_dm2.md` |
| `46ccdff` | `Update dm1 with obstruction 20a4 final assembly` | `scratch/_CHATGPT_DROP_dm1.md` |

These recent commits are mostly scratch/drop-document work.  The `FLT/Assumptions/MazurProof/` scaffold itself is the durable source-tree artifact.

## 2. Current `sorry` count across `MazurProof/`

Current inspected count:

```text
0
```

I found no `sorry` occurrences in the inspected Lean files under

```text
FLT/Assumptions/MazurProof/
```

and in the top-level import file

```text
FLT/Assumptions/MazurProof.lean
```

Suggested verification command for the next local session:

```bash
grep -RIn --include='*.lean' '\bsorry\b' \
  FLT/Assumptions/MazurProof \
  FLT/Assumptions/MazurProof.lean
```

Expected output: no matches.

## 3. Current axiom count

Current raw `axiom` declaration count across the inspected MazurProof Lean files:

```text
13
```

Breakdown:

| File | Count | Axiom declarations |
|---|---:|---|
| `Axioms.lean` | `3` | `rational_torsion_two_invariant_factors`, `weil_pairing_primitive_root`, `no_rational_point_of_order_ge_17` |
| `TorsionFinite.lean` | `1` | `mordell_weil_fg` |
| `DescentBridge.lean` | `2` | `obstruction_curve_20a4_points_degenerate`, `Z2xZ10_gives_non_degenerate_E20_point` |
| `DescentBridgeN12.lean` | `2` | `obstruction_curve_N12_points_degenerate`, `Z2xZ12_gives_non_degenerate_N12_point` |
| `DescentBridgeN14.lean` | `2` | `obstruction_curve_N14_points_degenerate`, `Z2xZ14_gives_non_degenerate_N14_point` |
| `DescentBridgeN16.lean` | `2` | `obstruction_curve_N16_points_degenerate`, `Z2xZ16_gives_non_degenerate_N16_point` |
| `ObstructionCurve.lean` | `1` | `E20_rational_points_complete` |

Suggested verification command for the next local session:

```bash
grep -RIn --include='*.lean' '^\s*axiom\b' \
  FLT/Assumptions/MazurProof \
  FLT/Assumptions/MazurProof.lean
```

### Interpreting the 13 raw axioms

Do not interpret the number `13` as 13 equally deep mathematical holes.  The current code intentionally refines a few large seams into smaller independent axioms:

1. **Global torsion structure / finite abelian group input.**
   - `rational_torsion_two_invariant_factors`
   - `mordell_weil_fg`

2. **Weil pairing / cyclotomic input.**
   - `weil_pairing_primitive_root`

3. **Deep cyclic Mazur bound.**
   - `no_rational_point_of_order_ge_17`

4. **Noncyclic obstruction bridges.**
   - Two bridge axioms each for N=10, 12, 14, 16.

5. **Explicit obstruction-curve rational-points certificate.**
   - `E20_rational_points_complete`.

The good news is that all uses of these inputs are named, narrow, and easy to grep.

## 4. What is actually proved now

### Roots of unity in `ℚ`

`RootsOfUnity.lean` proves the rational cyclotomic endpoint:

```lean
theorem isPrimitiveRoot_rat_order_le_two {ζ : ℚ} {m : ℕ}
    (hζ : IsPrimitiveRoot ζ m) : m ≤ 2
```

and also proves that a rational finite-order element is `1` or `-1`.

This is the downstream consumer of the Weil-pairing theorem.  Once the pairing gives a primitive `m`-th root in `ℚ`, the contradiction for `m ≥ 3` is already formalized.

### Pure group theory

`GroupTheory.lean` proves the key finite `ZMod` embeddings.  The most important one for the torsion-structure argument is:

```lean
theorem zmod_prod_contains_square
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    ∃ f : ZMod m × ZMod m →+ ZMod m × ZMod n, Function.Injective f
```

This turns the first invariant factor into full rational `m`-torsion in the skeleton:

```lean
theorem first_invariant_factor_full_torsion ... :
    HasFullRationalTorsion E m
```

Notably, `first_invariant_factor_full_torsion` is now a theorem, not an axiom.

### Torsion finite from Mordell-Weil finite generation

`TorsionFinite.lean` contains one axiom:

```lean
axiom mordell_weil_fg (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point
```

From this it proves the module-theoretic result that the torsion subgroup is finite.  This is a useful reduction: the remaining hard input is the standard Mordell-Weil finite-generation theorem, not a bespoke torsion-finiteness assertion.

### Main torsion-bound skeleton

`TorsionBound.lean` proves the desired numerical result from the seams:

1. Use torsion structure to write `|T| = m * n`, with `m ∣ n`.
2. Use first-invariant-factor full torsion plus the Weil pairing to prove `m ≤ 2`.
3. Use `no_rational_point_of_order_ge_17` to get `n ≤ 16`.
4. If `m = 1`, conclude `|T| = n ≤ 16`.
5. If `m = 2`, then if `n > 8`, parity plus `n ≤ 16` forces `n ∈ {10,12,14,16}`.
6. Use the noncyclic exclusions to contradict `ℤ/2 × ℤ/n` for those four values.
7. Conclude `n ≤ 8`, hence `|T| = 2n ≤ 16`.

This is exactly the right Mazur-theorem skeleton.

## 5. WeilPairing engineering plan

### Current repository status

The inspected `ai-scratch` tree currently has the high-level seam

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

in `Axioms.lean`.

I did **not** find a committed `WeilPairingInterface.lean` under the inspected `FLT/Assumptions/MazurProof/` tree.  If that file exists locally or on another branch, the next integration step is to land it on `ai-scratch` and import it from the MazurProof module graph.

### Layer 1 — abstract Galois-Weil interface: done as the intended first engineering layer

Layer 1 should be kept independent of the concrete elliptic-curve function-field implementation.

The goal of Layer 1 is:

```text
Abstract nondegenerate alternating Galois-equivariant pairing
on a free rank-2 ZMod m torsion module
+
all torsion points Galois-fixed
------------------------------------------------------------
base field contains a primitive m-th root of unity
```

The key theorem shape is:

```lean
primitive_root_in_base
```

Mathematically, the proof is simple and should remain the trusted core:

1. Pick a `ZMod m` basis `P, Q` of the torsion module.
2. Nondegeneracy/alternating perfectness implies `e P Q` is a primitive `m`-th root.
3. Since all torsion points are rational/Galois-fixed, `P` and `Q` are fixed by every Galois element.
4. By Galois equivariance of the pairing, `e P Q` is also fixed.
5. Therefore the primitive root lies in the base field.

Layer 1 should expose only one bridge seam from the real elliptic-curve world into the abstract data, e.g.

```lean
weil_interface_bridge
```

or similarly named.  That bridge is morally equivalent to the old `weil_pairing_primitive_root` axiom, but it is strictly better engineering because the pure Galois descent theorem is fully separated from the future Miller-function/divisor construction.

Recommended integration pattern:

```lean
-- future Axioms.lean / WeilPairing.lean structure

theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- obtain AbstractGaloisWeilData from the bridge
  -- apply primitive_root_in_base
```

So downstream `TorsionBound.lean` should not change: it should continue to call `weil_pairing_primitive_root`.

### Layer 2 — concrete Miller/function-field construction: planned

Layer 2 should build the actual elliptic-curve Weil pairing over Mathlib’s affine Weierstrass function-field API.

The relevant Mathlib types are:

```lean
W.CoordinateRing
W.FunctionField
```

with

```text
CoordinateRing = AdjoinRoot W.polynomial
FunctionField  = FractionRing W.CoordinateRing
```

For the Miller-function layer, the exact function-field element for the vertical line `x - a` is:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (WeierstrassCurve.Affine.CoordinateRing.XClass W a)
```

or inside `namespace WeierstrassCurve.Affine`:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.XClass W a)
```

The expanded form is:

```lean
algebraMap W.CoordinateRing W.FunctionField
  (CoordinateRing.mk W
    (Polynomial.C ((Polynomial.X : F[X]) - Polynomial.C a)))
```

Do **not** use bare

```lean
AdjoinRoot.mk (Polynomial.X - Polynomial.C a)
```

at the outer level: the coordinate ring polynomial lives in `F[X][Y]`, and the outer `Polynomial.X` is the `Y` variable.  The affine `x` coordinate is the inner `Polynomial.X : F[X]`, wrapped by the outer `Polynomial.C`.

Recommended first `MillerFunction.lean` wrappers:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F]
variable (W : Affine F)

/-- Coordinate-ring class of the vertical line `x = a`, i.e. the function `x - a`. -/
def verticalCoord (a : F) : W.CoordinateRing :=
  CoordinateRing.XClass W a

/-- Function-field vertical line `x - a`. -/
def verticalFunction (a : F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (verticalCoord W a)

/-- Coordinate-ring class of `Y - p(X)`. -/
def yMinusPolynomialCoord (p : F[X]) : W.CoordinateRing :=
  CoordinateRing.YClass W p

/-- Function-field element `Y - p(X)`. -/
def yMinusPolynomialFunction (p : F[X]) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (yMinusPolynomialCoord W p)

end Affine
end WeierstrassCurve
```

Then build upward:

1. `verticalFunction W a` for vertical denominator factors.
2. `yMinusPolynomialFunction W p` for line/tangent numerator terms.
3. Definitions for line through two affine points and tangent at one affine point.
4. Divisor statement for each line function and vertical function.
5. Miller loop function.
6. Miller divisor theorem.
7. Weil pairing definition from Miller functions.
8. Bilinearity, alternatingness, nondegeneracy, and Galois equivariance.
9. Instantiate Layer 1’s abstract data.
10. Replace the old `weil_pairing_primitive_root` axiom by a theorem depending only on the Layer 2 bridge until the bridge itself is discharged.

## 6. Known issues and consistency checks

### A. `UNDERSTANDING.md` is partially stale

`UNDERSTANDING.md` still speaks in terms of a smaller older seam count and says “6 axiom seams.”  The current raw Lean count is 13 `axiom` declarations because the noncyclic obstruction is split into several bridge axioms.

Recommendation: update `UNDERSTANDING.md` after the next source integration pass so that it distinguishes:

```text
raw Lean axiom declarations: 13
logical seam clusters: about 5
```

### B. Obstruction curve model naming needs alignment

There is a possible model mismatch to resolve before investing heavily in the N=10 certificate path:

- `DescentBridge.lean` uses the affine equation

  ```lean
  w ^ 2 = u ^ 3 + u ^ 2 - u
  ```

- `ObstructionCurve.lean` defines the LMFDB/Cremona curve with coefficients `[0,1,0,4,4]`, i.e.

  ```text
  y² = x³ + x² + 4x + 4
  ```

These may be isomorphic/related models, but the bridge file and the concrete curve certificate should make the model transformation explicit.  Otherwise it will be easy to prove rational-points completeness for one model while the noncyclic bridge expects another.

### C. Local obstruction checks are not the global descent

`DescentObstruction.lean` has real `native_decide` local checks, but the bridge from those finite checks to global rational-point degeneracy remains an axiom.  This is expected; just do not overstate `native_decide` as proving the whole N=10 exclusion by itself.

### D. Layer 1 WeilPairing interface needs to land in source

The current source tree still has the direct axiom `weil_pairing_primitive_root`.  If `WeilPairingInterface.lean` is already written elsewhere, land it next and make the dependency graph explicit.

## 7. Recommended next session plan

### Step 0: verify build and metrics locally

Run:

```bash
git checkout ai-scratch
lake build FLT.Assumptions.MazurProof

grep -RIn --include='*.lean' '\bsorry\b' \
  FLT/Assumptions/MazurProof \
  FLT/Assumptions/MazurProof.lean

grep -RIn --include='*.lean' '^\s*axiom\b' \
  FLT/Assumptions/MazurProof \
  FLT/Assumptions/MazurProof.lean
```

Expected metrics from this handoff:

```text
sorry count: 0
raw axiom count: 13
```

### Step 1: land Layer 1 WeilPairing interface

Create or integrate:

```text
FLT/Assumptions/MazurProof/WeilPairingInterface.lean
```

Target contents:

- abstract torsion module data;
- abstract pairing data;
- Galois-fixed/rationality assumptions;
- theorem `primitive_root_in_base` fully proved;
- a bridge seam from actual elliptic curves to the abstract data.

Then add an import path, preferably through a future

```text
FLT/Assumptions/MazurProof/WeilPairing.lean
```

and keep `TorsionBound.lean` unchanged.

### Step 2: replace direct Weil axiom by theorem-plus-bridge

Current:

```lean
axiom weil_pairing_primitive_root ...
```

Desired intermediate state:

```lean
theorem weil_pairing_primitive_root ... := by
  -- obtain abstract data by bridge
  -- exact primitive_root_in_base ...
```

with one explicit bridge axiom/sorry equivalent to:

```lean
actual_curve_has_abstract_galois_weil_data
```

This reduces conceptual risk: the Galois descent argument will be proved independently, and only the EC construction remains open.

### Step 3: start Layer 2 with function-field wrappers

Create:

```text
FLT/Assumptions/MazurProof/MillerFunction.lean
```

First compile only the tiny wrappers:

```lean
verticalCoord
verticalFunction
yMinusPolynomialCoord
yMinusPolynomialFunction
```

Do not attempt the full Miller loop until these compile against the pinned Mathlib API.

### Step 4: normalize the N=10 obstruction model

Before proving more about N=10, decide and document the precise relationship between:

```text
w² = u³ + u² - u
```

and

```text
y² = x³ + x² + 4x + 4
```

If they are isomorphic models, add the explicit rational transformation and theorem boundary.  If one is stale, update the stale file now.

### Step 5: choose the next axiom to discharge

Good next targets by feasibility:

1. **WeilPairing Layer 1 integration** — highest leverage, mostly pure algebra already designed.
2. **Torsion finite refinement** — `mordell_weil_fg` is standard, but proving Mordell-Weil itself is far beyond this local project; keep it as a named global theorem seam.
3. **N=10 obstruction bridge cleanup** — good for concrete progress, but requires model alignment and descent/rank-zero certificate boundaries.
4. **N=14/N=16 descent bridges** — likely need careful quartic-descent algebra, including the corrected N=14 factorization structure.
5. **Cyclic order ≥17** — deepest Mazur core; do not attack until the lighter seams are cleanly organized.

## 8. Bottom-line handoff

The Mazur torsion proof scaffold is in a good formalization state:

- zero `sorry` in the inspected MazurProof Lean source;
- main theorem `mazur_torsion_bound` proved from explicit seams;
- rational roots-of-unity endpoint fully proved;
- pure finite-group embedding lemmas proved;
- torsion finiteness reduced to Mordell-Weil finite generation;
- noncyclic cases factored into explicit descent/obstruction-curve bridge axioms.

The highest-value next move is not to change `TorsionBound.lean`.  It is to integrate the Layer 1 WeilPairing interface as a theorem-producing replacement for the direct `weil_pairing_primitive_root` axiom, while preserving the same downstream API.  After that, start the concrete `MillerFunction.lean` Layer 2 with the small `CoordinateRing.XClass` / `CoordinateRing.YClass` wrappers and build upward only after those compile.
