# Q2641 (dm-codex1): checked AP-constant wiring plan

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
Lean project: `FLT`  
Main files involved:

* `FLT/Assumptions/MazurProof/N12E1CoverResiduals.lean`
* `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`
* `FLT/Assumptions/MazurProof/N12CheckedDescentBridge.lean`

This answer is only about import-layer wiring and theorem shapes after the checked proofs

```lean
fourRatSquaresAPConst_checked : FourRatSquaresAPConst
fourIntSquaresAPConst_checked : FourIntSquaresAPConst
primitiveCenteredFourSqAPDescent_checked : PrimitiveCenteredFourSqAPDescent
```

have been proved in `N12FourSquaresAP.lean`.

## Short verdict

Use the downstream bridge.  Do **not** make `N12E1CoverResiduals.lean` import `N12FourSquaresAP.lean`.

The cleanest plan is:

1. Keep `N12E1CoverResiduals.lean` as the conditional/upstream residual layer.  Its theorems should continue to take

   ```lean
   (hAP : FourRatSquaresAPConst)
   ```

   explicitly.

2. Keep `N12CheckedDescentBridge.lean` importing `N12FourSquaresAP.lean`.  Put the checked inhabitants, the generic adapter, and the no-`hAP` wrappers for the two nonzero covers there.

3. For `N12E1FullCoverExtraction` or rational-point boundary closing theorems, either make those files terminal downstream consumers, or create separate terminal files such as

   ```lean
   N12E1FullCoverExtractionChecked.lean
   N12RationalPointBoundaryChecked.lean
   ```

   that import the bridge and discharge only `hAP` using `fourRatSquaresAPConst_checked`.

Do not push checked facts back upstream into `N12E1CoverResiduals.lean`.

## Dependency direction

The safe dependency graph is:

```text
N12E1CoverResiduals
  defines CoverQ, FourRatSquaresAPConst, DoubleLegCoverDegenerate
  proves conditional cover residuals requiring hAP
        │
        ▼
N12FourSquaresAP
  imports N12E1CoverResiduals
  proves fourRatSquaresAPConst_checked, fourIntSquaresAPConst_checked,
  primitiveCenteredFourSqAPDescent_checked
        │
        ▼
N12CheckedDescentBridge
  imports N12FourSquaresAP
  exposes checked adapters and no-hAP cover wrappers
        │
        ▼
N12E1FullCoverExtractionChecked / RationalPointBoundaryChecked
  terminal downstream wrappers that discharge hAP only
```

Forbidden dependency:

```text
N12E1CoverResiduals ──imports──▶ N12FourSquaresAP
```

That would immediately create the cycle

```text
N12E1CoverResiduals → N12FourSquaresAP → N12E1CoverResiduals.
```

Also avoid the less obvious cycle

```text
N12FourSquaresAP
  → N12E1CoverResiduals
  → N12E1FullCoverExtraction
  → N12CheckedDescentBridge
  → N12FourSquaresAP
```

If `N12E1FullCoverExtraction.lean` is currently upstream of anything used by `N12FourSquaresAP.lean`, do not edit it to import the checked bridge.  Add a new checked terminal wrapper file instead.

## Recommended contents of `N12CheckedDescentBridge.lean`

This file should be tiny and boring.  It should import the constructive proof file and export checked versions of the residual inputs.

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Checked inhabitant of the rational four-squares AP obstruction. -/
theorem checked_FourRatSquaresAPConst : FourRatSquaresAPConst :=
  fourRatSquaresAPConst_checked

/-- Checked inhabitant of the integer four-squares AP obstruction. -/
theorem checked_FourIntSquaresAPConst : FourIntSquaresAPConst :=
  fourIntSquaresAPConst_checked

/-- Checked primitive-centered descent inhabitant. -/
theorem checked_PrimitiveCenteredFourSqAPDescent :
    PrimitiveCenteredFourSqAPDescent :=
  primitiveCenteredFourSqAPDescent_checked

/-- Generic adapter: consume any theorem that only still needs `FourRatSquaresAPConst`. -/
theorem of_checked_FourRatSquaresAPConst {P : Prop}
    (h : FourRatSquaresAPConst → P) : P :=
  h checked_FourRatSquaresAPConst

end MazurProof.RationalPointsN12
```

The generic adapter is useful for large downstream theorems whose remaining binders you do not want to restate.  I would keep it.

## Add no-argument wrappers for the two nonzero cover residuals

Yes: add wrappers in `N12CheckedDescentBridge.lean` for the two nonzero cover residuals.  They are useful downstream because most later files should not have to mention `FourRatSquaresAPConst` anymore.

The most robust Lean shape is to let Lean infer the full dependent function type after applying the first argument `hAP`.  This avoids duplicating long binders and is resilient if the conditional theorem signatures change slightly.

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Checked no-`hAP` version of `coverQ_3_2_6_AP_const`. -/
theorem coverQ_3_2_6_AP_const_checked :=
  coverQ_3_2_6_AP_const checked_FourRatSquaresAPConst

/-- Checked no-`hAP` version of `coverQ_neg1_neg2_2_AP_const`. -/
theorem coverQ_neg1_neg2_2_AP_const_checked :=
  coverQ_neg1_neg2_2_AP_const checked_FourRatSquaresAPConst

/-- Checked no-`hAP` version of `coverQ_3_2_6_forces_X_eq_three`. -/
theorem coverQ_3_2_6_forces_X_eq_three_checked :=
  coverQ_3_2_6_forces_X_eq_three checked_FourRatSquaresAPConst

/-- Checked no-`hAP` version of `coverQ_neg1_neg2_2_forces_X_eq_neg_one`. -/
theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one_checked :=
  coverQ_neg1_neg2_2_forces_X_eq_neg_one checked_FourRatSquaresAPConst

end MazurProof.RationalPointsN12
```

This is the version I would implement first.

If you prefer explicit types for documentation, the first two wrappers should elaborate to the following shapes, assuming the source theorem binders are exactly the obvious `CoverQ` binders after `hAP`:

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Explicit-type version, if the source theorem has this binder shape. -/
theorem coverQ_3_2_6_AP_const_checked_explicit
    {A B C T : ℚ}
    (hQ : CoverQ 3 2 6 A B C T) :
    T ^ 2 = C ^ 2 ∧ C ^ 2 = A ^ 2 ∧ A ^ 2 = B ^ 2 :=
  coverQ_3_2_6_AP_const checked_FourRatSquaresAPConst hQ

/-- Explicit-type version, if the source theorem has this binder shape. -/
theorem coverQ_neg1_neg2_2_AP_const_checked_explicit
    {A B C T : ℚ}
    (hQ : CoverQ (-1) (-2) 2 A B C T) :
    A ^ 2 = B ^ 2 ∧ B ^ 2 = T ^ 2 ∧ T ^ 2 = C ^ 2 :=
  coverQ_neg1_neg2_2_AP_const checked_FourRatSquaresAPConst hQ

end MazurProof.RationalPointsN12
```

For the two `forces_X` theorems, I would initially use the inferred wrapper form:

```lean
theorem coverQ_3_2_6_forces_X_eq_three_checked :=
  coverQ_3_2_6_forces_X_eq_three checked_FourRatSquaresAPConst

theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one_checked :=
  coverQ_neg1_neg2_2_forces_X_eq_neg_one checked_FourRatSquaresAPConst
```

Then run

```lean
#check coverQ_3_2_6_forces_X_eq_three_checked
#check coverQ_neg1_neg2_2_forces_X_eq_neg_one_checked
```

and only expand the explicit statement if downstream readability really needs it.

## Higher-level checked modules

For full cover extraction or the rational-point boundary, I would not mutate an upstream conditional file unless you have verified that nothing in the AP-descent proof imports it.  The safest pattern is a new terminal checked module.

Skeleton:

```lean
import FLT.Assumptions.MazurProof.N12CheckedDescentBridge
import FLT.Assumptions.MazurProof.N12E1FullCoverExtraction
-- import the finite-point / rational-boundary module only if it is downstream
-- and does not feed back into N12FourSquaresAP.

namespace MazurProof.RationalPointsN12

/-!
This file is terminal/downstream.  It may discharge
`FourRatSquaresAPConst` using `checked_FourRatSquaresAPConst`, but it should
not be imported by `N12E1CoverResiduals` or `N12FourSquaresAP`.
-/

/-- Generic checked full-cover adapter.  Use this when the downstream theorem
still has a leading `FourRatSquaresAPConst` assumption. -/
theorem of_checked_full_cover {P : Prop}
    (h : FourRatSquaresAPConst → P) : P :=
  h checked_FourRatSquaresAPConst

/-- If the full-cover theorem also requires `DoubleLegCoverDegenerate`, keep
that assumption explicit.  The checked AP theorem does not discharge it. -/
theorem of_checked_full_cover_with_double_leg {P : Prop}
    (h : FourRatSquaresAPConst → DoubleLegCoverDegenerate → P)
    (hDL : DoubleLegCoverDegenerate) : P :=
  h checked_FourRatSquaresAPConst hDL

end MazurProof.RationalPointsN12
```

Then for each concrete downstream theorem, use a one-line wrapper:

```lean
import FLT.Assumptions.MazurProof.N12CheckedDescentBridge
import FLT.Assumptions.MazurProof.N12E1FullCoverExtraction

namespace MazurProof.RationalPointsN12

/-- Pattern: checked wrapper around a conditional extraction theorem. -/
theorem e1FullCoverExtraction_checked :=
  e1FullCoverExtraction checked_FourRatSquaresAPConst

/-- Pattern: checked wrapper around a conditional theorem that also needs
`DoubleLegCoverDegenerate`.  Keep `hDL` explicit. -/
theorem e1FullCoverExtraction_checked_with_double_leg
    (hDL : DoubleLegCoverDegenerate) :=
  e1FullCoverExtraction checked_FourRatSquaresAPConst hDL

end MazurProof.RationalPointsN12
```

The exact theorem names `e1FullCoverExtraction` and binder order above are placeholders for the declarations already in your file.  The important shape is:

```lean
someConditionalTheorem checked_FourRatSquaresAPConst ...
```

not

```lean
-- bad upstream move
-- prove or import checked_FourRatSquaresAPConst inside N12E1CoverResiduals
```

## Circularity warnings

### `DoubleLegCoverDegenerate`

`DoubleLegCoverDegenerate` is a separate proposition defined in `N12E1CoverResiduals.lean`.  The checked theorem

```lean
fourRatSquaresAPConst_checked : FourRatSquaresAPConst
```

only discharges `FourRatSquaresAPConst`.  It does **not** discharge

```lean
DoubleLegCoverDegenerate
```

unless you have a separate checked theorem proving that proposition.

Therefore do not write terminal wrappers that silently remove both assumptions unless the second checked inhabitant exists:

```lean
-- Only valid if this has actually been proved somewhere downstream-safe:
-- doubleLegCoverDegenerate_checked : DoubleLegCoverDegenerate
```

Until then, wrappers should look like:

```lean
theorem downstream_checked
    (hDL : DoubleLegCoverDegenerate)
    ... : Result :=
  downstream_conditional checked_FourRatSquaresAPConst hDL ...
```

### E24/E1 finite-point theorem

Keep the E24/E1 finite-point theorem layer conditional if it is used upstream in any route that helps prove `fourRatSquaresAPConst_checked`.  A final theorem may combine:

```lean
checked_FourRatSquaresAPConst
```

with a finite-point theorem, but only in a terminal downstream module.

Safe pattern:

```text
conditional finite-point theorem
        │
        ▼
terminal checked boundary wrapper
```

Dangerous pattern:

```text
finite-point theorem imports checked bridge
        │
        ▼
N12FourSquaresAP imports finite-point theorem
        │
        ▼
cycle back to checked bridge / N12FourSquaresAP
```

If in doubt, keep the existing finite-point theorem file assumption-parametric and add a `...Checked.lean` wrapper file that imports both the finite-point theorem and `N12CheckedDescentBridge.lean`.

## Recommended theorem inventory

I would aim for this inventory after the wiring pass.

In `N12E1CoverResiduals.lean`:

```lean
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop := ...
def FourRatSquaresAPConst : Prop := ...
def DoubleLegCoverDegenerate : Prop := ...

theorem coverQ_3_2_6_AP_const
    (hAP : FourRatSquaresAPConst) ... :
    T ^ 2 = C ^ 2 ∧ C ^ 2 = A ^ 2 ∧ A ^ 2 = B ^ 2 := ...

theorem coverQ_neg1_neg2_2_AP_const
    (hAP : FourRatSquaresAPConst) ... :
    A ^ 2 = B ^ 2 ∧ B ^ 2 = T ^ 2 ∧ T ^ 2 = C ^ 2 := ...

theorem coverQ_3_2_6_forces_X_eq_three
    (hAP : FourRatSquaresAPConst) ... : X = 3 := ...

theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one
    (hAP : FourRatSquaresAPConst) ... : X = -1 := ...
```

In `N12FourSquaresAP.lean`:

```lean
import FLT.Assumptions.MazurProof.N12E1CoverResiduals

namespace MazurProof.RationalPointsN12

theorem fourRatSquaresAPConst_checked : FourRatSquaresAPConst := ...
theorem fourIntSquaresAPConst_checked : FourIntSquaresAPConst := ...
theorem primitiveCenteredFourSqAPDescent_checked :
    PrimitiveCenteredFourSqAPDescent := ...

end MazurProof.RationalPointsN12
```

In `N12CheckedDescentBridge.lean`:

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

theorem checked_FourRatSquaresAPConst : FourRatSquaresAPConst :=
  fourRatSquaresAPConst_checked

theorem checked_FourIntSquaresAPConst : FourIntSquaresAPConst :=
  fourIntSquaresAPConst_checked

theorem checked_PrimitiveCenteredFourSqAPDescent :
    PrimitiveCenteredFourSqAPDescent :=
  primitiveCenteredFourSqAPDescent_checked

theorem of_checked_FourRatSquaresAPConst {P : Prop}
    (h : FourRatSquaresAPConst → P) : P :=
  h checked_FourRatSquaresAPConst

theorem coverQ_3_2_6_AP_const_checked :=
  coverQ_3_2_6_AP_const checked_FourRatSquaresAPConst

theorem coverQ_neg1_neg2_2_AP_const_checked :=
  coverQ_neg1_neg2_2_AP_const checked_FourRatSquaresAPConst

theorem coverQ_3_2_6_forces_X_eq_three_checked :=
  coverQ_3_2_6_forces_X_eq_three checked_FourRatSquaresAPConst

theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one_checked :=
  coverQ_neg1_neg2_2_forces_X_eq_neg_one checked_FourRatSquaresAPConst

end MazurProof.RationalPointsN12
```

In a terminal checked full-cover file, only if needed:

```lean
import FLT.Assumptions.MazurProof.N12CheckedDescentBridge
import FLT.Assumptions.MazurProof.N12E1FullCoverExtraction

namespace MazurProof.RationalPointsN12

-- Pattern only: keep non-AP assumptions explicit.
theorem someFullCoverTheorem_checked
    (hDL : DoubleLegCoverDegenerate)
    ... : Result :=
  someFullCoverTheorem checked_FourRatSquaresAPConst hDL ...

end MazurProof.RationalPointsN12
```

## Validation commands

Run these from the local checkout:

```bash
cd /Users/huangx/repos/flt-ai

# Upstream conditional residual layer should still check without importing the checked proof.
lake env lean FLT/Assumptions/MazurProof/N12E1CoverResiduals.lean

# Constructive proof file containing the checked AP constants.
lake env lean FLT/Assumptions/MazurProof/N12FourSquaresAP.lean

# Bridge file with generic adapter and no-hAP wrappers.
lake env lean FLT/Assumptions/MazurProof/N12CheckedDescentBridge.lean

# If you add terminal wrappers, check those too.
lake env lean FLT/Assumptions/MazurProof/N12E1FullCoverExtractionChecked.lean
lake env lean FLT/Assumptions/MazurProof/N12RationalPointBoundaryChecked.lean

# Module builds, if these module names are exposed in the package.
lake build FLT.Assumptions.MazurProof.N12E1CoverResiduals
lake build FLT.Assumptions.MazurProof.N12FourSquaresAP
lake build FLT.Assumptions.MazurProof.N12CheckedDescentBridge

# Whole project catches accidental import cycles.
lake build

# Confirm the residual layer did not acquire a back-import.
rg -n "N12FourSquaresAP|N12CheckedDescentBridge" \
  FLT/Assumptions/MazurProof/N12E1CoverResiduals.lean

# Inspect inferred wrapper types.
rg -n "coverQ_.*_checked|checked_FourRatSquaresAPConst" \
  FLT/Assumptions/MazurProof/N12CheckedDescentBridge.lean
```

## Final recommendation

Implement options **1 and 2** now: keep the generic adapter and add no-argument wrappers in `N12CheckedDescentBridge.lean`.

Use option **3** only as a terminal downstream wrapper layer.  Do not make existing upstream extraction/residual files import the checked bridge unless you have verified they are not in the import cone of `N12FourSquaresAP.lean`.
