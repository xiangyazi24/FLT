# Q2935 dm-codex2: next integration step after checked four-squares AP descent

Namespace: `MazurProof.RationalPointsN12`.

Target local files:

```text
FLT/Assumptions/MazurProof/N12FourSquaresAP.lean
FLT/Assumptions/MazurProof/KubertBridgeN12.lean
FLT/Assumptions/MazurProof/RationalPointsN12.lean
```

I could not fetch the local N12 files through GitHub, so this is keyed to the verified theorem shapes in the prompt. Since `N12FourSquaresAP.lean` and `KubertBridgeN12.lean` both pass after the checked AP file, this is now an **integration task**, not a new Fermat-four-square AP mathematical residual.

## 1. Highest-value replacement now

Replace any remaining residual/axiom/hypothesis of type

```lean
FourRatSquaresAPConst
```

or a wrapper whose only AP input is

```lean
(hAP : FourRatSquaresAPConst)
```

by the checked theorem

```lean
fourRatSquaresAPConst_checked : FourRatSquaresAPConst
```

Concretely, search the local tree:

```bash
rg "FourRatSquaresAPConst|fourRatSquaresAPConst|APConst|FourSquares" \
  FLT/Assumptions/MazurProof/KubertBridgeN12.lean \
  FLT/Assumptions/MazurProof/RationalPointsN12.lean \
  FLT/Assumptions/MazurProof -n
```

The first theorem to replace is likely a Kubert bridge theorem of the form:

```lean
-- likely current residual shape
axiom / theorem kubertN12_obstruction_of_fourRatSquaresAPConst :
  FourRatSquaresAPConst → KubertN12ObstructionStatement
```

or a main N12 assembly theorem with a parameter:

```lean
(hAP : FourRatSquaresAPConst) → ...
```

Replace it by a checked wrapper:

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP
-- plus the local file that defines the Kubert residual interface

namespace MazurProof.RationalPointsN12

/-- Checked AP input for the Kubert N=12 route. -/
theorem kubertN12_fourRatSquaresAPConst_checked : FourRatSquaresAPConst := by
  exact fourRatSquaresAPConst_checked

end MazurProof.RationalPointsN12
```

Then remove the AP parameter in the first downstream theorem by applying the old residual theorem to `fourRatSquaresAPConst_checked`.

Example wrapper pattern:

```lean
namespace MazurProof.RationalPointsN12

-- If this exists:
-- theorem kubertN12Obstruction_of_fourRatSquaresAPConst :
--     FourRatSquaresAPConst → KubertN12ObstructionStatement := ...

/-- AP-free checked Kubert obstruction. -/
theorem kubertN12Obstruction_checked :
    KubertN12ObstructionStatement := by
  exact kubertN12Obstruction_of_fourRatSquaresAPConst fourRatSquaresAPConst_checked

end MazurProof.RationalPointsN12
```

This is the immediate integration if the downstream file already has the AP-to-Kubert interface. It should be a tiny edit in `KubertBridgeN12.lean` or a small downstream bridge file.

## 2. Concrete curve bridge to add now

The Kubert curve named in the prompt is the E1 curve after the shift

```text
X = u - 1,  Y = w.
```

Indeed:

```text
u^3 - u^2 - 4u + 4 = (u - 1) * (u - 2) * (u + 2)
                      = X * (X - 1) * (X + 3).
```

Add this theorem wherever `E1FullCoverCurve` is visible. It is a pure algebra bridge and is independent of AP descent.

```lean
import Mathlib.Tactic
-- import the file that defines `E1FullCoverCurve`

namespace MazurProof.RationalPointsN12

/-- Kubert N=12 auxiliary curve in the shifted `u` coordinate. -/
def KubertN12Curve (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4

/-- The Kubert curve is the E1 curve under `X = u - 1`. -/
theorem kubertN12Curve_iff_E1_shift (u w : ℚ) :
    KubertN12Curve u w ↔ E1FullCoverCurve (u - 1) w := by
  unfold KubertN12Curve E1FullCoverCurve
  constructor <;> intro h
  · calc
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := h
      _ = (u - 1) * ((u - 1) - 1) * ((u - 1) + 3) := by ring
  · calc
      w ^ 2 = (u - 1) * ((u - 1) - 1) * ((u - 1) + 3) := h
      _ = u ^ 3 - u ^ 2 - 4 * u + 4 := by ring

/-- Forward direction, often easier for rewriting. -/
theorem E1_shift_of_kubertN12Curve {u w : ℚ}
    (h : KubertN12Curve u w) :
    E1FullCoverCurve (u - 1) w := by
  exact (kubertN12Curve_iff_E1_shift u w).1 h

/-- Backward direction, often easier after E1 classification. -/
theorem kubertN12Curve_of_E1_shift {u w : ℚ}
    (h : E1FullCoverCurve (u - 1) w) :
    KubertN12Curve u w := by
  exact (kubertN12Curve_iff_E1_shift u w).2 h

end MazurProof.RationalPointsN12
```

This bridge is useful in both routes:

* full-cover/E1 route: square-discriminant point on Kubert curve becomes an E1 point;
* AP route: any existing E1-to-four-square-AP bridge can be reused by shifting `u` to `X = u - 1`.

## 3. If the AP-to-Kubert interface already exists

If `KubertBridgeN12.lean` already has a theorem that turns `FourRatSquaresAPConst` into the required Kubert obstruction, add only this checked wrapper.

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP
import FLT.Assumptions.MazurProof.KubertBridgeN12

namespace MazurProof.RationalPointsN12

/-- The previously residual AP input is now discharged by the checked AP file. -/
theorem kubertN12_APObstruction_checked :
    KubertN12APObstructionStatement := by
  exact kubertN12_APObstruction_of_fourRatSquaresAPConst
    fourRatSquaresAPConst_checked

end MazurProof.RationalPointsN12
```

Use the actual local names after `#check`:

```lean
#check FourRatSquaresAPConst
#check fourRatSquaresAPConst_checked
#check kubertN12_APObstruction_of_fourRatSquaresAPConst
#check KubertN12APObstructionStatement
```

This is the best-case integration: no new mathematics, just deleting the AP residual from the theorem statement.

## 4. If no immediate upstream use exists: smallest missing interface theorem

If no theorem currently consumes `FourRatSquaresAPConst`, the missing interface is not the AP theorem. It is the curve-to-AP bridge:

> A non-degenerate rational point on the Kubert/E1 curve produces a nonconstant rational four-square arithmetic progression.

Add this as a small interface theorem first. Do not reprove AP descent in `KubertBridgeN12.lean`.

Because I cannot see the exact local definitions of `FourRatSquaresAPConst`, `FourRatSquaresAP`, and “constant,” the following is intentionally written in two layers: first with the local AP predicate names, then as a generic residual wrapper.

### 4.1 Local AP interface statement

Use the local tuple predicate and nonconstant predicate from `N12FourSquaresAP.lean`. The statement should look like this after replacing names:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12FourSquaresAP
-- import the file that defines E1FullCoverCurve / KubertBridgeN12Curve if separate

namespace MazurProof.RationalPointsN12

/--
Smallest missing mathematical interface:
a non-degenerate point on the shifted Kubert/E1 curve gives a nonconstant
rational four-square AP.

Replace `FourRatSquaresAP` and `FourRatSquaresAPNonconstant` by the exact local
predicate names used in `N12FourSquaresAP.lean`.
-/
def KubertN12CurveToNonconstantFourRatSquaresAPStatement : Prop :=
  ∀ {u w : ℚ},
    KubertN12Curve u w →
    KubertN12PointNondegenerate u w →
    ∃ a b c d : ℚ,
      FourRatSquaresAP a b c d ∧
      FourRatSquaresAPNonconstant a b c d

end MazurProof.RationalPointsN12
```

If the AP theorem is stated directly as a constancy theorem rather than through `FourRatSquaresAPNonconstant`, use the negated conclusion instead:

```lean
def KubertN12CurveToNonconstantFourRatSquaresAPStatement : Prop :=
  ∀ {u w : ℚ},
    KubertN12Curve u w →
    KubertN12PointNondegenerate u w →
    ∃ a b c d : ℚ,
      FourRatSquaresAP a b c d ∧
      ¬ FourRatSquaresAPTupleConst a b c d
```

The nondegenerate side condition must exclude exactly the curve points that map to a constant AP. Do **not** guess this as merely `w ≠ 0`: on the shifted E1 curve there are nonzero-`w` special points corresponding to trivial AP data. Make the side condition match the formula in the curve-to-AP map.

A safe provisional side-condition structure is:

```lean
structure KubertN12PointNondegenerate (u w : ℚ) : Prop where
  hw : w ≠ 0
  hu_not_degenerate_1 : u ≠ 0   -- fill from the actual AP map denominators
  hu_not_degenerate_2 : u ≠ 1   -- fill from the actual AP map denominators
  hu_not_degenerate_3 : u ≠ 2   -- fill from the actual AP map denominators
  hu_not_degenerate_4 : u ≠ 4   -- fill from the actual AP map denominators
```

Then remove any fields not used by the actual rational formulas.

### 4.2 Checked contradiction from AP theorem

Once the curve-to-AP interface exists, the use of `fourRatSquaresAPConst_checked` should be one screen.

```lean
namespace MazurProof.RationalPointsN12

/-- No non-degenerate Kubert curve point, assuming the curve-to-AP interface. -/
theorem kubertN12_no_nondegenerate_curve_point_checked
    (hbridge : KubertN12CurveToNonconstantFourRatSquaresAPStatement) :
    ∀ {u w : ℚ},
      KubertN12Curve u w →
      KubertN12PointNondegenerate u w →
      False := by
  intro u w hcurve hnd
  obtain ⟨a, b, c, d, hAP, hnonconst⟩ := hbridge hcurve hnd

  -- Adapt these two lines to the exact shape of `FourRatSquaresAPConst`.
  have hconst := fourRatSquaresAPConst_checked a b c d hAP
  exact hnonconst hconst

end MazurProof.RationalPointsN12
```

If `fourRatSquaresAPConst_checked` has theorem shape

```lean
FourRatSquaresAPConst : Prop
```

rather than a function after unfolding, use:

```lean
  have hAPConst : FourRatSquaresAPConst := fourRatSquaresAPConst_checked
  -- then apply/proj/unfold `FourRatSquaresAPConst` according to its definition
```

For example:

```lean
  unfold FourRatSquaresAPConst at hAPConst
  have hconst := hAPConst a b c d hAP
  exact hnonconst hconst
```

## 5. Bridge from square discriminant to Kubert curve

If `KubertBridgeN12.lean` currently reaches a square-discriminant statement from full-two torsion, the next interface should turn that square into a rational point on the Kubert curve.

The exact formula depends on `A12`, `B12`, and the local discriminant theorem, but the theorem should be isolated like this:

```lean
namespace MazurProof.RationalPointsN12

/--
Small algebra bridge from the checked square-discriminant output for the Kubert
normal form to a point on `w^2 = u^3 - u^2 - 4u + 4`.
-/
def KubertSquareDiscriminantToCurvePointStatement : Prop :=
  ∀ {t : ℚ},
    B12 t ≠ 0 →
    -- Replace by the exact output proposition of
    -- `square_discriminant_of_full_two_torsion_on_shortW (hB := ...)`.
    KubertSquareDiscriminantCondition t →
    ∃ u w : ℚ,
      KubertN12Curve u w ∧
      KubertN12PointNondegenerate u w

end MazurProof.RationalPointsN12
```

Then the fully checked Kubert obstruction assembly is:

```lean
namespace MazurProof.RationalPointsN12

theorem kubertN12_no_full_two_on_normal_form_checked
    (hDiscToCurve : KubertSquareDiscriminantToCurvePointStatement)
    (hCurveToAP : KubertN12CurveToNonconstantFourRatSquaresAPStatement)
    {t : ℚ}
    (hB : B12 t ≠ 0)
    (g : ZMod 2 × ZMod 2 →+
      WeierstrassCurve.Affine.Point (shortW (A12 t) (B12 t)))
    (hg : Function.Injective g) :
    False := by
  have hdisc := square_discriminant_of_full_two_torsion_on_shortW
    (hB := hB) g hg
  obtain ⟨u, w, hcurve, hnd⟩ := hDiscToCurve hB hdisc
  exact kubertN12_no_nondegenerate_curve_point_checked hCurveToAP hcurve hnd

end MazurProof.RationalPointsN12
```

This is the N=12 integration spine:

```text
C12 torsion
  -> full-two torsion on Kubert normal form
  -> square discriminant
  -> rational point on Kubert curve
  -> nonconstant four-square AP
  -> contradiction by fourRatSquaresAPConst_checked
```

Everything after “nonconstant four-square AP” is now checked by `N12FourSquaresAP.lean`.

## 6. Where to place the bridge

If `KubertBridgeN12.lean` already imports `N12FourSquaresAP.lean`, add the checked wrappers there.

If importing `N12FourSquaresAP.lean` into `KubertBridgeN12.lean` would create a cycle, add a new downstream bridge file:

```text
FLT/Assumptions/MazurProof/N12CheckedAPBridge.lean
```

with imports:

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP
import FLT.Assumptions.MazurProof.KubertBridgeN12

namespace MazurProof.RationalPointsN12

-- AP-free wrappers using `fourRatSquaresAPConst_checked` go here.

end MazurProof.RationalPointsN12
```

Then make `RationalPointsN12.lean` import `N12CheckedAPBridge` instead of taking an AP residual as an argument.

## 7. Exact next edit I recommend

Add this first, because it is pure algebra and will be reused regardless of whether the downstream route is AP or full-cover:

```lean
theorem kubertN12Curve_iff_E1_shift (u w : ℚ) :
    KubertN12Curve u w ↔ E1FullCoverCurve (u - 1) w := by
  unfold KubertN12Curve E1FullCoverCurve
  constructor <;> intro h
  · calc
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := h
      _ = (u - 1) * ((u - 1) - 1) * ((u - 1) + 3) := by ring
  · calc
      w ^ 2 = (u - 1) * ((u - 1) - 1) * ((u - 1) + 3) := h
      _ = u ^ 3 - u ^ 2 - 4 * u + 4 := by ring
```

Then search for the first `FourRatSquaresAPConst` argument and close it by:

```lean
exact fourRatSquaresAPConst_checked
```

If no such argument exists, implement the smallest missing interface:

```lean
def KubertN12CurveToNonconstantFourRatSquaresAPStatement : Prop :=
  ∀ {u w : ℚ},
    KubertN12Curve u w →
    KubertN12PointNondegenerate u w →
    ∃ a b c d : ℚ,
      FourRatSquaresAP a b c d ∧
      FourRatSquaresAPNonconstant a b c d
```

That interface is the new mathematical residual. The AP theorem itself is no longer a residual.
