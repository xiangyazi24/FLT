# Q2534 non-cyclic N12 checked-descent wiring

## Architecture

Keep `N12FourSquaresAP.lean` as the local descent-to-cover file.  Do **not** import `RationalPointsN12.lean` or `KubertBridgeN12.lean` into it.

```text
N12E1CoverResiduals.lean
  defines FourRatSquaresAPConst and cover wrappers
        ↑
N12FourSquaresAP.lean
  imports N12E1CoverResiduals
  proves PrimitiveCenteredFourSqAPDescent -> FourRatSquaresAPConst
        ↑
new file: N12CheckedDescentBridge.lean
  imports N12FourSquaresAP + RationalPointsN12 (+ KubertBridgeN12 only for torsion wrapper)
```

Use the new bridge file only as a downstream assembly layer.  No lower/root file should import it.

## In `N12FourSquaresAP.lean`

Put only this alias/packaging theorem at the end, if the existing name is too implementation-specific:

```lean
theorem fourRatSquaresAPConst_of_primitiveCenteredFourSqAPDescent_checked
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_checked_descent hdesc
```

## New downstream bridge file

Create `FLT/Assumptions/MazurProof/N12CheckedDescentBridge.lean`.

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP
import FLT.Assumptions.MazurProof.RationalPointsN12

/-!
Checked descent bridge for N=12.
This file is intentionally downstream of both the AP descent file and the rational-points file.
Do not import this file from `N12FourSquaresAP.lean` or `N12E1CoverResiduals.lean`.
-/

/-- Generic adapter: any theorem needing `FourRatSquaresAPConst` can now consume
`PrimitiveCenteredFourSqAPDescent` instead.  This is useful while the exact
RationalPointsN12 wrapper names are being stabilized. -/
theorem of_primitiveCenteredFourSqAPDescent_via_FourRatSquaresAPConst
    {P : Prop}
    (hdesc : PrimitiveCenteredFourSqAPDescent)
    (h : FourRatSquaresAPConst → P) :
    P :=
  h (fourRatSquaresAPConst_of_checked_descent hdesc)
```

Then add the concrete boundary wrapper next to the actual RationalPointsN12 wrapper.  Use the real wrapper name revealed by:

```lean
#check FourRatSquaresAPConst
#check fourRatSquaresAPConst_of_checked_descent
#check no_Z2xZ12_torsion_of_F_boundary
-- also #check the RationalPointsN12 theorem that consumes FourRatSquaresAPConst
```

Expected concrete shape:

```lean
/-- Replace `<N12_boundary_from_cover_wrapper>` and the residual parameters by
whatever `RationalPointsN12.lean` currently exposes. -/
theorem F_N12_boundary_of_primitiveCenteredFourSqAPDescent
    (hdesc : PrimitiveCenteredFourSqAPDescent)
    -- (h₁ : ExistingResidual₁)
    -- ...
    : <F_N12_boundary_prop> := by
  exact <N12_boundary_from_cover_wrapper>
    (fourRatSquaresAPConst_of_checked_descent hdesc)
    -- h₁
    -- ...
```

For the torsion wrapper, import Kubert only in the bridge file or in a second downstream file:

```lean
import FLT.Assumptions.MazurProof.N12FourSquaresAP
import FLT.Assumptions.MazurProof.RationalPointsN12
import FLT.Assumptions.MazurProof.KubertBridgeN12

/-- Final downstream assembly: checked AP descent plus existing N12 boundary
residuals gives the Kubert no-torsion conclusion. -/
theorem no_Z2xZ12_torsion_of_primitiveCenteredFourSqAPDescent
    (hdesc : PrimitiveCenteredFourSqAPDescent)
    -- (h₁ : ExistingBoundaryResidual₁)
    -- ...
    : <no_Z2xZ12_torsion_prop> := by
  exact no_Z2xZ12_torsion_of_F_boundary
    (F_N12_boundary_of_primitiveCenteredFourSqAPDescent
      hdesc
      -- h₁
      -- ...
    )
```

## Recommendation

For now, keep `fourRatSquaresAPConst_of_primitiveCenteredFourSqAPDescent_checked` in `N12FourSquaresAP.lean` and put all `F_N12` boundary / `no_Z2xZ12...` packaging in a new downstream bridge file.  This avoids refactoring active root files and prevents a cycle through `N12E1CoverResiduals -> N12FourSquaresAP -> RationalPointsN12/KubertBridgeN12`.
