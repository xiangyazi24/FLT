import FLT.Assumptions.MazurProof.N25F_ThreeAffineChartJacobian
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Characteristic-three N25 boundary diagnostics

This module provides diagnostic theorems about the characteristic-three N25
boundary structure. It clarifies:

1. The point [1:1:0:1] has W/X = 1, not W/X = 0
2. The curve local ring at a smooth point is a DVR, not Artinian
3. The correct Artinian object for divisor calculations is the quotient
   by the boundary germ
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeBoundaryDiagnostic

open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective

local notation "k₃" => ZMod 3

/-- The characteristic-three incarnation of the canonical cusp
`[1:1:0:1]`. -/
def cuspCThree : NormalizedProjective4 k₃ :=
  .xChart 1 0 1

/-- The point `[1:1:0:1]` lies on the characteristic-three canonical
quadric-cubic. -/
theorem cuspCThree_on_curve :
    IsCanonicalNormalizedThree cuspCThree := by
  norm_num [cuspCThree, IsCanonicalNormalizedThree,
    normalizedCoordinatesThree, canonicalQuadric25Three,
    canonicalCubic25Three]

/-- On the `X=1` chart, the last coordinate is exactly `W/X`, and at
`[1:1:0:1]` it equals one. -/
theorem cuspCThree_w_div_x_eq_one :
    (normalizedCoordinatesThree cuspCThree).w = 1 := by
  rfl

/-- In particular this point is not on the existing `W=0` boundary. -/
theorem cuspCThree_not_w_boundary :
    (normalizedCoordinatesThree cuspCThree).w ≠ 0 := by
  norm_num [cuspCThree, normalizedCoordinatesThree]

/-- A DVR itself cannot be Artinian: an Artinian domain is a field,
whereas a DVR is definitionally required not to be a field. -/
theorem dvr_not_artinian
    (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    ¬ IsArtinianRing R := by
  intro h
  letI : IsArtinianRing R := h
  exact IsDiscreteValuationRing.not_isField R
    (IsArtinianRing.isField_of_isDomain R)

/-- The same quotient has finite length over the original one-dimensional
ring.  This is the exact Mathlib theorem used by `Ring.ord`. -/
theorem quotient_span_singleton_finiteLength
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] {g : R}
    (hg : g ∈ nonZeroDivisors R) :
    IsFiniteLength R (R ⧸ Ideal.span {g}) :=
  isFiniteLength_quotient_span_singleton R hg

end MazurProof.N25F_ThreeBoundaryDiagnostic
