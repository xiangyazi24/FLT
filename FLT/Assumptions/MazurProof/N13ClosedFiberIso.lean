import FLT.Assumptions.MazurProof.N13ClosedFiberGlueIso

/-!
# The actual N13 closed fibre

Mathlib constructs a pullback from an open cover by first gluing the
chartwise pullbacks.  The resulting glued scheme satisfies the pullback
universal property.  Combining its canonical uniqueness isomorphism
with the explicit gluing comparison identifies the actual closed fibre
of the integral N13 model with the characteristic-two special fibre.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberIso

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

private abbrev P :=
  Scheme.Pullback.gluing
    D.openCover
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

/-- The actual closed fibre of the integral two-chart N13 model. -/
abbrev ClosedFiber : Scheme :=
  pullback
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

/-- The canonical pullback uniqueness isomorphism from the actual
closed fibre to Mathlib's chartwise glued pullback. -/
def closedFiberToGluedIso :
    ClosedFiber ≅ P.glued :=
  limit.isoLimitCone
    ⟨_,
      Scheme.Pullback.gluedIsLimit
        D.openCover
        N13IntegralCurveScheme.toBase
        N13ClosedFiberCharts.closedBaseMap⟩

/-- The actual closed fibre is the explicit integral
characteristic-two N13 special fibre. -/
def closedFiberIso :
    ClosedFiber ≅ N13SpecialFibreScheme.SpecialFibre :=
  closedFiberToGluedIso ≪≫
    N13ClosedFiberGlueIso.gluedIso

/-- The actual closed fibre of the integral N13 model is integral. -/
instance closedFiber_isIntegral :
    IsIntegral ClosedFiber :=
  IsIntegral.of_isIso closedFiberIso.inv

end MazurProof.N13ClosedFiberIso
