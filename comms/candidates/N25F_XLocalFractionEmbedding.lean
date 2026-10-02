import FLT.Assumptions.MazurProof.N25F_XChartFractionInjective
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal

/-!
# The actual X-boundary local ring inside the W-chart function field

Extend the coordinate-rigid, injective X-chart map by the universal property
of localization at the actual point prime. This records the exact image of
the germ W/X; no valuation or product-formula premise is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XLocalFractionEmbedding

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_XChartFractionMap
open N25F_XChartFractionInjective

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

private theorem xChartToFraction_isUnit_of_primeCompl (s : xPrime.primeCompl) :
    IsUnit (xChartToFraction (s : XChartRing)) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hs : (s : XChartRing) = 0 :=
    xChartToFraction_injective (h.trans (map_zero xChartToFraction).symm)
  exact (Ideal.mem_primeCompl_iff.mp s.2) (hs ▸ xPrime.zero_mem)

/-- The actual X-boundary local ring maps into the common W-chart function field. -/
def xLocalToFraction : XLocalRing →ₐ[ZMod 2] FractionRing W :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := XChartRing) (S := XLocalRing)
    (P := FractionRing W) (f := xChartToFraction)
    xChartToFraction_isUnit_of_primeCompl

@[simp]
theorem xLocalToFraction_algebraMap (a : XChartRing) :
    xLocalToFraction (algebraMap XChartRing XLocalRing a) =
      xChartToFraction a := by
  exact IsLocalization.lift_eq xChartToFraction_isUnit_of_primeCompl a

/-- The coordinate-rigid local-ring map is injective. -/
theorem xLocalToFraction_injective : Function.Injective xLocalToFraction := by
  change Function.Injective
    (IsLocalization.lift (S := XLocalRing)
      (g := xChartToFraction.toRingHom) xChartToFraction_isUnit_of_primeCompl)
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    simpa using congrArg xLocalToFraction h
  · intro h
    exact congrArg (algebraMap XChartRing XLocalRing) (xChartToFraction_injective h)

/-- In the shared field, the actual boundary germ is exactly W/X. -/
@[simp]
theorem xLocalToFraction_xWGerm :
    xLocalToFraction xWGerm = 1 / algebraMap W (FractionRing W) qx := by
  rw [xWGerm, xLocalToFraction_algebraMap, xChartToFraction_xW]

end MazurProof.N25F_XLocalFractionEmbedding
