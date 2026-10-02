import FLT.Assumptions.MazurProof.N25F_XChartWChartEquiv
import FLT.Assumptions.MazurProof.N25F_XChartFractionMap
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The actual X-boundary local ring is a discrete valuation ring

The explicit X/W chart algebra equivalence transports the established
Dedekind structure from the W chart. The coordinate-rigid map to the W
fraction field proves that `W/X` is nonzero, so the point prime at
`[1:0:0:0]` is nonzero. Localizing this actual Dedekind chart at that
nonzero prime gives the actual boundary local ring its DVR structure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XLocalDVR

open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_XChartWChartEquiv
open N25F_XChartFractionMap

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

/-- The actual X chart inherits Dedekind structure through its explicit
algebra equivalence with the established W chart. -/
instance xChartRing_isDedekindDomain : IsDedekindDomain XChartRing := by
  letI : IsNoetherianRing XChartRing :=
    isNoetherianRing_of_ringEquiv W xChartAlgEquivWChart.symm.toRingEquiv
  letI : Ring.DimensionLEOne XChartRing :=
    Ring.DimensionLEOne.of_ringEquiv xChartAlgEquivWChart.toRingEquiv
  letI : IsIntegrallyClosed XChartRing :=
    IsIntegrallyClosed.of_equiv xChartAlgEquivWChart.symm.toRingEquiv
  exact { }

/-- The actual coordinate `W/X` is nonzero, since its image is `1/(X/W)`
in the W-chart fraction field. No injectivity of the chart map is needed. -/
theorem xW_ne_zero : (xW : XChartRing) ≠ 0 := by
  intro h
  have heq := congrArg xChartToFraction h
  rw [xChartToFraction_xW, map_zero] at heq
  exact (one_div_ne_zero fraction_qx_ne_zero) heq

/-- The boundary coordinate vanishes at the actual X-boundary point. -/
theorem xW_mem_xPrime : xW ∈ xPrime :=
  RingHom.mem_ker.mpr xChartEval_xW

/-- The prime of `[1:0:0:0]` is a nonzero prime of the actual X chart. -/
theorem xPrime_ne_bot : xPrime ≠ ⊥ := by
  intro h
  have hw := xW_mem_xPrime
  rw [h, Ideal.mem_bot] at hw
  exact xW_ne_zero hw

local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime

/-- The actual curve local ring at `[1:0:0:0]` is a DVR. -/
instance xLocalRing_isDiscreteValuationRing : IsDiscreteValuationRing XLocalRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    XChartRing xPrime_ne_bot XLocalRing

/-- The actual germ of `W/X` stays nonzero in the boundary local ring. -/
theorem xWGerm_ne_zero : xWGerm ≠ 0 :=
  (map_ne_zero_iff (algebraMap XChartRing XLocalRing)
    (IsLocalization.injective XLocalRing xPrime.primeCompl_le_nonZeroDivisors)).2
      xW_ne_zero

end MazurProof.N25F_XLocalDVR
