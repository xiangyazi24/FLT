import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartDomain
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Krull dimension of the canonical binary plane chart

The integral `w = 1` chart is covered by the principal open on which the
plane projection is an isomorphism and its finite closed complement.  The
plane coordinate ring is integral over `F₂[z]`, so its principal open has
dimension at most one.  On the complement, the existing monic-tower
certificate makes the quotient finite and hence zero-dimensional.  These
two bounds prove that every nonzero prime of the full chart is maximal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartDimension

open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoPlaneChartLocalization
open RationalPointsN25QuotientTwoPlaneChartBoundary
open RationalPointsN25QuotientTwoPlaneChartDomain
open RationalPointsN25QuotientTwoPlaneFunctionField

private abbrev k := ZMod 2
private abbrev W :=
  RationalPointsN25QuotientTwoAffineChartsSmooth.ChartQuotient 3

/- Keep the boundary quotient on the semiring projection of its canonical
commutative-ring structure. -/
local instance canonicalWChartBoundary_semiring :
    Semiring CanonicalWChartBoundary :=
  (Ideal.Quotient.commRing canonicalWChartBoundaryIdeal).toSemiring

/-- The integral plane model has dimension at most one because it is integral
over the polynomial PID `F₂[z]`. -/
noncomputable instance planeCoordinateRing_dimensionLEOne :
    Ring.DimensionLEOne PlaneCoordinateRing := by
  letI : Module.Finite PlaneZRing PlaneCoordinateRing :=
    planeSexticPolynomial_monic.finite_adjoinRoot
  exact Ring.DimensionLEOne.of_isIntegral PlaneZRing PlaneCoordinateRing

/-- The plane principal open retains dimension at most one. -/
noncomputable instance planeDOpen_dimensionLEOne :
    Ring.DimensionLEOne PlaneDOpen :=
  Ring.DimensionLEOne.localization PlaneDOpen
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      planeProjectionDenominator_ne_zero)

/-- The corresponding principal open of the canonical chart has dimension
at most one by the proved ring equivalence. -/
noncomputable instance canonicalWChartDOpen_dimensionLEOne :
    Ring.DimensionLEOne CanonicalWChartDOpen :=
  Ring.DimensionLEOne.of_ringEquiv
    planeDOpenEquivCanonicalWChartDOpen.symm

/-- The closed projection boundary has finite underlying carrier. -/
theorem canonicalWChartBoundary_finite : Finite CanonicalWChartBoundary := by
  letI : Module.Finite k CanonicalWChartBoundary :=
    canonicalWChartBoundary_moduleFinite
  exact Module.finite_of_finite k

/-- Every maximal ideal of the canonical `w = 1` chart has height at most
one.  If it contains the projection denominator, use the zero-dimensional
finite boundary quotient.  Otherwise localize into the dimension-one plane
principal open. -/
theorem canonicalWChart_maximal_height_le_one
    (m : Ideal W) (hm : m.IsMaximal) :
    (m.height : WithBot ℕ∞) ≤ 1 := by
  letI : m.IsPrime := hm.isPrime
  by_cases hD : canonicalWChartProjectionDenominator ∈ m
  · letI : Module.Finite k CanonicalWChartBoundary :=
      canonicalWChartBoundary_moduleFinite
    letI : Finite CanonicalWChartBoundary := Module.finite_of_finite k
    have h := Ideal.height_le_ringKrullDim_quotient_add_one hD
    have hdim : ringKrullDim CanonicalWChartBoundary ≤ 0 :=
      Ring.krullDimLE_iff.mp
        ((isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp
          (isArtinian_of_finite : IsArtinianRing
            CanonicalWChartBoundary)).2)
    calc
      (m.height : WithBot ℕ∞) ≤
          ringKrullDim CanonicalWChartBoundary + 1 := h
      _ ≤ 0 + 1 := by simpa [add_comm] using add_le_add_right hdim 1
      _ = 1 := zero_add 1
  · have hdisj : Disjoint
        (Submonoid.powers canonicalWChartProjectionDenominator : Set W)
        (m : Set W) := by
      rw [Set.disjoint_left]
      intro x hxS hxm
      rcases hxS with ⟨n, rfl⟩
      exact hD (hm.isPrime.mem_of_pow_mem n hxm)
    let M : Ideal CanonicalWChartDOpen :=
      m.map (algebraMap W CanonicalWChartDOpen)
    have hMprime : M.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers canonicalWChartProjectionDenominator)
        CanonicalWChartDOpen m hm.isPrime hdisj
    letI : M.IsPrime := hMprime
    have hmap : M.height = m.height :=
      IsLocalization.height_map_of_disjoint
        (Submonoid.powers canonicalWChartProjectionDenominator) m hdisj
    have hdim : ringKrullDim CanonicalWChartDOpen ≤ 1 :=
      Ring.krullDimLE_iff.mp
        (Ring.KrullDimLE.mk₁' fun I hI hprime =>
          Ring.DimensionLEOne.maximalOfPrime hI hprime)
    rw [← hmap]
    exact (Ideal.height_le_ringKrullDim_of_ne_top
      (I := M) Ideal.IsPrime.ne_top').trans hdim

/-- The full canonical `w = 1` chart has dimension at most one. -/
noncomputable instance canonicalWChart_dimensionLEOne :
    Ring.DimensionLEOne W := by
  have hkrull : ringKrullDim W ≤ 1 :=
    (ringKrullDim_le_iff_isMaximal_height_le 1).2
      canonicalWChart_maximal_height_le_one
  have hk : Ring.KrullDimLE 1 W := Ring.krullDimLE_iff.mpr hkrull
  exact ⟨fun hp0 hp =>
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hk _ hp0 hp⟩

/-- Every nonzero prime of the canonical plane chart has height exactly
one. -/
theorem canonicalWChart_prime_height_eq_one
    (p : Ideal W) (hp : p.IsPrime) (hp0 : p ≠ ⊥) : p.height = 1 := by
  letI : p.IsPrime := hp
  apply le_antisymm
  · have hupper : (p.height : WithBot ℕ∞) ≤ 1 :=
      (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top').trans
        (Ring.krullDimLE_iff.mp
          (Ring.KrullDimLE.mk₁' fun I hI hprime =>
            Ring.DimensionLEOne.maximalOfPrime hI hprime))
    norm_cast at hupper
  · simpa using Ideal.height_add_one_le_of_lt_of_isPrime (Ne.bot_lt hp0)

end MazurProof.RationalPointsN25QuotientTwoPlaneChartDimension
