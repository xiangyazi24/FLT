import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCanonicalDifferentials
import FLT.Mathlib.RingTheory.Kaehler.AlgEquiv

/-!
# Canonical differentials on the actual N25 projective charts

The ordinary affine complete-intersection quotients used for the Jacobian
calculation are isomorphic to the degree-zero homogeneous coordinate rings
of the four standard projective charts.  This file transports the explicit
rank-one Kahler differential modules across those algebra equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCharts

open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoAffineCanonicalDifferentials
open RationalPointsN25QuotientTwoGradedKoszul

/-- The proved ring equivalence from the ordinary affine presentation to an
actual homogeneous chart respects the binary coefficient algebra. -/
def chartCoordinateRingAlgEquivAffine (pivot : Fin 4) :
    ChartQuotient pivot ≃ₐ[k] ChartCoordinateRing pivot where
  toRingEquiv := chartCoordinateRingEquivAffine pivot
  commutes' _ := rfl

/-- The actual relative Kahler differential module on every homogeneous
projective chart is explicitly free of rank one. -/
def chartCoordinateKaehlerDifferentialEquiv (pivot : Fin 4) :
    Ω[ChartCoordinateRing pivot⁄k] ≃ₗ[ChartCoordinateRing pivot]
      ChartCoordinateRing pivot := by
  let e := chartCoordinateRingAlgEquivAffine pivot
  letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI := RingHomInvPair.symm
    (↑e.toRingEquiv : ChartQuotient pivot →+* ChartCoordinateRing pivot)
    (e.toRingEquiv.symm : ChartCoordinateRing pivot →+* ChartQuotient pivot)
  exact (KaehlerDifferential.mapAlgEquiv e).symm.trans
    ((chartKaehlerDifferentialEquiv pivot).trans
      e.toRingEquiv.toSemilinearEquiv)

/-- The transported coordinate functional agrees with the affine Jacobian
residue functional after applying the chart algebra equivalence. -/
theorem chartCoordinateKaehlerDifferentialEquiv_mapAlgEquiv
    (pivot : Fin 4) (x : Ω[ChartQuotient pivot⁄k]) :
    let e := chartCoordinateRingAlgEquivAffine pivot
    letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
    letI := RingHomInvPair.symm
      (↑e.toRingEquiv : ChartQuotient pivot →+* ChartCoordinateRing pivot)
      (e.toRingEquiv.symm : ChartCoordinateRing pivot →+* ChartQuotient pivot)
    chartCoordinateKaehlerDifferentialEquiv pivot
        (KaehlerDifferential.mapAlgEquiv e x) =
      e (chartKaehlerDifferentialEquiv pivot x) := by
  let e := chartCoordinateRingAlgEquivAffine pivot
  letI := RingHomInvPair.of_ringEquiv e.toRingEquiv
  letI := RingHomInvPair.symm
    (↑e.toRingEquiv : ChartQuotient pivot →+* ChartCoordinateRing pivot)
    (e.toRingEquiv.symm : ChartCoordinateRing pivot →+* ChartQuotient pivot)
  change e.toRingEquiv.toSemilinearEquiv
      (chartKaehlerDifferentialEquiv pivot
        ((KaehlerDifferential.mapAlgEquiv e).symm
          (KaehlerDifferential.mapAlgEquiv e x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- A singleton basis of differentials on each actual projective chart. -/
def chartCoordinateKaehlerDifferentialBasis (pivot : Fin 4) :
    Module.Basis Unit (ChartCoordinateRing pivot)
      Ω[ChartCoordinateRing pivot⁄k] :=
  (Module.Basis.singleton Unit (ChartCoordinateRing pivot)).map
    (chartCoordinateKaehlerDifferentialEquiv pivot).symm

/-- Every actual homogeneous projective chart has a free rank-one module of
relative Kahler differentials. -/
theorem chartCoordinateKaehlerDifferential_free (pivot : Fin 4) :
    Module.Free (ChartCoordinateRing pivot)
      Ω[ChartCoordinateRing pivot⁄k] :=
  Module.Free.of_basis (chartCoordinateKaehlerDifferentialBasis pivot)

end MazurProof.RationalPointsN25QuotientTwoCanonicalDifferentialCharts
