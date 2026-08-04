import FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible
import FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite

/-!
# The affine spread branch for irreducible N13 quadratics

An irreducible quadratic Mumford graph lies in one of the two ordinary
proper charts.  On the affine chart its canonical contraction is finite,
and hence its divisorial hull is invertible.  The only branch left by this
file is the literal integral reciprocal equation on the infinity chart.
-/

open Polynomial

namespace MazurProof.N13IrreducibleQuadraticSpread

noncomputable section

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model

/-- An irreducible quadratic graph already has an invertible affine
divisorial spread unless its reciprocal monic equation is integral on the
infinity chart. -/
theorem divisorialHull_isUnit_or_integral_reciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      (D.u.coeff 0 ≠ 0 ∧
        ∃ a b : R₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹)) := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
        D hdeg hirr with hfinite | hreciprocal
  · exact Or.inl
      (N13FiniteContractIdealInvertible.divisorialHull_graphIdeal_isUnit_of_finite_quadratic
        D.toSemi hdeg hfinite)
  · exact Or.inr hreciprocal

end

end MazurProof.N13IrreducibleQuadraticSpread
