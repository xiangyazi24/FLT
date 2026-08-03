import FLT.Assumptions.MazurProof.N13RepeatedRootSpread

/-!
# The structural dichotomy for quadratic N13 graphs

A monic quadratic over `ℚ₂` is either irreducible or a product of two
linear factors.  Distinct factors are handled by the secant spread and a
repeated factor by the tangent spread.  Thus two-adic irreducibility is
the only remaining degree-two obstruction.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13QuadraticSpreadDichotomy

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  N13AllPointAffineSpread.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13AllPointAffineSpread.Model

abbrev IntegralRing : Type :=
  N13AllPointAffineSpread.IntegralRing

abbrev IntegralFractionalIdeal : Type :=
  N13AllPointAffineSpread.IntegralFractionalIdeal

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- A balanced quadratic Mumford graph either has an invertible integral
affine spread or its horizontal polynomial is irreducible over `ℚ₂`. -/
theorem mumfordGraph_has_affineSpread_or_irreducible
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    (∃ J : Ideal IntegralRing,
        IsUnit (J : IntegralFractionalIdeal) ∧
          Ideal.map
              N13TwoAdicCoordinateBaseChange.integralToSextic J =
            SexticMumford.mumfordIdeal Model D.u D.v) ∨
      Irreducible D.u := by
  by_cases hirr : Irreducible D.u
  · exact Or.inr hirr
  left
  obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
    (D.u_monic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp
      hirr
  let x₁ : Q₂ := -c₁
  let x₂ : Q₂ := -c₂
  have hfactor :
      D.u = (X - C x₁) * (X - C x₂) := by
    have hc₂ : D.u.coeff 2 = 1 := by
      calc
        D.u.coeff 2 = D.u.coeff D.u.natDegree :=
          congrArg D.u.coeff hdeg.symm
        _ = 1 := D.u_monic.coeff_natDegree
    simp only [x₁, x₂, C_neg, sub_neg_eq_add]
    rw [D.u.as_sum_range_C_mul_X_pow, hdeg,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc₂, hc₀, hc₁, C_mul, C_add, C_1]
    ring
  by_cases hneq : x₁ ≠ x₂
  · exact
      N13AllPointAffineSpread.mumfordGraph_has_affineSpread_of_distinct_split
        D x₁ x₂ hfactor hneq
  · have heq : x₂ = x₁ := by
      apply not_ne_iff.mp
      exact fun h ↦ hneq h.symm
    have hfactorSquare :
        D.u = (X - C x₁) ^ 2 := by
      rw [heq] at hfactor
      simpa only [pow_two] using hfactor
    exact
      N13RepeatedRootSpread.mumfordGraph_has_affineSpread_of_repeated_root
        D x₁ hfactorSquare

/-- The Padé-selected quadratic graph therefore has an invertible affine
spread unless its normalized horizontal polynomial is genuinely
irreducible over `ℚ₂`. -/
theorem selectedGraph_has_affineSpread_or_irreducible
    (P : G)
    (hdeg :
      (N13ConstructedHalfIntegralSpread.graphU P).natDegree = 2) :
    (∃ J : Ideal IntegralRing,
        IsUnit (J : IntegralFractionalIdeal) ∧
          Ideal.map
              N13TwoAdicCoordinateBaseChange.integralToSextic J =
            SexticMumford.mumfordIdeal Model
              (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
                P).u
              (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
                P).v) ∨
      Irreducible
        (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
          P).u := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  have hDdeg : D.u.natDegree = 2 := by
    change
      ((N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u.map N13InfinityBaseChange.ratToQ₂).natDegree = 2
    rw [
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford
        P).u_monic.natDegree_map]
    exact
      (N13DegreeOneGraphPoint.normalizedGraphMumford_u_natDegree P).trans
        hdeg
  simpa [D] using
    (mumfordGraph_has_affineSpread_or_irreducible D hDdeg)

end

end MazurProof.N13QuadraticSpreadDichotomy
