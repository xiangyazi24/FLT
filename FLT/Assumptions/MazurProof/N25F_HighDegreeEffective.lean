import FLT.Assumptions.MazurProof.N25F_CoarseLowerBound
import FLT.Assumptions.MazurProof.N25F_SectionClassFiber
import Mathlib.LinearAlgebra.Dimension.Finite
import Lean.Elab.Tactic.Omega

/-!
# High-degree effective representatives on the actual N25 curve over F2

SOURCE-ONLY CANDIDATE: the complete actual-geometry dependency closure and
this module have NOT been compiled or kernel audited.

The constant is the existing divisor-independent
`wPolynomialBasisPoleBound25Two`; no numerical value is assumed for it.
Every divisor and section below uses the existing full closed-point carrier.
No generic Riemann--Roch or effectiveness premise is added.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_HighDegreeEffective

open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace
open N25F_WBasisPoleBound N25F_CoarseLowerBound
open N25F_SectionFiniteness N25F_FullPicardDegree N25F_SectionClassFiber

/-- The existing coarse lower bound forces positive section dimension above
the fixed threshold, for every actual signed projective divisor. -/
theorem finrank_pos_of_degree_gt_four_basis_bound
    (D : ProjectiveDivisor25Two)
    (hD : 4 * (wPolynomialBasisPoleBound25Two : ℤ) <
      fullClosedPointGrading25Two.divisorDegree D) :
    0 < Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) := by
  have hbound := degree_le_finrank_add_four_basis_bound D
  omega

/-- Above the fixed threshold there is an actual nonzero bounded-pole
function. Finiteness is supplied by the existing geometric instance. -/
theorem nonzeroSection_nonempty_of_degree_gt_four_basis_bound
    (D : ProjectiveDivisor25Two)
    (hD : 4 * (wPolynomialBasisPoleBound25Two : ℤ) <
      fullClosedPointGrading25Two.divisorDegree D) :
    Nonempty (NonzeroSection25Two D) := by
  obtain ⟨f, hf⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero
      (R := ZMod 2) (M := fullRiemannRochSpace25Two D)).mp
      (finrank_pos_of_degree_gt_four_basis_bound D hD)
  exact ⟨⟨f, hf⟩⟩

/-- Equivalent submodule formulation of nonvanishing: the full actual
Riemann--Roch space is not the zero submodule. -/
theorem riemannRochSpace_ne_bot_of_degree_gt_four_basis_bound
    (D : ProjectiveDivisor25Two)
    (hD : 4 * (wPolynomialBasisPoleBound25Two : ℤ) <
      fullClosedPointGrading25Two.divisorDegree D) :
    fullRiemannRochSpace25Two D ≠ ⊥ := by
  intro hzero
  have hpos := finrank_pos_of_degree_gt_four_basis_bound D hD
  rw [hzero, finrank_bot] at hpos
  exact (Nat.lt_irrefl 0) hpos

/-- Every full projective divisor above the fixed threshold is linearly
equivalent to an effective divisor of its exact degree. The class equality
is in the existing quotient by divisors of actual nonzero curve functions. -/
theorem exists_effective_representative_of_degree_gt_four_basis_bound
    (D : ProjectiveDivisor25Two)
    (hD : 4 * (wPolynomialBasisPoleBound25Two : ℤ) <
      fullClosedPointGrading25Two.divisorDegree D) :
    ∃ E : fullClosedPointGrading25Two.EffDivOfDegree
        (fullClosedPointGrading25Two.divisorDegree D).toNat,
      fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
        (fullClosedPointGrading25Two.effectiveToDivisor E.1) =
      fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D := by
  obtain ⟨f⟩ := nonzeroSection_nonempty_of_degree_gt_four_basis_bound D hD
  exact ⟨(nonzeroSectionToFullClassFiber25Two D f).1,
    (nonzeroSectionToFullClassFiber25Two D f).2⟩

end MazurProof.N25F_HighDegreeEffective
