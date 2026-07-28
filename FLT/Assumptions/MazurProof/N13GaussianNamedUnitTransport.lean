import FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses
import FLT.Assumptions.MazurProof.N13CandidateCollapse

/-!
# Transport of the named N13 units

The unit squareclass computation is carried out in the maximal order of the
Gaussian cubic presentation, while the fake-descent candidates use the sextic
presentation.  This file gives the literal carrier-preserving map between the
two and proves that the three named units agree under it.

Consequently the structural maximal-order unit decomposition transports to the
same three units appearing in `N13CandidateCollapse`, without enumerating the
eight unit squareclasses.
-/

namespace MazurProof.N13GaussianNamedUnitTransport

noncomputable section

abbrev Lg := N13GaussianCubicField.L
abbrev Ls := N13SexticSquareclass.SexticAlgebra

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldLg : Field Lg :=
  AdjoinRoot.instField

abbrev O := NumberField.RingOfIntegers Lg

/-- The maximal-order carrier embedded into its Gaussian cubic fraction
field.  It is written explicitly to avoid choosing between definitionally
different `Algebra O Lg` instances. -/
def orderToGaussian : O →+* Lg :=
  (Subalgebra.val
      (integralClosure N13GaussianGlobalArithmetic.GI Lg)).toRingHom.comp
    N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm.toRingHom

def orderUnitsToGaussian : Oˣ →* Lgˣ :=
  Units.map orderToGaussian.toMonoidHom

/-- Transport maximal-order units through the proved equivalence between the
sextic and Gaussian cubic presentations. -/
def orderUnitsToSextic : Oˣ →* Lsˣ :=
  (Units.map
      N13GaussianFieldEquiv.sexticEquivGaussian.symm.toMonoidHom).comp
    orderUnitsToGaussian

theorem map_relativeTheta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianGlobalReductionTwo.relativeTheta =
      N13GaussianFieldEquiv.gaussianTheta := by
  change
    ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) + 9 =
      N13GaussianCubicField.alpha + 9
  rw [N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]

theorem map_relativeZeta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeZeta =
      N13GaussianFieldEquiv.gaussianI := by
  change
    algebraMap N13GaussianGlobalArithmetic.GI Lg
        N13GaussianGlobalArithmetic.i =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply
      N13GaussianGlobalArithmetic.GI
      N13GaussianCubicField.K Lg]

theorem orderUnitsToGaussian_zeta_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.zetaUnit : O) =
      N13GaussianFieldEquiv.gaussianI := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeZeta) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply]
  exact map_relativeZeta

theorem orderUnitsToGaussian_e1_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e1Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE1) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e1]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE1 =
      1 - N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (N13GaussianFieldEquiv.gaussianI - 1) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE1,
    map_add, map_sub, map_pow, map_mul, map_one,
    map_relativeTheta, map_relativeZeta]

theorem orderUnitsToGaussian_e2_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e2Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE2) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e2]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE2 =
      1 + N13GaussianFieldEquiv.gaussianI *
          N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (1 + 2 * N13GaussianFieldEquiv.gaussianI) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE2,
    map_add, map_mul, map_pow, map_one, map_ofNat,
    map_relativeTheta, map_relativeZeta]

@[simp] theorem orderUnitsToSextic_zeta :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.zetaUnit =
      N13CandidateCollapse.zetaUnit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.zetaUnit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.zeta
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_zeta]
  exact orderUnitsToGaussian_zeta_val

@[simp] theorem orderUnitsToSextic_e1 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e1Unit =
      N13CandidateCollapse.e1Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e1Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e1_val

@[simp] theorem orderUnitsToSextic_e2 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e2Unit =
      N13CandidateCollapse.e2Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e2Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e2_val

/-- Every maximal-order unit becomes the same named binary word used by the
sextic candidate calculation, times a square. -/
theorem orderUnitsToSextic_decompose_named (ε : Oˣ) :
    ∃ i j k : ZMod 2, ∃ η : Lsˣ,
      orderUnitsToSextic ε =
        N13CandidateCollapse.zetaUnit ^ i.val *
          N13CandidateCollapse.e1Unit ^ j.val *
          N13CandidateCollapse.e2Unit ^ k.val * η ^ 2 := by
  obtain ⟨i, j, k, η, hη⟩ :=
    N13GaussianNamedUnitSquareclasses.unit_modSq_decompose_named ε
  refine ⟨i, j, k, orderUnitsToSextic η, ?_⟩
  simpa only [map_mul, map_pow, orderUnitsToSextic_zeta,
    orderUnitsToSextic_e1, orderUnitsToSextic_e2] using
    congrArg (fun u : Oˣ => orderUnitsToSextic u) hη

end

end MazurProof.N13GaussianNamedUnitTransport
