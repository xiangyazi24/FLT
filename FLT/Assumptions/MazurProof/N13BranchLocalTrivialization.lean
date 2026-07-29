import FLT.Assumptions.MazurProof.N13IntegralAffineLattice
import FLT.Assumptions.MazurProof.N13ActualTwistedCech

/-!
# Branch-local trivializations of N13 affine lattices

An invertible affine fractional ideal need not be principal on the affine
chart.  Its restriction to either rational Laurent branch is nevertheless
locally free of rank one.  This file packages that local fact without
promoting the chosen local section to a global generator.

A nonzero section of the finite integral affine lattice has nonzero image in
both faithful branch fields, hence gives a unit in their product.  Multiplying
the standard complete branch lattice by that unit produces the corresponding
rank-one local model.  It is linearly equivalent to the standard lattice, has
full rational branch span, and contains the restricted chosen section.

The remaining arithmetic step is deliberately not hidden here: for a class
in the specialization kernel one must prove that its actual completed affine
module is this local model and that the resulting integral formal-overlap
transition reduces to one.
-/

open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace MazurProof.N13BranchLocalTrivialization

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicBranchLattice.R₂

abbrev Q₂ : Type :=
  N13TwoAdicBranchLattice.Q₂

abbrev RationalLaurent : Type :=
  N13TwoAdicBranchLattice.RationalLaurent

abbrev RationalBranchPair : Type :=
  N13TwoAdicBranchLattice.RationalBranchPair

abbrev CompleteBranches : Type :=
  N13TwoAdicBranchLattice.CompleteBranches

abbrev FunctionField : Type :=
  N13IntegralAffineLattice.FunctionField

abbrev IntegralRing : Type :=
  N13IntegralAffineLattice.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralAffineLattice.RationalRing

abbrev AffineFractionalIdeal : Type :=
  N13IntegralAffineLattice.AffineFractionalIdeal

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralAffineLattice.integralToRational.toAlgebra

local instance functionFieldModule :
    Module IntegralRing FunctionField :=
  Module.compHom FunctionField
    N13IntegralAffineLattice.integralToRational

local instance functionFieldAlgebra :
    Algebra IntegralRing FunctionField :=
  Algebra.compHom FunctionField
    N13IntegralAffineLattice.integralToRational

local instance rationalLaurentAlgebra :
    Algebra R₂ RationalLaurent :=
  HahnSeries.instAlgebra

local instance rationalBranchPairModule :
    Module R₂ RationalBranchPair :=
  Algebra.toModule

/-- Multiplication by a unit of the rational branch pair is an `R₂`-linear
automorphism. -/
def unitMulLinearEquiv
    (u : RationalBranchPairˣ) :
    RationalBranchPair ≃ₗ[R₂] RationalBranchPair where
  toFun z := u.val * z
  invFun z := u.inv * z
  left_inv z := by
    change u.inv * (u.val * z) = z
    rw [← mul_assoc, u.inv_val, one_mul]
  right_inv z := by
    change u.val * (u.inv * z) = z
    rw [← mul_assoc, u.val_inv, one_mul]
  map_add' x y := by
    exact mul_add _ _ _
  map_smul' a z := by
    simp only [Algebra.smul_def]
    ac_rfl

@[simp] theorem unitMulLinearEquiv_apply
    (u : RationalBranchPairˣ)
    (z : RationalBranchPair) :
    unitMulLinearEquiv u z =
      (u : RationalBranchPair) * z :=
  rfl

@[simp] theorem unitMulLinearEquiv_symm_apply
    (u : RationalBranchPairˣ)
    (z : RationalBranchPair) :
    (unitMulLinearEquiv u).symm z =
      u.inv * z :=
  rfl

/-- A branch-local basis consists of a nonzero section of the finite affine
lattice together with the unit represented by its two Laurent expansions.
The section is only a local basis after passing to the branch fields. -/
structure BranchLocalBasis
    (I : AffineFractionalIdealˣ) where
  basisSection : FunctionField
  basisSection_mem :
    basisSection ∈ N13IntegralAffineLattice.integralAffineLattice I
  basisSection_ne_zero : basisSection ≠ 0
  transition : RationalBranchPairˣ
  transition_spec :
    (transition : RationalBranchPair) =
      N13TwoInfinityRestriction.functionFieldToBranches Q₂ basisSection

theorem nonempty_branchLocalBasis
    (I : AffineFractionalIdealˣ) :
    Nonempty (BranchLocalBasis I) := by
  obtain ⟨f, hf, hf0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (N13IntegralAffineLattice.integralAffineLattice_ne_bot I)
  let z : RationalBranchPair :=
    N13TwoInfinityRestriction.functionFieldToBranches Q₂ f
  have hzfst :
      N13Infinity.functionFieldToLaurent Q₂ f ≠ 0 := by
    simpa only [map_zero] using
      (N13Infinity.functionFieldToLaurent_injective Q₂).ne hf0
  have hzsnd :
      N13InfinityMinus.functionFieldToLaurentMinus Q₂ f ≠ 0 := by
    simpa only [map_zero] using
      (N13InfinityMinus.functionFieldToLaurentMinus_injective Q₂).ne hf0
  have hzunit : IsUnit z := by
    rw [Prod.isUnit_iff]
    exact
      ⟨isUnit_iff_ne_zero.mpr hzfst,
        isUnit_iff_ne_zero.mpr hzsnd⟩
  exact
    ⟨⟨f, hf, hf0, hzunit.unit,
      IsUnit.unit_spec hzunit⟩⟩

/-- A fixed branch-local basis.  Different choices give linearly equivalent
local lattices below. -/
def branchLocalBasis
    (I : AffineFractionalIdealˣ) :
    BranchLocalBasis I :=
  Classical.choice (nonempty_branchLocalBasis I)

namespace BranchLocalBasis

variable {I : AffineFractionalIdealˣ}
variable (B : BranchLocalBasis I)

theorem section_mem_fractional :
    B.basisSection ∈ (I : AffineFractionalIdeal) :=
  N13IntegralAffineLattice.mem_fractional_of_mem_integralAffineLattice
    I B.basisSection_mem

theorem restricted_section_ne_zero :
    N13TwoInfinityRestriction.functionFieldToBranches
        Q₂ B.basisSection ≠ 0 := by
  simpa only [map_zero] using
    (N13TwoInfinityRestriction.functionFieldToBranches_injective Q₂).ne
      B.basisSection_ne_zero

theorem transition_ne_zero :
    (B.transition : RationalBranchPair) ≠ 0 :=
  Units.ne_zero B.transition

end BranchLocalBasis

theorem one_mem_completeBranchLattice :
    (1 : RationalBranchPair) ∈
      N13TwoAdicBranchLattice.completeBranchLattice := by
  simpa using
    (N13TwoAdicBranchLattice.completeBranchesToRational_mem
      (1 : CompleteBranches))

/-- The standard complete branch lattice, multiplied by a chosen local
basis of the affine fractional ideal. -/
def localModelLattice
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I) :
    Submodule R₂ RationalBranchPair :=
  N13TwoAdicBranchLattice.completeBranchLattice.map
    (unitMulLinearEquiv B.transition).toLinearMap

@[simp] theorem mem_localModelLattice
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I)
    (z : RationalBranchPair) :
    z ∈ localModelLattice B ↔
      B.transition.inv * z ∈
        N13TwoAdicBranchLattice.completeBranchLattice := by
  change
    z ∈
        N13TwoAdicBranchLattice.completeBranchLattice.map
          (unitMulLinearEquiv B.transition).toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

/-- Multiplication by the chosen local basis identifies the standard
complete lattice with the local model. -/
def standardToLocalModel
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I) :
    N13TwoAdicBranchLattice.completeBranchLattice ≃ₗ[R₂]
      localModelLattice B :=
  (unitMulLinearEquiv B.transition).submoduleMap
    N13TwoAdicBranchLattice.completeBranchLattice

@[simp] theorem standardToLocalModel_apply
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I)
    (z : N13TwoAdicBranchLattice.completeBranchLattice) :
    ((standardToLocalModel B z :
        localModelLattice B) :
      RationalBranchPair) =
        (B.transition : RationalBranchPair) *
          (z : RationalBranchPair) :=
  rfl

/-- The restricted chosen section is the image of the constant standard
basis section, hence belongs to the local model lattice. -/
theorem restricted_section_mem_localModelLattice
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I) :
    N13TwoInfinityRestriction.functionFieldToBranches
        Q₂ B.basisSection ∈
      localModelLattice B := by
  rw [← B.transition_spec]
  refine ⟨1, one_mem_completeBranchLattice, ?_⟩
  simp

/-- Any two local-basis choices produce linearly equivalent local model
lattices.  Thus the construction depends on a trivialization only through
the expected change of basis. -/
def localModelChange
    {I : AffineFractionalIdealˣ}
    (B C : BranchLocalBasis I) :
    localModelLattice B ≃ₗ[R₂] localModelLattice C :=
  (standardToLocalModel B).symm.trans
    (standardToLocalModel C)

/-- Rational scalar span of a branch-local model lattice. -/
def localModelScalarSpan
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I) :
    Submodule RationalBranchPair RationalBranchPair :=
  Submodule.span RationalBranchPair
    (localModelLattice B : Set RationalBranchPair)

/-- Every branch-local model has full rational branchwise scalar span. -/
theorem localModelScalarSpan_eq_top
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I) :
    localModelScalarSpan B = ⊤ := by
  have htransition :
      (B.transition : RationalBranchPair) ∈
        localModelScalarSpan B := by
    apply Submodule.subset_span
    rw [B.transition_spec]
    exact restricted_section_mem_localModelLattice B
  have hone :
      (1 : RationalBranchPair) ∈
        localModelScalarSpan B := by
    have h :=
      (localModelScalarSpan B).smul_mem
        B.transition.inv
        htransition
    change
      B.transition.inv *
          (B.transition : RationalBranchPair) ∈
        localModelScalarSpan B at h
    rw [B.transition.inv_val] at h
    exact h
  apply top_unique
  intro z _
  have h := (localModelScalarSpan B).smul_mem z hone
  simpa using h

/-- The actual complete formal-infinity chart supplies precisely the
standard vectors which are multiplied by the local transition. -/
theorem mem_localModelLattice_iff_exists_infinityChart
    {I : AffineFractionalIdealˣ}
    (B : BranchLocalBasis I)
    (z : RationalBranchPair) :
    z ∈ localModelLattice B ↔
      ∃ w : N13ActualTwistedCech.InfinityCurve,
        z =
          (B.transition : RationalBranchPair) *
            N13ActualTwistedCech.infinityChartToRationalBranches w := by
  constructor
  · intro hz
    rw [mem_localModelLattice] at hz
    obtain ⟨w, hw⟩ :=
      (N13ActualTwistedCech.mem_completeBranchLattice_iff_exists_infinityChart
        (B.transition.inv * z)).1 hz
    refine ⟨w, ?_⟩
    rw [hw]
    rw [← mul_assoc, B.transition.val_inv, one_mul]
  · rintro ⟨w, rfl⟩
    rw [mem_localModelLattice]
    simpa [mul_assoc, B.transition.inv_val] using
      (N13ActualTwistedCech.mem_completeBranchLattice_iff_exists_infinityChart
        (N13ActualTwistedCech.infinityChartToRationalBranches w)).2
        ⟨w, rfl⟩

end

end MazurProof.N13BranchLocalTrivialization
