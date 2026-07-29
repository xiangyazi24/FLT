import FLT.Assumptions.MazurProof.N13TwoAdicBranchLattice

/-!
# Integral affine lattices for N13 fractional ideals

An invertible affine fractional ideal on the generic fibre need not admit a
global generator.  Instead, choose a finite generating family over the
rational affine coordinate ring and take its span over the integral model.
The resulting finite integral lattice lies in the fractional ideal and
recovers it after rational scalar extension.

Restriction of this lattice to the two rational branches still has full
branchwise scalar span.  The proof uses a nonzero lattice section only
locally: its two faithful Laurent expansions are units in the product of the
branch fields.  No global generator of the fractional ideal is selected.
-/

open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13IntegralAffineLattice

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicAffineRestrictionCompatibility.R₂

abbrev Q₂ : Type :=
  N13TwoAdicAffineRestrictionCompatibility.Q₂

abbrev IntegralRing : Type :=
  N13TwoAdicCoordinateBaseChange.IntegralRing

abbrev RationalRing : Type :=
  N13Mumford.CoordinateRing Q₂

abbrev FunctionField : Type :=
  N13Mumford.FunctionField Q₂

abbrev RationalBranchPair : Type :=
  N13TwoAdicBranchLattice.RationalBranchPair

abbrev AffineFractionalIdeal : Type :=
  N13TwoInfinityRestriction.AffineFractionalIdeal Q₂

/-- The integral affine model maps to the rational sextic coordinate ring. -/
def integralToRational :
    IntegralRing →+* RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic

local instance rationalAlgebra :
    Algebra IntegralRing RationalRing :=
  integralToRational.toAlgebra

local instance functionFieldModule :
    Module IntegralRing FunctionField :=
  Module.compHom FunctionField integralToRational

local instance functionFieldAlgebra :
    Algebra IntegralRing FunctionField :=
  Algebra.compHom FunctionField integralToRational

/-- Restriction of an integral affine function to the two rational branches. -/
def integralToBranches :
    IntegralRing →+* RationalBranchPair :=
  (N13TwoInfinityRestriction.coordinateToBranches Q₂).comp
    integralToRational

local instance rationalBranchPairRationalAlgebra :
    Algebra RationalRing RationalBranchPair :=
  (N13TwoInfinityRestriction.coordinateToBranches Q₂).toAlgebra

local instance rationalBranchesModule :
    Module IntegralRing RationalBranchPair :=
  Module.compHom RationalBranchPair integralToRational

local instance rationalBranchesAlgebra :
    Algebra IntegralRing RationalBranchPair :=
  Algebra.compHom RationalBranchPair integralToRational

/-- Rational function restriction, regarded as a map over the integral
affine coordinate ring. -/
def functionToBranchesAlgHom :
    FunctionField →ₐ[IntegralRing] RationalBranchPair where
  __ := N13TwoInfinityRestriction.functionFieldToBranches Q₂
  commutes' a := by
    change
      N13TwoInfinityRestriction.functionFieldToBranches Q₂
          (algebraMap RationalRing FunctionField
            (integralToRational a)) =
        N13TwoInfinityRestriction.coordinateToBranches Q₂
          (integralToRational a)
    exact
      N13TwoInfinityRestriction.functionFieldToBranches_algebraMap
        Q₂ (integralToRational a)

/-- A finite rational generating family for an invertible affine fractional
ideal.  This is finite projectivity data, not a global generator. -/
structure GeneratorFamily
    (I : AffineFractionalIdealˣ) where
  n : ℕ
  generator : Fin n → FunctionField
  span_eq :
    Submodule.span RationalRing (Set.range generator) =
      ((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField)

theorem nonempty_generatorFamily
    (I : AffineFractionalIdealˣ) :
    Nonempty (GeneratorFamily I) := by
  have hfg :
      (((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField)).FG :=
    FractionalIdeal.fg_unit I
  obtain ⟨n, generator, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  exact ⟨⟨n, generator, hspan⟩⟩

/-- A fixed finite generating family, used only to package the lattice. -/
def generatorFamily
    (I : AffineFractionalIdealˣ) :
    GeneratorFamily I :=
  Classical.choice (nonempty_generatorFamily I)

/-- The finite integral affine lattice spanned by a rational generating
family of the fractional ideal. -/
def integralAffineLattice
    (I : AffineFractionalIdealˣ) :
    Submodule IntegralRing FunctionField :=
  Submodule.span IntegralRing
    (Set.range (generatorFamily I).generator)

theorem generator_mem_fractional
    (I : AffineFractionalIdealˣ)
    (i : Fin (generatorFamily I).n) :
    (generatorFamily I).generator i ∈
      (I : AffineFractionalIdeal) := by
  have hmem :
      (generatorFamily I).generator i ∈
        Submodule.span RationalRing
          (Set.range (generatorFamily I).generator) :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [(generatorFamily I).span_eq] at hmem
  exact hmem

/-- The integral lattice is genuinely a submodule of the original rational
fractional ideal. -/
theorem mem_fractional_of_mem_integralAffineLattice
    (I : AffineFractionalIdealˣ)
    {f : FunctionField}
    (hf : f ∈ integralAffineLattice I) :
    f ∈ (I : AffineFractionalIdeal) := by
  refine Submodule.span_induction
    (p := fun f _ ↦ f ∈ (I : AffineFractionalIdeal))
    ?_ ?_ ?_ ?_ hf
  · intro f hf
    obtain ⟨i, rfl⟩ := hf
    exact generator_mem_fractional I i
  · exact FractionalIdeal.zero_mem _
  · intro f g _ _ hfI hgI
    exact
      (((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField).add_mem hfI hgI)
  · intro a f _ hfI
    have hsmul :=
      (((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField).smul_mem
          (integralToRational a) hfI)
    exact hsmul

/-- Rational scalar extension of an integral affine lattice. -/
def rationalSpan
    (L : Submodule IntegralRing FunctionField) :
    Submodule RationalRing FunctionField :=
  Submodule.span RationalRing (L : Set FunctionField)

/-- Extending the constructed lattice back to the rational affine ring
recovers the original fractional ideal exactly. -/
theorem rationalSpan_integralAffineLattice
    (I : AffineFractionalIdealˣ) :
    rationalSpan (integralAffineLattice I) =
      ((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    exact mem_fractional_of_mem_integralAffineLattice I hf
  · rw [← (generatorFamily I).span_eq]
    apply Submodule.span_mono
    rintro f ⟨i, rfl⟩
    exact
      Submodule.subset_span
        (Set.mem_range_self i)

theorem integralAffineLattice_fg
    (I : AffineFractionalIdealˣ) :
    (integralAffineLattice I).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem integralAffineLattice_ne_bot
    (I : AffineFractionalIdealˣ) :
    integralAffineLattice I ≠ ⊥ := by
  intro hbot
  have hIbot :
      ((I : AffineFractionalIdeal) :
        Submodule RationalRing FunctionField) = ⊥ := by
    rw [← rationalSpan_integralAffineLattice I, hbot]
    simp [rationalSpan]
  apply I.ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simpa using hIbot

/-- Restriction of the finite integral affine lattice to the two rational
Laurent branches. -/
def restrictedIntegralAffineLattice
    (I : AffineFractionalIdealˣ) :
    Submodule IntegralRing RationalBranchPair :=
  (integralAffineLattice I).map
    functionToBranchesAlgHom.toLinearMap

theorem function_mem_restrictedIntegralAffineLattice
    (I : AffineFractionalIdealˣ)
    {f : FunctionField}
    (hf : f ∈ integralAffineLattice I) :
    N13TwoInfinityRestriction.functionFieldToBranches Q₂ f ∈
      restrictedIntegralAffineLattice I := by
  exact ⟨f, hf, rfl⟩

theorem restrictedIntegralAffineLattice_fg
    (I : AffineFractionalIdealˣ) :
    (restrictedIntegralAffineLattice I).FG :=
  (integralAffineLattice_fg I).map
    functionToBranchesAlgHom.toLinearMap

/-- Scalar span of the restricted integral lattice in the product of the
two rational branch fields. -/
def restrictedScalarSpan
    (I : AffineFractionalIdealˣ) :
    Submodule RationalBranchPair RationalBranchPair :=
  Submodule.span RationalBranchPair
    (restrictedIntegralAffineLattice I :
      Set RationalBranchPair)

/-- The restricted integral affine lattice has full branchwise rational
span.  Thus it is already a lattice in the same rank-one branch module as
the complete formal-infinity lattice. -/
theorem restrictedScalarSpan_eq_top
    (I : AffineFractionalIdealˣ) :
    restrictedScalarSpan I = ⊤ := by
  obtain ⟨f, hf, hf0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (integralAffineLattice_ne_bot I)
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
  let unit : RationalBranchPairˣ := hzunit.unit
  have hunit :
      (unit : RationalBranchPair) = z :=
    IsUnit.unit_spec hzunit
  have hzmem :
      z ∈ restrictedScalarSpan I := by
    apply Submodule.subset_span
    exact function_mem_restrictedIntegralAffineLattice I hf
  have hone :
      (1 : RationalBranchPair) ∈ restrictedScalarSpan I := by
    have h :=
      (restrictedScalarSpan I).smul_mem
        (↑(unit⁻¹) : RationalBranchPair) hzmem
    change
      (↑(unit⁻¹) : RationalBranchPair) * z ∈
        restrictedScalarSpan I at h
    rw [← hunit, Units.inv_mul] at h
    exact h
  apply top_unique
  intro x _
  have h := (restrictedScalarSpan I).smul_mem x hone
  simpa using h

end

end MazurProof.N13IntegralAffineLattice
