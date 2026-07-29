import FLT.Assumptions.MazurProof.N13TwoAdicAffineRestrictionCompatibility

/-!
# The complete integral lattice in the two N13 infinity branches

Restriction to the two rational Laurent branches locally trivializes every
nonzero affine fractional ideal: any nonzero section is a unit in the product
of the two branch fields.  This argument uses the section only to prove local
generation and does not choose a global generator for the ideal.

The two integral power-series branches embed coefficientwise into this common
rational branch pair.  Their image is the complete integral lattice that will
enter the formal Čech comparison.
-/

open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace MazurProof.N13TwoAdicBranchLattice

noncomputable section

universe u

section RationalBranches

variable (K : Type u) [Field K] [CharZero K]

abbrev CoordinateRing : Type u :=
  N13Mumford.CoordinateRing K

abbrev FunctionField : Type u :=
  N13Mumford.FunctionField K

abbrev RationalBranches : Type u :=
  LaurentSeries K × LaurentSeries K

abbrev AffineFractionalIdeal : Type u :=
  N13TwoInfinityRestriction.AffineFractionalIdeal K

/-- Scalar span of the restriction of an affine fractional ideal inside the
product of the two branch fields. -/
def branchScalarSpan
    (I : AffineFractionalIdeal K) :
    Submodule (RationalBranches K) (RationalBranches K) :=
  Submodule.span (RationalBranches K)
    (N13TwoInfinityRestriction.restrictFractionalIdeal K I :
      Set (RationalBranches K))

theorem function_mem_branchScalarSpan
    (I : AffineFractionalIdeal K)
    {f : FunctionField K} (hf : f ∈ I) :
    N13TwoInfinityRestriction.functionFieldToBranches K f ∈
      branchScalarSpan K I := by
  apply Submodule.subset_span
  exact
    (N13TwoInfinityRestriction.mem_restrictFractionalIdeal K I _).2
      ⟨f, hf, rfl⟩

/-- Every nonzero affine fractional ideal becomes the unit rank-one module
after simultaneous scalar extension to the two Laurent fields. -/
theorem branchScalarSpan_eq_top
    (I : AffineFractionalIdeal K) (hI : I ≠ 0) :
    branchScalarSpan K I = ⊤ := by
  obtain ⟨f, hf, hf0⟩ : ∃ f ∈ I, f ≠ 0 := by
    simpa [ne_eq, FractionalIdeal.eq_zero_iff] using hI
  let z : RationalBranches K :=
    N13TwoInfinityRestriction.functionFieldToBranches K f
  have hzfst :
      N13Infinity.functionFieldToLaurent K f ≠ 0 := by
    simpa only [map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne hf0
  have hzsnd :
      N13InfinityMinus.functionFieldToLaurentMinus K f ≠ 0 := by
    simpa only [map_zero] using
      (N13InfinityMinus.functionFieldToLaurentMinus_injective K).ne hf0
  have hzunit : IsUnit z := by
    rw [Prod.isUnit_iff]
    exact
      ⟨isUnit_iff_ne_zero.mpr hzfst,
        isUnit_iff_ne_zero.mpr hzsnd⟩
  let unit : (RationalBranches K)ˣ := hzunit.unit
  have hunit :
      (unit : RationalBranches K) = z :=
    IsUnit.unit_spec hzunit
  have hzmem : z ∈ branchScalarSpan K I :=
    function_mem_branchScalarSpan K I hf
  have hone :
      (1 : RationalBranches K) ∈ branchScalarSpan K I := by
    have h :=
      (branchScalarSpan K I).smul_mem
        (↑(unit⁻¹) : RationalBranches K) hzmem
    change
      (↑(unit⁻¹) : RationalBranches K) * z ∈
        branchScalarSpan K I at h
    rw [← hunit, Units.inv_mul] at h
    exact h
  apply top_unique
  intro x _
  have h := (branchScalarSpan K I).smul_mem x hone
  simpa using h

theorem branchScalarSpan_unit_eq_top
    (I : (AffineFractionalIdeal K)ˣ) :
    branchScalarSpan K (I : AffineFractionalIdeal K) = ⊤ :=
  branchScalarSpan_eq_top K I I.ne_zero

end RationalBranches

section IntegralLattice

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicAffineRestrictionCompatibility.R₂

abbrev Q₂ : Type :=
  N13TwoAdicAffineRestrictionCompatibility.Q₂

abbrev IntegralPower : Type :=
  PowerSeries R₂

abbrev IntegralLaurent : Type :=
  LaurentSeries R₂

abbrev RationalLaurent : Type :=
  LaurentSeries Q₂

abbrev CompleteBranches : Type :=
  IntegralPower × IntegralPower

abbrev IntegralOverlapBranches : Type :=
  IntegralLaurent × IntegralLaurent

abbrev RationalBranchPair : Type :=
  RationalLaurent × RationalLaurent

local instance rationalLaurentAlgebra :
    Algebra R₂ RationalLaurent :=
  HahnSeries.instAlgebra

/-- Include an integral power series into a rational Laurent series by
coefficient extension, as an `R₂`-algebra map. -/
def powerToRationalLaurentAlgHom :
    IntegralPower →ₐ[R₂] RationalLaurent :=
  (HahnSeries.ofPowerSeriesAlg ℤ R₂).comp
    (PowerSeries.mapAlgHom (Algebra.ofId R₂ Q₂))

def powerToRationalLaurent :
    IntegralPower →+* RationalLaurent :=
  powerToRationalLaurentAlgHom.toRingHom

@[simp] theorem powerToRationalLaurent_apply
    (f : IntegralPower) :
    powerToRationalLaurent f =
      (HahnSeries.ofPowerSeries ℤ Q₂)
        (N13TwoAdicInfinityCompatibility.powerMap f) := by
  unfold powerToRationalLaurent
    powerToRationalLaurentAlgHom
  change
    (HahnSeries.ofPowerSeries ℤ Q₂)
        (PowerSeries.mapAlgHom
          (Algebra.ofId R₂ Q₂) f) =
      (HahnSeries.ofPowerSeries ℤ Q₂)
        (N13TwoAdicInfinityCompatibility.powerMap f)
  rw [PowerSeries.mapAlgHom_apply]
  rfl

theorem powerToRationalLaurent_injective :
    Function.Injective powerToRationalLaurent := by
  intro f g h
  rw [powerToRationalLaurent_apply,
    powerToRationalLaurent_apply] at h
  apply N13TwoAdicInfinityCompatibility.powerMap_injective
  exact
    (HahnSeries.ofPowerSeries_injective
      (Γ := ℤ) (R := Q₂)) h

/-- Coefficientwise embedding of the two complete integral branches into the
two rational Laurent branch fields, as an `R₂`-algebra map. -/
def completeBranchesToRationalAlgHom :
    CompleteBranches →ₐ[R₂] RationalBranchPair :=
  ((powerToRationalLaurentAlgHom).comp
      (AlgHom.fst R₂ IntegralPower IntegralPower)).prod
    ((powerToRationalLaurentAlgHom).comp
      (AlgHom.snd R₂ IntegralPower IntegralPower))

def completeBranchesToRational :
    CompleteBranches →+* RationalBranchPair :=
  completeBranchesToRationalAlgHom.toRingHom

@[simp] theorem completeBranchesToRational_apply
    (z : CompleteBranches) :
    completeBranchesToRational z =
      (powerToRationalLaurent z.1,
        powerToRationalLaurent z.2) :=
  rfl

theorem completeBranchesToRational_injective :
    Function.Injective completeBranchesToRational := by
  intro z w h
  apply Prod.ext
  · apply powerToRationalLaurent_injective
    exact congrArg Prod.fst h
  · apply powerToRationalLaurent_injective
    exact congrArg Prod.snd h

/-- The complete-branch embedding is the restriction-to-overlap embedding
followed by coefficient extension. -/
theorem completeBranchesToRational_eq_rationalizeFormal
    (z : CompleteBranches) :
    completeBranchesToRational z =
      N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
        (N13FormalOverlapSplit.includePowerBranches z) := by
  apply Prod.ext
  · change
      powerToRationalLaurent z.1 =
        N13TwoAdicInfinityCompatibility.laurentMap
          (N13FormalInfinityChart.includePowerRing z.1)
    rw [powerToRationalLaurent_apply]
    exact
      (N13TwoAdicInfinityCompatibility.laurentMap_includePower
        z.1).symm
  · change
      powerToRationalLaurent z.2 =
        N13TwoAdicInfinityCompatibility.laurentMap
          (N13FormalInfinityChart.includePowerRing z.2)
    rw [powerToRationalLaurent_apply]
    exact
      (N13TwoAdicInfinityCompatibility.laurentMap_includePower
        z.2).symm

local instance rationalBranchPairModule :
    Module R₂ RationalBranchPair :=
  Algebra.toModule

/-- The integral complete branches, viewed as an `R₂`-linear submodule of
the rational branch pair. -/
def completeBranchLattice :
    Submodule R₂ RationalBranchPair :=
  completeBranchesToRationalAlgHom.range.toSubmodule

@[simp] theorem mem_completeBranchLattice
    (z : RationalBranchPair) :
    z ∈ completeBranchLattice ↔
      ∃ p : CompleteBranches,
        completeBranchesToRational p = z := by
  change
    z ∈ completeBranchesToRationalAlgHom.range ↔
      ∃ p : CompleteBranches,
        completeBranchesToRationalAlgHom p = z
  exact AlgHom.mem_range completeBranchesToRationalAlgHom

theorem completeBranchesToRational_mem
    (z : CompleteBranches) :
    completeBranchesToRational z ∈ completeBranchLattice :=
  (AlgHom.mem_range completeBranchesToRationalAlgHom).2
    ⟨z, rfl⟩

/-- The complete integral lattice lies in the scalar extension of every
invertible affine fractional ideal. -/
theorem completeBranchLattice_subset_branchScalarSpan
    (I :
      (N13TwoInfinityRestriction.AffineFractionalIdeal Q₂)ˣ)
    {z : RationalBranchPair}
    (_hz : z ∈ completeBranchLattice) :
    z ∈
      branchScalarSpan Q₂
        (I :
          N13TwoInfinityRestriction.AffineFractionalIdeal Q₂) := by
  rw [branchScalarSpan_unit_eq_top]
  trivial

end IntegralLattice

end

end MazurProof.N13TwoAdicBranchLattice
