import FLT.Assumptions.MazurProof.N13ActualCechComplex
import FLT.Assumptions.MazurProof.N13TwoAdicBranchLattice

/-!
# The actual N13 Čech complex after the fixed base-divisor twist

The selected divisor `(0,0)+(-1,0)` is supported on the affine chart.
Consequently its twist does not alter the complete lattice at infinity:
it enlarges the affine source by the two genuine principal parts already
constructed in `N13IntegralFormalCech`.

This file first identifies the actual complete formal-infinity chart with
the complete integral branch lattice inside the rational branch pair.  It
then combines the genuine two-chart coboundary with the two base-divisor
principal parts.  For every overlap transition reducing to one, the
resulting extended coboundary is surjective.  The proof uses the structural
rank-two obstruction quotient and its integral connecting isomorphism; it
does not choose a generator on the affine chart.
-/

namespace MazurProof.N13ActualTwistedCech

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13ActualCechComplex.R₂

abbrev Q₂ : Type :=
  N13TwoAdicBranchLattice.Q₂

abbrev Overlap : Type :=
  N13ActualCechComplex.Overlap

abbrev IntegralAffineRing : Type :=
  N13ActualCechComplex.IntegralAffineRing

abbrev InfinityCurve : Type :=
  N13ActualCechComplex.InfinityCurve

abbrev CompleteBranches : Type :=
  N13TwoAdicBranchLattice.CompleteBranches

abbrev RationalBranchPair : Type :=
  N13TwoAdicBranchLattice.RationalBranchPair

abbrev PrincipalParts : Type :=
  N13IntegralFormalCech.PrincipalParts

abbrev Obstruction : Type :=
  N13ActualCechComplex.Obstruction

abbrev NearIdentityTransition : Type :=
  N13FormalLineBundleCech.NearIdentityTransition

/-! ## The actual complete chart realizes the integral branch lattice -/

/-- Restrict an actual complete-chart function to its two Hensel branches
and then extend coefficients to the rational Laurent branch fields. -/
def infinityChartToRationalBranches :
    InfinityCurve →+* RationalBranchPair :=
  N13TwoAdicBranchLattice.completeBranchesToRational.comp
    N13FormalInfinitySplit.branchEval

theorem infinityChartToRationalBranches_injective :
    Function.Injective infinityChartToRationalBranches :=
  N13TwoAdicBranchLattice.completeBranchesToRational_injective.comp
    N13FormalInfinitySplit.branchEval_injective

/-- The rational image of the actual complete formal-infinity chart is
exactly the complete integral branch lattice. -/
theorem mem_completeBranchLattice_iff_exists_infinityChart
    (z : RationalBranchPair) :
    z ∈ N13TwoAdicBranchLattice.completeBranchLattice ↔
      ∃ w : InfinityCurve,
        infinityChartToRationalBranches w = z := by
  rw [N13TwoAdicBranchLattice.mem_completeBranchLattice]
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨w, hw⟩ :=
      N13FormalInfinitySplit.branchEval_surjective p
    exact ⟨w, by simp [infinityChartToRationalBranches, hw]⟩
  · rintro ⟨w, rfl⟩
    exact
      ⟨N13FormalInfinitySplit.branchEval w, rfl⟩

/-- The actual complete-chart embedding agrees with restriction to the
punctured formal overlap followed by branch splitting and coefficient
extension. -/
theorem infinityChartToRationalBranches_eq_rationalizeOverlap
    (w : InfinityCurve) :
    infinityChartToRationalBranches w =
      N13TwoAdicAffineRestrictionCompatibility.laurentPairMap
        (N13FormalOverlapSplit.formalBranchEval
          (N13FormalInfinityChart.infinityToFormalCurve w)) := by
  rw [N13FormalOverlapSplit.formalBranchEval_infinityToFormalCurve]
  exact
    N13TwoAdicBranchLattice.completeBranchesToRational_eq_rationalizeFormal
      (N13FormalInfinitySplit.branchEval w)

/-! ## The actual fixed-divisor extension of the two-chart complex -/

abbrev ChartCochains : Type :=
  IntegralAffineRing × InfinityCurve

abbrev BaseTwistedCochains : Type :=
  ChartCochains × PrincipalParts

/-- Multiply the two actual base-divisor principal parts by the chosen
near-identity overlap transition. -/
def twistedPrincipalOverlap
    (g : NearIdentityTransition) :
    PrincipalParts →ₗ[R₂] Overlap :=
  (N13FormalLineBundleCech.leftMul g.transition).comp
    N13IntegralFormalCech.principalOverlap

@[simp] theorem twistedPrincipalOverlap_apply
    (g : NearIdentityTransition) (p : PrincipalParts) :
    twistedPrincipalOverlap g p =
      N13FormalLineBundleCech.mulOverlap
        g.transition
        (N13IntegralFormalCech.principalOverlap p) :=
  rfl

theorem identity_twistedPrincipalOverlap :
    twistedPrincipalOverlap
        N13FormalLineBundleCech.NearIdentityTransition.identity =
      N13IntegralFormalCech.principalOverlap := by
  apply LinearMap.ext
  intro p
  change
    N13FormalLineBundleCech.mulOverlap
        N13FormalLineBundleCech.oneOverlap
        (N13IntegralFormalCech.principalOverlap p) =
      N13IntegralFormalCech.principalOverlap p
  exact N13FormalLineBundleCech.oneOverlap_mul _

/-- The genuine two-chart restriction difference, enlarged on the affine
side by the two principal parts of the fixed base divisor. -/
def baseTwistedCoboundary
    (g : NearIdentityTransition) :
    BaseTwistedCochains →ₗ[R₂] Overlap :=
  (N13ActualCechComplex.chartCoboundaryLinear.comp
      (LinearMap.fst R₂ ChartCochains PrincipalParts)) +
    ((twistedPrincipalOverlap g).comp
      (LinearMap.snd R₂ ChartCochains PrincipalParts))

@[simp] theorem baseTwistedCoboundary_apply
    (g : NearIdentityTransition)
    (z : BaseTwistedCochains) :
    baseTwistedCoboundary g z =
      N13ActualCechComplex.chartCoboundaryLinear z.1 +
        twistedPrincipalOverlap g z.2 :=
  rfl

/-- For the identity transition this is literally the actual two-chart
coboundary plus the two affine principal parts of the base divisor. -/
theorem identity_baseTwistedCoboundary_apply
    (z : BaseTwistedCochains) :
    baseTwistedCoboundary
        N13FormalLineBundleCech.NearIdentityTransition.identity z =
      N13ActualCechComplex.chartCoboundaryLinear z.1 +
        N13IntegralFormalCech.principalOverlap z.2 := by
  rw [baseTwistedCoboundary_apply,
    identity_twistedPrincipalOverlap]

theorem obstruction_chartCoboundary
    (z : ChartCochains) :
    N13CechLaurentSeriesCore.obstruction
        (N13ActualCechComplex.chartCoboundaryLinear z) = 0 := by
  exact
    (N13ActualCechComplex.obstruction_eq_zero_iff_exists_chart_coboundary
        (N13ActualCechComplex.chartCoboundary z)).2
      ⟨z, rfl⟩

/-- The obstruction of the extended coboundary is exactly the already
verified near-identity connecting map on its principal-part coordinate. -/
theorem obstruction_baseTwistedCoboundary
    (g : NearIdentityTransition)
    (z : BaseTwistedCochains) :
    N13CechLaurentSeriesCore.obstruction
        (baseTwistedCoboundary g z) =
      g.twistedConnectingMap z.2 := by
  rw [baseTwistedCoboundary_apply, map_add,
    obstruction_chartCoboundary, zero_add]
  rfl

/-- Every overlap cochain is a sum of a genuine two-chart coboundary and
a transition-twisted principal part of the fixed base divisor. -/
theorem exists_chart_and_principal_decomposition
    (g : NearIdentityTransition)
    (z : Overlap) :
    ∃ w : ChartCochains, ∃ p : PrincipalParts,
      z =
        N13ActualCechComplex.chartCoboundaryLinear w +
          twistedPrincipalOverlap g p := by
  obtain ⟨p, hp⟩ :=
    g.twistedConnectingMap_surjective
      (N13CechLaurentSeriesCore.obstruction z)
  have hzero :
      N13CechLaurentSeriesCore.obstruction
          (z - twistedPrincipalOverlap g p) = 0 := by
    rw [map_sub]
    change
      N13CechLaurentSeriesCore.obstruction z -
          g.twistedConnectingMap p = 0
    exact sub_eq_zero.mpr hp.symm
  obtain ⟨w, hw⟩ :=
    (N13ActualCechComplex.obstruction_eq_zero_iff_exists_chart_coboundary
        (z - twistedPrincipalOverlap g p)).1 hzero
  refine ⟨w, p, ?_⟩
  rw [N13ActualCechComplex.chartCoboundaryLinear_apply,
    hw]
  abel

/-- The actual fixed-divisor extended Čech coboundary is surjective for
every overlap transition reducing to one. -/
theorem baseTwistedCoboundary_surjective
    (g : NearIdentityTransition) :
    Function.Surjective (baseTwistedCoboundary g) := by
  intro z
  obtain ⟨w, p, hwp⟩ :=
    exists_chart_and_principal_decomposition g z
  exact ⟨(w, p), hwp.symm⟩

theorem range_baseTwistedCoboundary
    (g : NearIdentityTransition) :
    LinearMap.range (baseTwistedCoboundary g) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (baseTwistedCoboundary_surjective g)

/-- The actual additive Čech cokernel after the base-divisor twist. -/
abbrev BaseTwistedCechH1
    (g : NearIdentityTransition) : Type :=
  Overlap ⧸ LinearMap.range (baseTwistedCoboundary g)

noncomputable instance baseTwistedCechH1_subsingleton
    (g : NearIdentityTransition) :
    Subsingleton (BaseTwistedCechH1 g) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact range_baseTwistedCoboundary g

theorem baseTwistedCechH1_eq_zero
    (g : NearIdentityTransition)
    (z : BaseTwistedCechH1 g) :
    z = 0 :=
  Subsingleton.elim _ _

/-- Kernel lifting for the genuine extended cochain module.  Since the
extended coboundary is already surjective, no finiteness assumption on the
infinite overlap module is needed. -/
theorem exists_baseTwisted_kernel_lift
    (g : NearIdentityTransition)
    (x : BaseTwistedCochains)
    (hx :
      baseTwistedCoboundary g x ∈
        IsLocalRing.maximalIdeal R₂ •
          (⊤ : Submodule R₂ Overlap)) :
    ∃ z : BaseTwistedCochains,
      baseTwistedCoboundary g z = 0 ∧
        x - z ∈
          IsLocalRing.maximalIdeal R₂ •
            (⊤ : Submodule R₂ BaseTwistedCochains) := by
  have hrange :
      LinearMap.range (baseTwistedCoboundary g) = ⊤ :=
    range_baseTwistedCoboundary g
  have hmap :
      (IsLocalRing.maximalIdeal R₂ •
          (⊤ : Submodule R₂ BaseTwistedCochains)).map
          (baseTwistedCoboundary g) =
        IsLocalRing.maximalIdeal R₂ •
          (⊤ : Submodule R₂ Overlap) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  have hxmap :
      baseTwistedCoboundary g x ∈
        (IsLocalRing.maximalIdeal R₂ •
          (⊤ : Submodule R₂ BaseTwistedCochains)).map
            (baseTwistedCoboundary g) := by
    rwa [hmap]
  obtain ⟨t, ht, htx⟩ := hxmap
  refine ⟨x - t, ?_, ?_⟩
  · rw [map_sub, htx, sub_self]
  · simpa using ht

end

end MazurProof.N13ActualTwistedCech
