import FLT.Assumptions.MazurProof.N13ClosedFiberLocus
import FLT.Assumptions.MazurProof.N13IntegralCurveProperties
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The unique vertical component of the N13 model

The quotient of `ℤ₂` by `(2)` is `𝔽₂`, so the closed base has one point.
The carrier range formula for scheme pullbacks identifies the closed-fibre
locus with the inverse image of that point.  Since the closed fibre is
irreducible, it is the unique maximal irreducible closed subset of the
vertical locus.

This is the topological unique-vertical-prime input.  A later Cartier
argument upgrades it from components of the fibre to coefficients of
vertical divisors.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Set

namespace MazurProof.N13VerticalFibreTopology

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev R₂ :=
  N13OrdinaryCurveOverlap.R₂

private abbrev X :=
  N13IntegralCurveScheme.IntegralCurve

private theorem verticalIdeal_eq_maximalIdeal :
    N13ClosedFiberCharts.verticalIdeal =
      IsLocalRing.maximalIdeal R₂ := by
  exact
    (PadicInt.maximalIdeal_eq_span_p (p := 2)).symm

/-- The closed-base coordinate ring is the residue field `𝔽₂`. -/
def closedBaseRingEquiv :
    (R₂ ⧸ N13ClosedFiberCharts.verticalIdeal) ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq verticalIdeal_eq_maximalIdeal).trans
    PadicInt.residueField

private noncomputable instance closedBaseRingField :
    Field (R₂ ⧸ N13ClosedFiberCharts.verticalIdeal) :=
  (closedBaseRingEquiv.toMulEquiv.isField
    (Field.toIsField (ZMod 2))).toField

/-- The unique closed point of the two-adic base. -/
def closedBasePoint :
    Spec (.of R₂) :=
  N13ClosedFiberCharts.closedBaseMap
    (default : N13ClosedFiberCharts.ClosedBase)

theorem closedBaseMap_range :
    Set.range N13ClosedFiberCharts.closedBaseMap =
      ({closedBasePoint} : Set (Spec (.of R₂))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_singleton_iff]
    congr 1
    exact Subsingleton.elim _ _
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Set.mem_range_self _

/-- The scheme-theoretic closed fibre has exactly the topological inverse
image of the unique closed base point as its underlying set. -/
theorem fibreRange_eq_preimage_closedBasePoint :
    N13ClosedFiberLocus.fibreRange =
      N13IntegralCurveScheme.toBase ⁻¹'
        ({closedBasePoint} : Set (Spec (.of R₂))) := by
  rw [N13ClosedFiberLocus.fibreRange,
    N13ClosedFiberLocus.inclusion,
    Scheme.Pullback.range_fst,
    closedBaseMap_range]

/-- A vertical component is a maximal nonempty irreducible closed subset
inside the closed-fibre locus. -/
def IsVerticalComponent (Z : Set X) : Prop :=
  IsClosed Z ∧
    IsIrreducible Z ∧
    Z.Nonempty ∧
    Z ⊆ N13ClosedFiberLocus.fibreRange ∧
    ∀ W : Set X,
      IsClosed W →
      IsIrreducible W →
      W.Nonempty →
      Z ⊆ W →
      W ⊆ N13ClosedFiberLocus.fibreRange →
      W = Z

theorem fibreRange_isVerticalComponent :
    IsVerticalComponent N13ClosedFiberLocus.fibreRange := by
  refine
    ⟨N13ClosedFiberLocus.fibreRange_isClosed,
      N13ClosedFiberLocus.fibreRange_isIrreducible,
      ⟨N13ClosedFiberLocus.fibreGenericPoint,
        N13ClosedFiberLocus.fibreGenericPoint_mem⟩,
      Set.Subset.rfl,
      ?_⟩
  intro W _hWclosed _hWirr _hWne _hsub hWfibre
  exact Set.Subset.antisymm hWfibre _hsub

/-- The closed fibre is the only vertical irreducible component. -/
theorem eq_fibreRange_of_isVerticalComponent
    {Z : Set X}
    (hZ : IsVerticalComponent Z) :
    Z = N13ClosedFiberLocus.fibreRange := by
  rcases hZ with
    ⟨_hZclosed, _hZirr, _hZne, hZfibre, hZmax⟩
  exact
    (hZmax
      N13ClosedFiberLocus.fibreRange
      N13ClosedFiberLocus.fibreRange_isClosed
      N13ClosedFiberLocus.fibreRange_isIrreducible
      ⟨N13ClosedFiberLocus.fibreGenericPoint,
        N13ClosedFiberLocus.fibreGenericPoint_mem⟩
      hZfibre
      Set.Subset.rfl).symm

theorem verticalComponent_unique
    {Z W : Set X}
    (hZ : IsVerticalComponent Z)
    (hW : IsVerticalComponent W) :
    Z = W := by
  rw [eq_fibreRange_of_isVerticalComponent hZ,
    eq_fibreRange_of_isVerticalComponent hW]

end MazurProof.N13VerticalFibreTopology
