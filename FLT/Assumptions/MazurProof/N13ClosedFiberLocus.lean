import FLT.Assumptions.MazurProof.N13ClosedFiberIso
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The irreducible N13 vertical fibre locus

The actual closed fibre embeds as a single irreducible closed subset of
the integral two-chart model.  This records its generic point
topologically, before the later codimension-one and Cartier-divisor
arguments.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Set

namespace MazurProof.N13ClosedFiberLocus

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev X :=
  N13IntegralCurveScheme.IntegralCurve

private abbrev X₀ :=
  N13ClosedFiberIso.ClosedFiber

/-- The closed-fibre inclusion into the integral N13 model. -/
abbrev inclusion : X₀ ⟶ X :=
  pullback.fst
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

private instance closedBaseMap_isClosedImmersion :
    IsClosedImmersion N13ClosedFiberCharts.closedBaseMap := by
  change
    IsClosedImmersion
      (Spec.map
        (CommRingCat.ofHom
          (Ideal.Quotient.mk
            N13ClosedFiberCharts.verticalIdeal)))
  exact
    IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective

instance inclusion_isClosedImmersion :
    IsClosedImmersion inclusion :=
  inferInstance

/-- The underlying closed subset of the special fibre. -/
def fibreRange : Set X :=
  Set.range inclusion

theorem fibreRange_isClosed :
    IsClosed fibreRange :=
  inclusion.isClosedEmbedding.isClosed_range

theorem fibreRange_isIrreducible :
    IsIrreducible fibreRange := by
  rw [fibreRange, ← Set.image_univ]
  exact
    (IrreducibleSpace.isIrreducible_univ X₀).image
      inclusion inclusion.continuous.continuousOn

/-- The generic point of the integral closed fibre, viewed in the
total model. -/
def fibreGenericPoint : X :=
  inclusion (genericPoint X₀)

/-- The closure of the fibre generic point is exactly the whole
scheme-theoretic closed-fibre locus. -/
theorem closure_fibreGenericPoint :
    closure ({fibreGenericPoint} : Set X) = fibreRange := by
  rw [fibreGenericPoint, ← Set.image_singleton,
    inclusion.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ]
  rfl

theorem fibreGenericPoint_mem :
    fibreGenericPoint ∈ fibreRange :=
  Set.mem_range_self (genericPoint X₀)

end MazurProof.N13ClosedFiberLocus
