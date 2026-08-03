import FLT.Assumptions.MazurProof.N13ClosedFiberGlueTransition

/-!
# The N13 closed fibre as an explicit glued scheme

The chart and overlap isomorphisms for the closed fibre assemble to an
isomorphism of the two gluing multispans.  Taking colimits then identifies
the glued pullback datum with the explicit characteristic-two special
fibre.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.N13ClosedFiberGlueIso

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev D :=
  N13IntegralCurveScheme.glueData

private abbrev P :=
  Scheme.Pullback.gluing
    D.openCover
    N13IntegralCurveScheme.toBase
    N13ClosedFiberCharts.closedBaseMap

private abbrev S :=
  N13SpecialFibreScheme.glueData

/-- The closed-fibre isomorphism on each of the two charts. -/
def chartIso : ∀ i : Bool, P.U i ≅ S.U i
  | false =>
      N13ClosedFiberGlueComparison.affinePullbackChartIso
  | true =>
      N13ClosedFiberGlueComparison.infinityPullbackChartIso

/-- The closed-fibre isomorphism on an off-diagonal overlap. -/
def offDiagonalOverlapIso
    (i j : Bool) (h : i ≠ j) :
    P.V (i, j) ≅ S.V (i, j) := by
  cases i <;> cases j
  · exact False.elim (h rfl)
  · exact N13ClosedFiberGlueComparison.affinePullbackOverlapIso
  · exact N13ClosedFiberGlueComparison.infinityPullbackOverlapIso
  · exact False.elim (h rfl)

/-- Naturality of an off-diagonal overlap isomorphism with respect to
the inclusion into its source chart. -/
@[reassoc]
theorem offDiagonalOverlapIso_f
    (i j : Bool) (h : i ≠ j) :
    P.f i j ≫ (chartIso i).hom =
      (offDiagonalOverlapIso i j h).hom ≫ S.f i j := by
  cases i <;> cases j
  · exact False.elim (h rfl)
  · exact N13ClosedFiberGlueComparison.affinePullback_f
  · exact N13ClosedFiberGlueComparison.infinityPullback_f
  · exact False.elim (h rfl)

/-- Naturality of an off-diagonal overlap isomorphism with respect to
the gluing transition. -/
@[reassoc]
theorem offDiagonalOverlapIso_t
    (i j : Bool) (h : i ≠ j) :
    P.t i j ≫
        (offDiagonalOverlapIso j i h.symm).hom =
      (offDiagonalOverlapIso i j h).hom ≫ S.t i j := by
  cases i <;> cases j
  · exact False.elim (h rfl)
  · exact N13ClosedFiberGlueTransition.affinePullback_t
  · exact N13ClosedFiberGlueTransition.infinityPullback_t
  · exact False.elim (h rfl)

/-- The overlap isomorphism for every ordered pair of charts.  On the
diagonal it is forced by the two isomorphisms from the diagonal
overlap to its chart. -/
def overlapIso (i j : Bool) :
    P.V (i, j) ≅ S.V (i, j) :=
  if h : i = j then
    by
      subst j
      exact
        asIso (P.f i i) ≪≫
          chartIso i ≪≫
            (asIso (S.f i i)).symm
  else
    offDiagonalOverlapIso i j h

/-- Naturality for the first leg of the gluing multispan. -/
@[reassoc]
theorem overlapIso_fst_naturality (i j : Bool) :
    P.f i j ≫ (chartIso i).hom =
      (overlapIso i j).hom ≫ S.f i j := by
  by_cases h : i = j
  · subst j
    simp [overlapIso, Category.assoc]
  · simpa [overlapIso, h] using
      offDiagonalOverlapIso_f i j h

/-- Naturality with respect to every gluing transition. -/
@[reassoc]
theorem overlapIso_t_naturality (i j : Bool) :
    P.t i j ≫ (overlapIso j i).hom =
      (overlapIso i j).hom ≫ S.t i j := by
  by_cases h : i = j
  · subst j
    simp [overlapIso]
  · simpa [overlapIso, h, Ne.symm h] using
      offDiagonalOverlapIso_t i j h

/-- Naturality for the second leg of the gluing multispan follows from
transition naturality and the first-leg square for the reversed
ordered pair. -/
@[reassoc]
theorem overlapIso_snd_naturality (i j : Bool) :
    (P.t i j ≫ P.f j i) ≫ (chartIso j).hom =
      (overlapIso i j).hom ≫
        (S.t i j ≫ S.f j i) := by
  calc
    (P.t i j ≫ P.f j i) ≫ (chartIso j).hom =
        P.t i j ≫ (P.f j i ≫ (chartIso j).hom) :=
      Category.assoc _ _ _
    _ =
        P.t i j ≫ ((overlapIso j i).hom ≫ S.f j i) := by
      exact congrArg
        (fun k => P.t i j ≫ k)
        (overlapIso_fst_naturality j i)
    _ =
        (P.t i j ≫ (overlapIso j i).hom) ≫ S.f j i :=
      (Category.assoc _ _ _).symm
    _ =
        ((overlapIso i j).hom ≫ S.t i j) ≫ S.f j i := by
      exact congrArg
        (fun k => k ≫ S.f j i)
        (overlapIso_t_naturality i j)
    _ =
        (overlapIso i j).hom ≫ (S.t i j ≫ S.f j i) :=
      Category.assoc _ _ _

/-- The natural isomorphism between the pullback and explicit
special-fibre gluing multispans. -/
def diagramIso :
    P.diagram.multispan ≅ S.diagram.multispan :=
  WalkingMultispan.functorExt
    (fun ij => overlapIso ij.1 ij.2)
    chartIso
    (fun ij => by
      rcases ij with ⟨i, j⟩
      change
        P.f i j ≫ (chartIso i).hom =
          (overlapIso i j).hom ≫ S.f i j
      exact overlapIso_fst_naturality i j)
    (fun ij => by
      rcases ij with ⟨i, j⟩
      change
        (P.t i j ≫ P.f j i) ≫ (chartIso j).hom =
          (overlapIso i j).hom ≫
            (S.t i j ≫ S.f j i)
      exact overlapIso_snd_naturality i j)

set_option backward.isDefEq.respectTransparency false in
/-- The glued pullback datum is isomorphic to the explicit N13
special fibre. -/
def gluedIso : P.glued ≅ S.glued :=
  HasColimit.isoOfNatIso diagramIso

end MazurProof.N13ClosedFiberGlueIso
