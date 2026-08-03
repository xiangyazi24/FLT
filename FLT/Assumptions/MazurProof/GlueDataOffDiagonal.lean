import Mathlib.CategoryTheory.GlueData

/-!
# Off-diagonal adapters for `GlueData.ofGlueData'`

The full glue data constructed from `GlueData'` stores its overlap
objects behind a diagonal/off-diagonal conditional.  For distinct
indices, this file gives the canonical comparison with the original
off-diagonal object and records its compatibility with the transition
map.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.GlueData'

universe v u

variable {C : Type u} [Category.{v} C] (D : GlueData' C)

open scoped Classical

/-- The canonical identification of an original off-diagonal overlap
with the corresponding overlap of `GlueData.ofGlueData'`. -/
def offDiagonalIso {i j : D.J} (h : i ≠ j) :
    D.V i j h ≅ (GlueData.ofGlueData' D).V (i, j) :=
  eqToIso (dif_neg h).symm

/-- The canonical off-diagonal identification recovers the original
overlap inclusion. -/
@[simp, reassoc]
theorem offDiagonalIso_hom_f {i j : D.J} (h : i ≠ j) :
    (offDiagonalIso D h).hom ≫ (GlueData.ofGlueData' D).f i j =
      D.f i j h := by
  simp [offDiagonalIso, GlueData.ofGlueData', GlueData'.f', h]

/-- The canonical off-diagonal identification intertwines the original
and promoted transition maps. -/
@[reassoc]
theorem offDiagonalIso_hom_t {i j : D.J} (h : i ≠ j) :
    (offDiagonalIso D h).hom ≫ (GlueData.ofGlueData' D).t i j =
      D.t i j h ≫ (offDiagonalIso D h.symm).hom := by
  simp [offDiagonalIso, GlueData.ofGlueData', h]

end CategoryTheory.GlueData'
