import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of a glue-data overlap

The direct base change of an overlap in scheme glue data is canonically
the overlap presentation used by `Scheme.Pullback.gluing`.  The
comparison is assembled from the glue-data intersection theorem,
pullback associativity, and pullback symmetry.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.GlueDataClosedBaseChange

universe u

variable (D : Scheme.GlueData.{u})
variable {S T : Scheme.{u}}
variable (p : D.glued ⟶ S) (g : T ⟶ S)

/-- The structure morphism on an oriented overlap. -/
def overlapToBase (i j : D.J) :
    D.V (i, j) ⟶ S :=
  D.f i j ≫ D.ι i ≫ p

/-- The original overlap is canonically the intersection of its two
charts in the glued scheme. -/
def overlapIntersectionIso (i j : D.J) :
    D.V (i, j) ≅ pullback (D.ι i) (D.ι j) :=
  (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso
    (pullback.isLimit (D.ι i) (D.ι j))

@[simp, reassoc]
theorem overlapIntersectionIso_hom_fst (i j : D.J) :
    (overlapIntersectionIso D i j).hom ≫
        pullback.fst (D.ι i) (D.ι j) =
      D.f i j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

@[simp, reassoc]
theorem overlapIntersectionIso_hom_snd (i j : D.J) :
    (overlapIntersectionIso D i j).hom ≫
        pullback.snd (D.ι i) (D.ι j) =
      D.t i j ≫ D.f j i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

/-- Use the orientation `Uⱼ ×_X Uᵢ`, whose second projection is the
chosen map from the overlap to `Uᵢ`. -/
def overlapIntersectionSwapIso (i j : D.J) :
    D.V (i, j) ≅ pullback (D.ι j) (D.ι i) :=
  overlapIntersectionIso D i j ≪≫
    pullbackSymmetry (D.ι i) (D.ι j)

@[simp, reassoc]
theorem overlapIntersectionSwapIso_hom_snd (i j : D.J) :
    (overlapIntersectionSwapIso D i j).hom ≫
        pullback.snd (D.ι j) (D.ι i) =
      D.f i j := by
  simp [overlapIntersectionSwapIso]

/-- Transport the direct base change of `D.V(i,j)` across the canonical
intersection isomorphism. -/
def transportOverlapBaseChange (i j : D.J) :
    pullback (overlapToBase D p i j) g ≅
      pullback
        (pullback.snd (D.ι j) (D.ι i) ≫ D.ι i ≫ p)
        g :=
  asIso <|
    pullback.map
      (overlapToBase D p i j)
      g
      (pullback.snd (D.ι j) (D.ι i) ≫ D.ι i ≫ p)
      g
      (overlapIntersectionSwapIso D i j).hom
      (𝟙 T)
      (𝟙 S)
      (by
        simp only [Category.comp_id, overlapToBase,
          overlapIntersectionSwapIso_hom_snd_assoc])
      (by simp)

/-- The direct base change of `D.V(i,j)` is the overlap object used by
the pullback gluing construction. -/
def overlapBaseChangeIso (i j : D.J) :
    pullback (overlapToBase D p i j) g ≅
      pullback
        (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
        (D.ι j) :=
  transportOverlapBaseChange D p g i j ≪≫
    pullbackAssoc
      (D.ι j)
      (D.ι i)
      (D.ι i ≫ p)
      g ≪≫
    pullbackSymmetry
      (D.ι j)
      (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)

end MazurProof.GlueDataClosedBaseChange
