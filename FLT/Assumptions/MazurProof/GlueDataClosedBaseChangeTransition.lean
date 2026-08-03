import FLT.Assumptions.MazurProof.GlueDataClosedBaseChange

/-!
# Transition maps under closed base change

The direct base change of a glue-data overlap carries the original
transition map.  Under the canonical comparison with the overlap used
by `Scheme.Pullback.gluing`, this direct transition agrees with
`Scheme.Pullback.t`.

The proof is categorical: both maps are compared through the three
projections of the nested pullbacks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurProof.GlueDataClosedBaseChange

universe u

variable (D : Scheme.GlueData.{u})
variable {S T : Scheme.{u}}
variable (p : D.glued ⟶ S) (g : T ⟶ S)

/-- Direct base change of an overlap transition. -/
def overlapTransitionBaseChange (i j : D.J) :
    pullback (overlapToBase D p i j) g ⟶
      pullback (overlapToBase D p j i) g :=
  pullback.map
    (overlapToBase D p i j)
    g
    (overlapToBase D p j i)
    g
    (D.t i j)
    (𝟙 T)
    (𝟙 S)
    (by
      simp only [overlapToBase, Category.comp_id]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ p) (D.glue_condition i j).symm)
    (by simp)

@[reassoc]
theorem overlapTransitionBaseChange_fst (i j : D.J) :
    overlapTransitionBaseChange D p g i j ≫
        pullback.fst (overlapToBase D p j i) g =
      pullback.fst (overlapToBase D p i j) g ≫ D.t i j := by
  unfold overlapTransitionBaseChange
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem overlapTransitionBaseChange_snd (i j : D.J) :
    overlapTransitionBaseChange D p g i j ≫
        pullback.snd (overlapToBase D p j i) g =
      pullback.snd (overlapToBase D p i j) g := by
  unfold overlapTransitionBaseChange
  exact pullback.lift_snd _ _ _

@[reassoc]
theorem overlapBaseChangeIso_hom_fst_fst (i j : D.J) :
    (overlapBaseChangeIso D p g i j).hom ≫
          pullback.fst
            (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
            (D.ι j) ≫
        pullback.fst (D.ι i ≫ p) g =
      pullback.fst (overlapToBase D p i j) g ≫ D.f i j := by
  rw [overlapBaseChangeIso_hom_fst_assoc]
  unfold overlapToChartBaseChange
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem overlapBaseChangeIso_hom_fst_snd (i j : D.J) :
    (overlapBaseChangeIso D p g i j).hom ≫
          pullback.fst
            (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
            (D.ι j) ≫
        pullback.snd (D.ι i ≫ p) g =
      pullback.snd (overlapToBase D p i j) g := by
  rw [overlapBaseChangeIso_hom_fst_assoc]
  unfold overlapToChartBaseChange
  exact pullback.lift_snd _ _ _

@[reassoc]
theorem overlapBaseChangeIso_hom_snd (i j : D.J) :
    (overlapBaseChangeIso D p g i j).hom ≫
        pullback.snd
          (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
          (D.ι j) =
      pullback.fst (overlapToBase D p i j) g ≫
        D.t i j ≫ D.f j i := by
  apply (cancel_mono (D.ι j)).mp
  calc
    ((overlapBaseChangeIso D p g i j).hom ≫
        pullback.snd
          (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
          (D.ι j)) ≫ D.ι j =
      ((overlapBaseChangeIso D p g i j).hom ≫
          pullback.fst
            (pullback.fst (D.ι i ≫ p) g ≫ D.ι i)
            (D.ι j)) ≫
        (pullback.fst (D.ι i ≫ p) g ≫ D.ι i) := by
          rw [Category.assoc, Category.assoc,
            pullback.condition]
    _ =
      (pullback.fst (overlapToBase D p i j) g ≫
          D.f i j) ≫ D.ι i := by
            exact overlapBaseChangeIso_hom_fst_fst_assoc D p g i j _
    _ =
      (pullback.fst (overlapToBase D p i j) g ≫
          D.t i j ≫ D.f j i) ≫ D.ι j := by
            simp only [Category.assoc]
            rw [D.glue_condition]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from a direct overlap base change to the
pullback gluing intertwines the two transition maps. -/
theorem overlapBaseChangeIso_hom_t (i j : D.openCover.I₀) :
    (overlapBaseChangeIso D p g i j).hom ≫
        Scheme.Pullback.t D.openCover p g i j =
      overlapTransitionBaseChange D p g i j ≫
        (overlapBaseChangeIso D p g j i).hom := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc
        (((overlapBaseChangeIso D p g i j).hom ≫
              Scheme.Pullback.t D.openCover p g i j) ≫
            pullback.fst
              (pullback.fst (D.openCover.f j ≫ p) g ≫
                D.openCover.f j)
              (D.openCover.f i)) ≫
          pullback.fst (D.openCover.f j ≫ p) g =
            (overlapBaseChangeIso D p g i j).hom ≫
              pullback.snd
                (pullback.fst (D.openCover.f i ≫ p) g ≫
                  D.openCover.f i)
                (D.openCover.f j) := by
                  simpa only [Category.assoc] using
                    congrArg
                      (fun k =>
                        (overlapBaseChangeIso D p g i j).hom ≫ k)
                      (Scheme.Pullback.t_fst_fst
                        D.openCover p g i j)
        _ =
            pullback.fst (overlapToBase D p i j) g ≫
              D.t i j ≫ D.f j i :=
          overlapBaseChangeIso_hom_snd D p g i j
        _ =
            ((overlapTransitionBaseChange D p g i j ≫
                (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.fst
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i)) ≫
              pullback.fst (D.openCover.f j ≫ p) g := by
          symm
          calc
            ((overlapTransitionBaseChange D p g i j ≫
                (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.fst
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i)) ≫
              pullback.fst (D.openCover.f j ≫ p) g =
                overlapTransitionBaseChange D p g i j ≫
                  ((overlapBaseChangeIso D p g j i).hom ≫
                    pullback.fst
                      (pullback.fst (D.openCover.f j ≫ p) g ≫
                        D.openCover.f j)
                      (D.openCover.f i) ≫
                    pullback.fst (D.openCover.f j ≫ p) g) := by
                      simp only [Category.assoc]
            _ =
                overlapTransitionBaseChange D p g i j ≫
                  (pullback.fst (overlapToBase D p j i) g ≫
                    D.f j i) := by
                      simpa only [Scheme.GlueData.openCover] using
                        congrArg
                          (fun k =>
                            overlapTransitionBaseChange D p g i j ≫ k)
                          (overlapBaseChangeIso_hom_fst_fst
                            D p g j i)
            _ =
                (overlapTransitionBaseChange D p g i j ≫
                  pullback.fst (overlapToBase D p j i) g) ≫
                    D.f j i := (Category.assoc _ _ _).symm
            _ =
                (pullback.fst (overlapToBase D p i j) g ≫
                  D.t i j) ≫ D.f j i := by
                    exact congrArg
                      (fun k => k ≫ D.f j i)
                      (overlapTransitionBaseChange_fst
                        D p g i j)
            _ =
                pullback.fst (overlapToBase D p i j) g ≫
                  D.t i j ≫ D.f j i := Category.assoc _ _ _
    · calc
        (((overlapBaseChangeIso D p g i j).hom ≫
              Scheme.Pullback.t D.openCover p g i j) ≫
            pullback.fst
              (pullback.fst (D.openCover.f j ≫ p) g ≫
                D.openCover.f j)
              (D.openCover.f i)) ≫
          pullback.snd (D.openCover.f j ≫ p) g =
            (overlapBaseChangeIso D p g i j).hom ≫
              pullback.fst
                (pullback.fst (D.openCover.f i ≫ p) g ≫
                  D.openCover.f i)
                (D.openCover.f j) ≫
              pullback.snd (D.openCover.f i ≫ p) g := by
                simpa only [Category.assoc,
                  Scheme.GlueData.openCover_f] using
                  congrArg
                    (fun k =>
                      (overlapBaseChangeIso D p g i j).hom ≫ k)
                    (Scheme.Pullback.t_fst_snd
                      D.openCover p g i j)
        _ = pullback.snd (overlapToBase D p i j) g := by
          simpa only [Scheme.GlueData.openCover] using
            overlapBaseChangeIso_hom_fst_snd D p g i j
        _ =
            ((overlapTransitionBaseChange D p g i j ≫
                (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.fst
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i)) ≫
              pullback.snd (D.openCover.f j ≫ p) g := by
          symm
          calc
            ((overlapTransitionBaseChange D p g i j ≫
                (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.fst
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i)) ≫
              pullback.snd (D.openCover.f j ≫ p) g =
                overlapTransitionBaseChange D p g i j ≫
                  ((overlapBaseChangeIso D p g j i).hom ≫
                    pullback.fst
                      (pullback.fst (D.openCover.f j ≫ p) g ≫
                        D.openCover.f j)
                      (D.openCover.f i) ≫
                    pullback.snd (D.openCover.f j ≫ p) g) := by
                      simp only [Category.assoc]
            _ =
                overlapTransitionBaseChange D p g i j ≫
                  pullback.snd (overlapToBase D p j i) g := by
                    simpa only [Scheme.GlueData.openCover] using
                      congrArg
                        (fun k =>
                          overlapTransitionBaseChange D p g i j ≫ k)
                        (overlapBaseChangeIso_hom_fst_snd
                          D p g j i)
            _ = pullback.snd (overlapToBase D p i j) g :=
              overlapTransitionBaseChange_snd D p g i j
  · calc
      ((overlapBaseChangeIso D p g i j).hom ≫
          Scheme.Pullback.t D.openCover p g i j) ≫
        pullback.snd
          (pullback.fst (D.openCover.f j ≫ p) g ≫
            D.openCover.f j)
          (D.openCover.f i) =
          (overlapBaseChangeIso D p g i j).hom ≫
            pullback.fst
              (pullback.fst (D.openCover.f i ≫ p) g ≫
                D.openCover.f i)
              (D.openCover.f j) ≫
            pullback.fst (D.openCover.f i ≫ p) g := by
              simpa only [Category.assoc,
                Scheme.GlueData.openCover_f] using
                congrArg
                  (fun k =>
                    (overlapBaseChangeIso D p g i j).hom ≫ k)
                  (Scheme.Pullback.t_snd D.openCover p g i j)
      _ =
          pullback.fst (overlapToBase D p i j) g ≫
            D.f i j := by
        simpa only [Scheme.GlueData.openCover] using
          overlapBaseChangeIso_hom_fst_fst D p g i j
      _ =
          (overlapTransitionBaseChange D p g i j ≫
            (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.snd
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i) := by
        symm
        calc
          (overlapTransitionBaseChange D p g i j ≫
            (overlapBaseChangeIso D p g j i).hom) ≫
              pullback.snd
                (pullback.fst (D.openCover.f j ≫ p) g ≫
                  D.openCover.f j)
                (D.openCover.f i) =
              overlapTransitionBaseChange D p g i j ≫
                ((overlapBaseChangeIso D p g j i).hom ≫
                  pullback.snd
                    (pullback.fst (D.openCover.f j ≫ p) g ≫
                      D.openCover.f j)
                    (D.openCover.f i)) := by
                      simp only [Category.assoc]
          _ =
              overlapTransitionBaseChange D p g i j ≫
                (pullback.fst (overlapToBase D p j i) g ≫
                  D.t j i ≫ D.f i j) := by
                    simpa only [Scheme.GlueData.openCover] using
                      congrArg
                        (fun k =>
                          overlapTransitionBaseChange D p g i j ≫ k)
                        (overlapBaseChangeIso_hom_snd D p g j i)
          _ =
              (overlapTransitionBaseChange D p g i j ≫
                pullback.fst (overlapToBase D p j i) g) ≫
                  D.t j i ≫ D.f i j := by
                    simp only [Category.assoc]
          _ =
              (pullback.fst (overlapToBase D p i j) g ≫
                D.t i j) ≫ D.t j i ≫ D.f i j := by
                  exact congrArg
                    (fun k => k ≫ D.t j i ≫ D.f i j)
                    (overlapTransitionBaseChange_fst D p g i j)
          _ =
              pullback.fst (overlapToBase D p i j) g ≫
                D.f i j := by
                  simp only [Category.assoc, D.t_inv_assoc]

end MazurProof.GlueDataClosedBaseChange
