import FLT.Assumptions.MazurProof.N13SpecialCurveOverlap
import FLT.Assumptions.MazurProof.GlueDataOffDiagonal
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Off-diagonal gluing data for the N13 special fibre

This file records the two integral characteristic-two affine charts and
their distinguished principal-open transition as
`CategoryTheory.GlueData'`.  The index type is `Bool`, so the
three-distinct-index compatibility condition is vacuous.  Promotion to
`Scheme.GlueData` is the next layer.
-/

open CategoryTheory
open Set Topology

namespace MazurProof.N13SpecialFibreScheme

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev Affine :=
  N13SpecialCurveOverlap.AffineCurve

private abbrev Infinity :=
  N13SpecialCurveOverlap.CoordinateRing

private abbrev AffineOverlap :=
  N13SpecialCurveOverlap.AffineOverlap

private abbrev InfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

open AlgebraicGeometry

/-- The affine and infinity charts of the special fibre. -/
def chart : Bool → Scheme
  | false => Spec (.of Affine)
  | true => Spec (.of Infinity)

/-- The oriented intersections of the two charts. -/
def overlap : ∀ i j : Bool, i ≠ j → Scheme
  | false, false, h => False.elim (h rfl)
  | false, true, _ => Spec (.of AffineOverlap)
  | true, false, _ => Spec (.of InfinityOverlap)
  | true, true, h => False.elim (h rfl)

/-- A principal-open intersection included into its source chart. -/
def overlapInclusion : ∀ i j (h : i ≠ j), overlap i j h ⟶ chart i
  | false, false, h => False.elim (h rfl)
  | false, true, _ =>
      Spec.map
        (CommRingCat.ofHom
          (algebraMap Affine AffineOverlap))
  | true, false, _ =>
      Spec.map
        (CommRingCat.ofHom
          (algebraMap Infinity InfinityOverlap))
  | true, true, h => False.elim (h rfl)

private theorem overlapInclusion_open :
    ∀ i j (h : i ≠ j), IsOpenImmersion (overlapInclusion i j h) := by
  intro i j h
  cases i <;> cases j
  · exact False.elim (h rfl)
  · dsimp [overlapInclusion, overlap, chart]
    infer_instance
  · dsimp [overlapInclusion, overlap, chart]
    infer_instance
  · exact False.elim (h rfl)

/-- Transition isomorphisms on the oriented intersections. -/
def transition : ∀ i j (h : i ≠ j), overlap i j h ⟶ overlap j i h.symm
  | false, false, h => False.elim (h rfl)
  | false, true, _ =>
      Spec.map
        (CommRingCat.ofHom
          N13SpecialCurveOverlap.overlapEquiv.symm.toRingHom)
  | true, false, _ =>
      Spec.map
        (CommRingCat.ofHom
          N13SpecialCurveOverlap.overlapEquiv.toRingHom)
  | true, true, h => False.elim (h rfl)

private theorem transition_inv :
    ∀ i j (h : i ≠ j),
      transition i j h ≫ transition j i h.symm = 𝟙 _ := by
  intro i j h
  cases i <;> cases j
  · exact False.elim (h rfl)
  · change
      Spec.map
            (CommRingCat.ofHom
              N13SpecialCurveOverlap.overlapEquiv.symm.toRingHom) ≫
          Spec.map
            (CommRingCat.ofHom
              N13SpecialCurveOverlap.overlapEquiv.toRingHom) =
        𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of AffineOverlap)
    ext z
    simp
  · change
      Spec.map
            (CommRingCat.ofHom
              N13SpecialCurveOverlap.overlapEquiv.toRingHom) ≫
          Spec.map
            (CommRingCat.ofHom
              N13SpecialCurveOverlap.overlapEquiv.symm.toRingHom) =
        𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of InfinityOverlap)
    ext z
    simp
  · exact False.elim (h rfl)

/-- The off-diagonal gluing datum.  With only two charts, the
triple-overlap fields are vacuous. -/
def glueData' : CategoryTheory.GlueData' Scheme where
  J := Bool
  U := chart
  V := overlap
  f := overlapInclusion
  f_mono := by
    intro i j h
    cases i <;> cases j
    · exact False.elim (h rfl)
    · dsimp [overlapInclusion, overlap, chart]
      infer_instance
    · dsimp [overlapInclusion, overlap, chart]
      infer_instance
    · exact False.elim (h rfl)
  f_hasPullback := by
    intro i j k hij hik
    infer_instance
  t := transition
  t' := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k
    all_goals contradiction
  t_fac := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k
    all_goals contradiction
  t_inv := transition_inv
  cocycle := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k
    all_goals contradiction

private theorem glueData'_f_open
    (i j : glueData'.J) (h : i ≠ j) :
    IsOpenImmersion (glueData'.f i j h) := by
  change Bool at i j
  change IsOpenImmersion (overlapInclusion i j h)
  exact overlapInclusion_open i j h

private theorem glueData_f'_open
    (i j : glueData'.J) :
    IsOpenImmersion (glueData'.f' i j) := by
  classical
  unfold CategoryTheory.GlueData'.f'
  split
  · infer_instance
  · rename_i h
    haveI := glueData'_f_open i j h
    infer_instance

/-- The full scheme gluing datum obtained from the two off-diagonal
principal opens. -/
def glueData : Scheme.GlueData where
  toGlueData :=
    CategoryTheory.GlueData.ofGlueData' glueData'
  f_open := glueData_f'_open

open scoped Classical in
/-- The explicit affine overlap, identified with the corresponding
off-diagonal object of the full glue data. -/
def affineOverlapToGlueDataIso :
    Spec (.of AffineOverlap) ≅ glueData.V (false, true) :=
  CategoryTheory.GlueData'.offDiagonalIso glueData'
    (i := false) (j := true) (by simp)

open scoped Classical in
/-- The explicit infinity overlap, identified with the corresponding
off-diagonal object of the full glue data. -/
def infinityOverlapToGlueDataIso :
    Spec (.of InfinityOverlap) ≅ glueData.V (true, false) :=
  CategoryTheory.GlueData'.offDiagonalIso glueData'
    (i := true) (j := false) (by simp)

@[reassoc]
theorem affineOverlapToGlueDataIso_hom_t :
    affineOverlapToGlueDataIso.hom ≫ glueData.t false true =
      transition false true (by simp) ≫
        infinityOverlapToGlueDataIso.hom := by
  exact CategoryTheory.GlueData'.offDiagonalIso_hom_t glueData'
    (i := false) (j := true) (by simp)

@[simp, reassoc]
theorem affineOverlapToGlueDataIso_hom_f :
    affineOverlapToGlueDataIso.hom ≫ glueData.f false true =
      overlapInclusion false true (by decide) := by
  exact CategoryTheory.GlueData'.offDiagonalIso_hom_f glueData'
    (i := false) (j := true) (by simp)

@[simp, reassoc]
theorem infinityOverlapToGlueDataIso_hom_f :
    infinityOverlapToGlueDataIso.hom ≫ glueData.f true false =
      overlapInclusion true false (by decide) := by
  exact CategoryTheory.GlueData'.offDiagonalIso_hom_f glueData'
    (i := true) (j := false) (by simp)

/-- The glued characteristic-two special fibre. -/
abbrev SpecialFibre : Scheme :=
  glueData.glued

/-- The canonical affine/infinity open cover. -/
abbrev chartCover : SpecialFibre.OpenCover :=
  glueData.openCover

private instance chart_isIntegral (i : Bool) :
    IsIntegral (chart i) := by
  cases i <;> dsimp [chart] <;> infer_instance

/-- Two irreducible open subsets with nonempty intersection and union the
whole space make the ambient space irreducible. -/
private theorem irreducibleSpace_of_two_open_cover
    {X : Type*} [TopologicalSpace X]
    (A B : Set X)
    (hAopen : IsOpen A)
    (_hBopen : IsOpen B)
    (hcover : A ∪ B = Set.univ)
    (hAirr : IsIrreducible A)
    (hBirr : IsIrreducible B)
    (hAB : (A ∩ B).Nonempty) :
    IrreducibleSpace X := by
  rw [irreducibleSpace_def]
  have hAdense : Dense A := by
    rw [dense_iff_inter_open]
    intro W hW hWne
    by_cases hWA : (W ∩ A).Nonempty
    · exact hWA
    · have hBW : (B ∩ W).Nonempty := by
        obtain ⟨x, hxW⟩ := hWne
        have hxCover : x ∈ A ∪ B := by
          rw [hcover]
          trivial
        rcases hxCover with hxA | hxB
        · exact (hWA ⟨x, hxW, hxA⟩).elim
        · exact ⟨x, hxB, hxW⟩
      have hBA : (B ∩ A).Nonempty := by
        simpa [inter_comm] using hAB
      rcases
          hBirr.isPreirreducible
            W A hW hAopen hBW hBA with
        ⟨x, hxB, hxW, hxA⟩
      exact ⟨x, hxW, hxA⟩
  have hclosure : IsIrreducible (closure A) :=
    hAirr.closure
  rw [hAdense.closure_eq] at hclosure
  simpa using hclosure

private def affineRange : Set SpecialFibre :=
  Set.range (glueData.ι false).base

private def infinityRange : Set SpecialFibre :=
  Set.range (glueData.ι true).base

private theorem affineRange_open :
    IsOpen affineRange :=
  (glueData.ι false).isOpenEmbedding.isOpen_range

private theorem infinityRange_open :
    IsOpen infinityRange :=
  (glueData.ι true).isOpenEmbedding.isOpen_range

private theorem affineRange_irreducible :
    IsIrreducible affineRange := by
  rw [affineRange, ← Set.image_univ]
  exact
    (IrreducibleSpace.isIrreducible_univ
      (chart false).carrier).image
      (glueData.ι false).base
      (glueData.ι false).base.hom.continuous.continuousOn

private theorem infinityRange_irreducible :
    IsIrreducible infinityRange := by
  rw [infinityRange, ← Set.image_univ]
  exact
    (IrreducibleSpace.isIrreducible_univ
      (chart true).carrier).image
      (glueData.ι true).base
      (glueData.ι true).base.hom.continuous.continuousOn

private theorem ranges_cover :
    affineRange ∪ infinityRange = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, hy⟩ := glueData.ι_jointly_surjective x
  subst x
  cases i
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

private theorem affine_xClass_ne_zero :
    N13SpecialCurveOverlap.xClass ≠ 0 := by
  apply N13GoodCoordinateRingTwo.xClass_ne_zero
  exact Polynomial.X_ne_zero

private instance affineOverlap_isDomain :
    IsDomain AffineOverlap :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      affine_xClass_ne_zero)

private noncomputable def overlapPoint :
    (glueData.V (false, true)).carrier := by
  let p : (Spec (.of AffineOverlap)).carrier :=
    Classical.choice
      (inferInstance :
        Nonempty (Spec (.of AffineOverlap)).carrier)
  simpa [glueData, CategoryTheory.GlueData.ofGlueData',
    glueData', overlap] using p

private theorem ranges_inter_nonempty :
    (affineRange ∩ infinityRange).Nonempty := by
  let z := overlapPoint
  refine
    ⟨glueData.ι false (glueData.f false true z), ?_, ?_⟩
  · exact ⟨_, rfl⟩
  · refine
      ⟨glueData.f true false
          (glueData.t false true z), ?_⟩
    have h :=
      congrArg (fun q => q z)
        (glueData.glue_condition false true)
    change
      (glueData.ι true)
          (glueData.f true false
            (glueData.t false true z)) =
        (glueData.ι false)
          (glueData.f false true z) at h
    exact h

instance specialFibre_isReduced :
    IsReduced SpecialFibre := by
  letI :
      ∀ i : Bool,
        IsReduced ((glueData.openCover).X i) :=
    fun i => by
      change IsReduced (chart i)
      infer_instance
  exact IsReduced.of_openCover
    SpecialFibre glueData.openCover

instance specialFibre_irreducibleSpace :
    IrreducibleSpace SpecialFibre :=
  irreducibleSpace_of_two_open_cover
    affineRange
    infinityRange
    affineRange_open
    infinityRange_open
    ranges_cover
    affineRange_irreducible
    infinityRange_irreducible
    ranges_inter_nonempty

instance specialFibre_isIntegral :
    IsIntegral SpecialFibre :=
  isIntegral_of_irreducibleSpace_of_isReduced
    SpecialFibre

end

end MazurProof.N13SpecialFibreScheme
