import FLT.Assumptions.MazurProof.N13OrdinaryCurveOverlap
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The integral two-chart N13 curve

The ordinary affine and infinity charts over `R₂` are glued along their
distinguished principal opens.  As for the special fibre, the index type
is `Bool`, so the genuinely three-distinct-index part of
`CategoryTheory.GlueData'` is empty.
-/

open CategoryTheory CategoryTheory.Limits
open Polynomial

namespace MazurProof.N13IntegralCurveScheme

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

private abbrev Affine :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev Infinity :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev AffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

private abbrev InfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

open AlgebraicGeometry

/-- The ordinary affine and infinity charts. -/
def chart : Bool → Scheme
  | false => Spec (.of Affine)
  | true => Spec (.of Infinity)

/-- The two oriented principal-open intersections. -/
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

/-- The chart transition induced by the ordinary overlap ring
equivalence. -/
def transition : ∀ i j (h : i ≠ j), overlap i j h ⟶ overlap j i h.symm
  | false, false, h => False.elim (h rfl)
  | false, true, _ =>
      Spec.map
        (CommRingCat.ofHom
          N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom)
  | true, false, _ =>
      Spec.map
        (CommRingCat.ofHom
          N13OrdinaryCurveOverlap.overlapEquiv.toRingHom)
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
              N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom) ≫
          Spec.map
            (CommRingCat.ofHom
              N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) =
        𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of AffineOverlap)
    ext z
    simp
  · change
      Spec.map
            (CommRingCat.ofHom
              N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) ≫
          Spec.map
            (CommRingCat.ofHom
              N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom) =
        𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of InfinityOverlap)
    ext z
    simp
  · exact False.elim (h rfl)

/-- Off-diagonal gluing data for the ordinary model. -/
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

/-- The full ordinary two-chart scheme gluing datum. -/
def glueData : Scheme.GlueData where
  toGlueData :=
    CategoryTheory.GlueData.ofGlueData' glueData'
  f_open := glueData_f'_open

/-- The integral two-chart N13 model. -/
abbrev IntegralCurve : Scheme :=
  glueData.glued

/-- Its canonical affine/infinity open cover. -/
abbrev chartCover : IntegralCurve.OpenCover :=
  glueData.openCover

private abbrev R₂ :=
  N13OrdinaryCurveOverlap.R₂

/-- The coefficient map from the two-adic base into the affine chart. -/
def affineBaseMap : R₂ →+* Affine :=
  (AdjoinRoot.of
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))).comp
      (Polynomial.C : R₂ →+* R₂[X])

/-- The coefficient map from the two-adic base into the infinity chart. -/
def infinityBaseMap : R₂ →+* Infinity :=
  (AdjoinRoot.of
    N13IntegralInfinityChart.infinityCurvePoly).comp
      (Polynomial.C : R₂ →+* R₂[X])

/-- The two chart structure morphisms to the two-adic base. -/
def chartToBase : ∀ i : Bool, chart i ⟶ Spec (.of R₂)
  | false =>
      Spec.map
        (CommRingCat.ofHom
          affineBaseMap)
  | true =>
      Spec.map
        (CommRingCat.ofHom
          infinityBaseMap)

private theorem overlapEquiv_symm_base (r : R₂) :
    N13OrdinaryCurveOverlap.overlapEquiv.symm
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r) =
      N13OrdinaryCurveOverlap.coefficientToAffineOverlap r := by
  rw [N13OrdinaryCurveOverlap.overlapEquiv_symm_apply]
  change
    N13OrdinaryCurveOverlap.infinityOverlapToAffineOverlap
        (algebraMap Infinity InfinityOverlap
          (AdjoinRoot.of
            N13IntegralInfinityChart.infinityCurvePoly
            (Polynomial.C r))) =
      N13OrdinaryCurveOverlap.coefficientToAffineOverlap r
  rw [N13OrdinaryCurveOverlap.infinityOverlapToAffineOverlap_algebraMap]
  rw [N13OrdinaryCurveOverlap.infinityToAffineOverlap_of]
  simp [N13OrdinaryCurveOverlap.infinityCoeffMap]

private theorem overlapEquiv_base (r : R₂) :
    N13OrdinaryCurveOverlap.overlapEquiv
        (N13OrdinaryCurveOverlap.coefficientToAffineOverlap r) =
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r := by
  rw [N13OrdinaryCurveOverlap.overlapEquiv_apply]
  change
    N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap Affine AffineOverlap
          (AdjoinRoot.of
            (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
            (Polynomial.C r))) =
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r
  rw [N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap]
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_of]
  simp [N13OrdinaryCurveOverlap.affineCoeffMap]

private theorem affineOverlap_baseMap_eq :
    CommRingCat.ofHom affineBaseMap ≫
        CommRingCat.ofHom
          (algebraMap Affine AffineOverlap) =
      CommRingCat.ofHom infinityBaseMap ≫
        CommRingCat.ofHom
          (algebraMap Infinity InfinityOverlap) ≫
            CommRingCat.ofHom
              N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom := by
  ext r
  change
    N13OrdinaryCurveOverlap.coefficientToAffineOverlap r =
      N13OrdinaryCurveOverlap.overlapEquiv.symm
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r)
  exact (overlapEquiv_symm_base r).symm

private theorem infinityOverlap_baseMap_eq :
    CommRingCat.ofHom infinityBaseMap ≫
        CommRingCat.ofHom
          (algebraMap Infinity InfinityOverlap) =
      CommRingCat.ofHom affineBaseMap ≫
        CommRingCat.ofHom
          (algebraMap Affine AffineOverlap) ≫
            CommRingCat.ofHom
              N13OrdinaryCurveOverlap.overlapEquiv.toRingHom := by
  ext r
  change
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r =
      N13OrdinaryCurveOverlap.overlapEquiv
        (N13OrdinaryCurveOverlap.coefficientToAffineOverlap r)
  exact (overlapEquiv_base r).symm

private theorem overlapToBase :
    ∀ i j (h : i ≠ j),
      overlapInclusion i j h ≫ chartToBase i =
        transition i j h ≫
          overlapInclusion j i h.symm ≫
            chartToBase j := by
  intro i j h
  cases i <;> cases j
  · exact False.elim (h rfl)
  · change
      Spec.map
            (CommRingCat.ofHom
              (algebraMap Affine AffineOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              affineBaseMap) =
        Spec.map
              (CommRingCat.ofHom
                N13OrdinaryCurveOverlap.overlapEquiv.symm.toRingHom) ≫
            Spec.map
              (CommRingCat.ofHom
                (algebraMap Infinity InfinityOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              infinityBaseMap)
    simpa only [Spec.map_comp, Category.assoc] using
      congrArg Spec.map affineOverlap_baseMap_eq
  · change
      Spec.map
            (CommRingCat.ofHom
              (algebraMap Infinity InfinityOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              infinityBaseMap) =
        Spec.map
              (CommRingCat.ofHom
                N13OrdinaryCurveOverlap.overlapEquiv.toRingHom) ≫
            Spec.map
              (CommRingCat.ofHom
                (algebraMap Affine AffineOverlap)) ≫
          Spec.map
            (CommRingCat.ofHom
              affineBaseMap)
    simpa only [Spec.map_comp, Category.assoc] using
      congrArg Spec.map infinityOverlap_baseMap_eq
  · exact False.elim (h rfl)

/-- The structure morphism of the glued integral curve over the two-adic
base. -/
def toBase : IntegralCurve ⟶ Spec (.of R₂) := by
  fapply Multicoequalizer.desc
  · exact chartToBase
  rintro ⟨i, j⟩
  change
    glueData.f i j ≫ chartToBase i =
      (glueData.t i j ≫ glueData.f j i) ≫
        chartToBase j
  cases i <;> cases j
  · simp
  · simp only [glueData,
      CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',
      glueData']
    convert overlapToBase false true
      (by intro h; contradiction) using 1 <;> simp
  · simp only [glueData,
      CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',
      glueData']
    convert overlapToBase true false
      (by intro h; contradiction) using 1 <;> simp
  · simp

@[simp, reassoc]
theorem ι_toBase (i : Bool) :
    glueData.ι i ≫ toBase = chartToBase i :=
  Multicoequalizer.π_desc _ _ _ _ _

end

end MazurProof.N13IntegralCurveScheme
