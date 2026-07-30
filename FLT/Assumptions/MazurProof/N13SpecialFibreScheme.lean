import FLT.Assumptions.MazurProof.N13SpecialCurveOverlap
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

end

end MazurProof.N13SpecialFibreScheme
