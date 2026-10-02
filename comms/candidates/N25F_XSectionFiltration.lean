import FLT.Assumptions.MazurProof.N25F_RiemannRochSpace
import FLT.Assumptions.MazurProof.N25F_BinaryResidueCancellation
import FLT.Assumptions.MazurProof.N25F_InfinityResidueFields

/-! The first X-point filtration step on the actual section spaces. The
strict cancellation proof uses the genuine local DVR and its F2 residue field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XSectionFiltration
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_RiemannRochSpace
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_InfinityResidueFields
open N25F_BinaryResidueCancellation
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "XPoint" => fullBoundaryAtomOfTag .X

private theorem unit_mk0_eq (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : CurveField) hf) = f := by
  apply Additive.toMul.injective
  exact Units.ext rfl

/-- Removing the genuine X point gives a subspace of the original section space. -/
theorem fullRiemannRochSpace25Two_sub_X_le (D : ProjectiveDivisor25Two) :
    fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) ≤
      fullRiemannRochSpace25Two D := by
  classical
  intro a ha
  rcases ha with rfl | ⟨ha, hb⟩
  · exact (fullRiemannRochSpace25Two D).zero_mem
  refine Or.inr ⟨ha, ?_⟩
  intro A
  have h := hb A
  by_cases hA : A = XPoint
  · subst A
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same] at h
    omega
  · simpa [hA, Ne.symm hA] using h

/-- Membership in the next X filtration step is exactly strict improvement
of the allowed X order, once the other pole bounds already hold. -/
theorem mem_fullRiemannRochSpace25Two_sub_X_iff (D : ProjectiveDivisor25Two)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two D) :
    (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) ↔
      -D XPoint < xBoundaryOrder f := by
  classical
  have hb : ∀ A, 0 ≤ D A + projectivePrincipalDivisor f A := by
    rcases hf with h | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero h).elim
    simpa only [unit_mk0_eq f hf0] using hb
  constructor
  · intro hs
    rcases hs with h | ⟨hf0, hs⟩
    · exact (f.toMul.ne_zero h).elim
    have hx := hs XPoint
    rw [unit_mk0_eq f hf0, Finsupp.sub_apply, Finsupp.single_eq_same,
      projectivePrincipalDivisor_apply_X] at hx
    omega
  · intro hx
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = XPoint
    · subst A
      rw [Finsupp.sub_apply, Finsupp.single_eq_same, projectivePrincipalDivisor_apply_X]
      omega
    · simpa [hA, Ne.symm hA] using hb A

/-- A section outside the next step has exactly the extremal allowed X order. -/
theorem xBoundaryOrder_eq_neg_of_not_mem_sub_X (D : ProjectiveDivisor25Two)
    (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two D)
    (hnot : (f.toMul : CurveField) ∉
      fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)) :
    xBoundaryOrder f = -D XPoint := by
  have hn := mt (mem_fullRiemannRochSpace25Two_sub_X_iff D f hf).mpr hnot
  rcases hf with h | ⟨hf0, hb⟩
  · exact (f.toMul.ne_zero h).elim
  have hx := hb XPoint
  rw [unit_mk0_eq f hf0, projectivePrincipalDivisor_apply_X] at hx
  omega

/-- All sections outside L(D-X) have the same nonzero leading coefficient:
their difference lies in L(D-X), by the actual binary residue calculation. -/
theorem sub_mem_fullRiemannRochSpace25Two_sub_X (D : ProjectiveDivisor25Two)
    (a b : CurveField) (ha : a ∈ fullRiemannRochSpace25Two D)
    (hb : b ∈ fullRiemannRochSpace25Two D)
    (hanot : a ∉ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1))
    (hbnot : b ∉ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)) :
    a - b ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) := by
  by_cases hab : a = b
  · rw [hab, sub_self]
    exact (fullRiemannRochSpace25Two _).zero_mem
  have ha0 : a ≠ 0 := by
    intro h
    apply hanot
    rw [h]
    exact (fullRiemannRochSpace25Two _).zero_mem
  have hb0 : b ≠ 0 := by
    intro h
    apply hbnot
    rw [h]
    exact (fullRiemannRochSpace25Two _).zero_mem
  have hxa := xBoundaryOrder_eq_neg_of_not_mem_sub_X D (Additive.ofMul (Units.mk0 a ha0)) ha hanot
  have hxb := xBoundaryOrder_eq_neg_of_not_mem_sub_X D (Additive.ofMul (Units.mk0 b hb0)) hb hbnot
  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
  have hp := log_ordFrac_sub_gt_of_log_eq xLocalResidueRingEquivF2 a b ha0 hb0 hab
    (hxa.trans hxb.symm)
  have hs : a - b ≠ 0 := sub_ne_zero.mpr hab
  apply (mem_fullRiemannRochSpace25Two_sub_X_iff D
    (Additive.ofMul (Units.mk0 (a - b) hs)) ((fullRiemannRochSpace25Two D).sub_mem ha hb)).mpr
  change -D XPoint < WithZero.log (Ring.ordFrac XLocalRing (a - b))
  change WithZero.log (Ring.ordFrac XLocalRing b) = -D XPoint at hxb
  omega

end MazurProof.N25F_XSectionFiltration
