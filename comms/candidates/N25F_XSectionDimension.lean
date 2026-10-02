import FLT.Assumptions.MazurProof.N25F_XSectionFiltration
import FLT.Assumptions.MazurProof.N25F_SectionFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The genuine X-point filtration changes section dimension by at most one. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XSectionDimension
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_SectionFiniteness
open N25F_ProjectiveDivisorDegree
open N25F_XSectionFiltration
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "XPoint" => fullBoundaryAtomOfTag .X

/-- Any section at the extremal X order spans the single possible new direction. -/
theorem fullRiemannRochSpace25Two_eq_sub_X_sup_span (D : ProjectiveDivisor25Two)
    (a : CurveField) (ha : a ∈ fullRiemannRochSpace25Two D)
    (hanot : a ∉ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)) :
    fullRiemannRochSpace25Two D =
      fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set CurveField) := by
  apply le_antisymm
  · intro b hb
    by_cases hbn : b ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)
    · exact Submodule.mem_sup_left hbn
    have hba := sub_mem_fullRiemannRochSpace25Two_sub_X D b a hb ha hbn hanot
    have haS : a ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set CurveField) :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton a))
    simpa only [sub_add_cancel] using
      (Submodule.add_mem _ (Submodule.mem_sup_left hba) haS)
  · refine sup_le (fullRiemannRochSpace25Two_sub_X_le D) ?_
    apply Submodule.span_le.mpr
    intro b hb
    have hba : b = a := Set.mem_singleton_iff.mp hb
    subst b
    exact ha

/-- Removing the actual degree-one X point loses at most one independent section. -/
theorem finrank_fullRiemannRochSpace25Two_le_sub_X_add_one (D : ProjectiveDivisor25Two) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)) + 1 := by
  by_cases hle : fullRiemannRochSpace25Two D ≤
      fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)
  · exact (Submodule.finrank_mono hle).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, hanot⟩ := SetLike.not_le_iff_exists.mp hle
  have ha0 : a ≠ 0 := by
    intro h
    apply hanot
    rw [h]
    exact (fullRiemannRochSpace25Two _).zero_mem
  rw [fullRiemannRochSpace25Two_eq_sub_X_sup_span D a ha hanot]
  simpa only [finrank_span_singleton ha0] using
    (Submodule.finrank_add_le_finrank_add_finrank
      (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1))
      (Submodule.span (ZMod 2) ({a} : Set CurveField)))

/-- The actual elementary upper bound follows by successively removing X,
ending in the already proved negative-degree zero space. -/
theorem finrank_fullRiemannRochSpace25Two_le_degree_add_one (D : ProjectiveDivisor25Two) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      (fullClosedPointGrading25Two.divisorDegree D + 1).toNat := by
  classical
  have hX : fullClosedPointGrading25Two.divisorDegree (Finsupp.single XPoint 1) = 1 := by
    simp [ClosedPointGrading.divisorDegree]
  have hbound : ∀ n : ℕ, ∀ E : ProjectiveDivisor25Two,
      fullClosedPointGrading25Two.divisorDegree E ≤ n →
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) ≤ n + 1 := by
    intro n
    induction n with
    | zero =>
        intro E hE
        have hneg : fullClosedPointGrading25Two.divisorDegree
            (E - Finsupp.single XPoint 1) < 0 := by
          rw [map_sub, hX]
          omega
        have hstep := finrank_fullRiemannRochSpace25Two_le_sub_X_add_one E
        rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg _ hneg,
          finrank_bot] at hstep
        exact hstep
    | succ n ih =>
        intro E hE
        have hsmall : fullClosedPointGrading25Two.divisorDegree
            (E - Finsupp.single XPoint 1) ≤ n := by
          rw [map_sub, hX]
          omega
        exact (finrank_fullRiemannRochSpace25Two_le_sub_X_add_one E).trans
          (Nat.add_le_add_right (ih _ hsmall) 1)
  by_cases hneg : fullClosedPointGrading25Two.divisorDegree D < 0
  · rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg D hneg, finrank_bot]
    exact Nat.zero_le _
  have h := hbound (fullClosedPointGrading25Two.divisorDegree D).toNat D (by omega)
  have he : (fullClosedPointGrading25Two.divisorDegree D + 1).toNat =
      (fullClosedPointGrading25Two.divisorDegree D).toNat + 1 := by omega
  rwa [he]

/-- The actual quotient by the next X filtration step has dimension at most one. -/
theorem finrank_fullRiemannRochSpace25Two_X_quotient_le_one (D : ProjectiveDivisor25Two) :
    Module.finrank (ZMod 2)
      ((fullRiemannRochSpace25Two D) ⧸
        (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)).submoduleOf
          (fullRiemannRochSpace25Two D)) ≤ 1 := by
  let P := (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)).submoduleOf
    (fullRiemannRochSpace25Two D)
  have he : Module.finrank (ZMod 2) P =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)) :=
    (Submodule.submoduleOfEquivOfLe (fullRiemannRochSpace25Two_sub_X_le D)).finrank_eq
  have hsum := P.finrank_quotient_add_finrank
  rw [he] at hsum
  have hstep := finrank_fullRiemannRochSpace25Two_le_sub_X_add_one D
  change Module.finrank (ZMod 2) ((fullRiemannRochSpace25Two D) ⧸ P) ≤ 1
  omega

end MazurProof.N25F_XSectionDimension
