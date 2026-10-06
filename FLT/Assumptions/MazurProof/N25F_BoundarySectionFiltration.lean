import FLT.Assumptions.MazurProof.N25F_BinaryResidueCancellation
import FLT.Assumptions.MazurProof.N25F_InfinityResidueFields
import FLT.Assumptions.MazurProof.N25F_SectionMultiplication
import FLT.Assumptions.MazurProof.N25F_SectionFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The genuine binary residue filtrations at all three boundary points. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_BoundarySectionFiltration
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_ProjectivePrincipalCoefficients
open N25F_RiemannRochSpace N25F_SectionFiniteness N25F_SectionMultiplication
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_InfinityResidueFields N25F_BinaryResidueCancellation
open RationalPointsN25QuotientTwoClosedPointPartition
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- Equal-order leading terms cancel at each of the three actual binary residue fields. -/
theorem boundary_principal_sub_gt_of_eq (t : FullBoundaryTag25Two)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 a ha)) (fullBoundaryAtomOfTag t) =
      projectivePrincipalDivisor (Additive.ofMul (Units.mk0 b hb)) (fullBoundaryAtomOfTag t)) :
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 b hb)) (fullBoundaryAtomOfTag t) <
      projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (a - b) (sub_ne_zero.mpr hab)))
        (fullBoundaryAtomOfTag t) := by
  cases t with
  | X =>
      rw [projectivePrincipalDivisor_apply_X, projectivePrincipalDivisor_apply_X] at h ⊢
      letI : Algebra XLocalRing K := xLocalToFraction.toRingHom.toAlgebra
      letI : IsFractionRing XLocalRing K := xLocalToFraction_isFractionRing
      exact log_ordFrac_sub_gt_of_log_eq xLocalResidueRingEquivF2 a b ha hb hab h
  | YZ =>
      rw [projectivePrincipalDivisor_apply_YZ, projectivePrincipalDivisor_apply_YZ] at h ⊢
      letI : Algebra YZLocalRing K := yzLocalToFraction.toRingHom.toAlgebra
      letI : IsFractionRing YZLocalRing K := yzLocalToFraction_isFractionRing
      exact log_ordFrac_sub_gt_of_log_eq yzLocalResidueRingEquivF2 a b ha hb hab h
  | Z =>
      rw [projectivePrincipalDivisor_apply_Z, projectivePrincipalDivisor_apply_Z] at h ⊢
      letI : Algebra ZLocalRing K := zLocalToFraction.toRingHom.toAlgebra
      letI : IsFractionRing ZLocalRing K := zLocalToFraction_isFractionRing
      exact log_ordFrac_sub_gt_of_log_eq zLocalResidueRingEquivF2 a b ha hb hab h

private theorem unit_mk0_eq (f : Additive Kˣ) (hf : (f.toMul : K) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : K) hf) = f := by
  apply Additive.toMul.injective
  exact Units.ext rfl

theorem fullRiemannRochSpace25Two_sub_boundary_le (D : ProjectiveDivisor25Two) (t : FullBoundaryTag25Two) :
    fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1) ≤
      fullRiemannRochSpace25Two D := by
  classical
  apply fullRiemannRochSpace25Two_mono
  intro A
  by_cases hA : A = fullBoundaryAtomOfTag t
  · subst A
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
    omega
  · simp [hA, Ne.symm hA]

theorem mem_fullRiemannRochSpace25Two_sub_boundary_iff (D : ProjectiveDivisor25Two)
    (t : FullBoundaryTag25Two) (f : Additive Kˣ)
    (hf : (f.toMul : K) ∈ fullRiemannRochSpace25Two D) :
    (f.toMul : K) ∈ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1) ↔
      -D (fullBoundaryAtomOfTag t) < projectivePrincipalDivisor f (fullBoundaryAtomOfTag t) := by
  classical
  have hb : ∀ A, 0 ≤ D A + projectivePrincipalDivisor f A := by
    rcases hf with h | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero h).elim
    simpa only [unit_mk0_eq f hf0] using hb
  constructor
  · intro hs
    rcases hs with h | ⟨hf0, hs⟩
    · exact (f.toMul.ne_zero h).elim
    have hp := hs (fullBoundaryAtomOfTag t)
    rw [unit_mk0_eq f hf0, Finsupp.sub_apply, Finsupp.single_eq_same] at hp
    omega
  · intro hp
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = fullBoundaryAtomOfTag t
    · subst A
      rw [Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · simpa [hA, Ne.symm hA] using hb A

theorem boundary_principal_eq_neg_of_not_mem (D : ProjectiveDivisor25Two)
    (t : FullBoundaryTag25Two) (f : Additive Kˣ)
    (hf : (f.toMul : K) ∈ fullRiemannRochSpace25Two D)
    (hnot : (f.toMul : K) ∉ fullRiemannRochSpace25Two
      (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)) :
    projectivePrincipalDivisor f (fullBoundaryAtomOfTag t) = -D (fullBoundaryAtomOfTag t) := by
  have hn := mt (mem_fullRiemannRochSpace25Two_sub_boundary_iff D t f hf).mpr hnot
  rcases hf with h | ⟨hf0, hb⟩
  · exact (f.toMul.ne_zero h).elim
  have hp := hb (fullBoundaryAtomOfTag t)
  rw [unit_mk0_eq f hf0] at hp
  omega

theorem sub_mem_fullRiemannRochSpace25Two_sub_boundary (D : ProjectiveDivisor25Two)
    (t : FullBoundaryTag25Two) (a b : K) (ha : a ∈ fullRiemannRochSpace25Two D)
    (hb : b ∈ fullRiemannRochSpace25Two D)
    (hanot : a ∉ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1))
    (hbnot : b ∉ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)) :
    a - b ∈ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1) := by
  by_cases hab : a = b
  · rw [hab, sub_self]
    exact (fullRiemannRochSpace25Two _).zero_mem
  have ha0 : a ≠ 0 := by intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have hb0 : b ≠ 0 := by intro h; apply hbnot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have hpa := boundary_principal_eq_neg_of_not_mem D t (Additive.ofMul (Units.mk0 a ha0)) ha hanot
  have hpb := boundary_principal_eq_neg_of_not_mem D t (Additive.ofMul (Units.mk0 b hb0)) hb hbnot
  have hp := boundary_principal_sub_gt_of_eq t a b ha0 hb0 hab (hpa.trans hpb.symm)
  apply (mem_fullRiemannRochSpace25Two_sub_boundary_iff D t
    (Additive.ofMul (Units.mk0 (a - b) (sub_ne_zero.mpr hab)))
    ((fullRiemannRochSpace25Two D).sub_mem ha hb)).mpr
  omega

/-- Each actual binary boundary condition costs at most one dimension. -/
theorem finrank_fullRiemannRochSpace25Two_le_sub_boundary_add_one
    (D : ProjectiveDivisor25Two) (t : FullBoundaryTag25Two) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)) + 1 := by
  by_cases hle : fullRiemannRochSpace25Two D ≤
      fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)
  · exact (Submodule.finrank_mono hle).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, hanot⟩ := SetLike.not_le_iff_exists.mp hle
  have ha0 : a ≠ 0 := by intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have he : fullRiemannRochSpace25Two D =
      fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set K) := by
    apply le_antisymm
    · intro b hb
      by_cases hbn : b ∈ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)
      · exact Submodule.mem_sup_left hbn
      have hba := sub_mem_fullRiemannRochSpace25Two_sub_boundary D t b a hb ha hbn hanot
      have haS : a ∈ fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1) ⊔
          Submodule.span (ZMod 2) ({a} : Set K) :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton a))
      simpa only [sub_add_cancel] using (Submodule.add_mem _ (Submodule.mem_sup_left hba) haS)
    · refine sup_le (fullRiemannRochSpace25Two_sub_boundary_le D t) ?_
      apply Submodule.span_le.mpr
      intro b hb
      have hba : b = a := Set.mem_singleton_iff.mp hb
      subst b
      exact ha
  rw [he]
  simpa only [finrank_span_singleton ha0] using
    (Submodule.finrank_add_le_finrank_add_finrank
      (fullRiemannRochSpace25Two (D - Finsupp.single (fullBoundaryAtomOfTag t) 1))
      (Submodule.span (ZMod 2) ({a} : Set K)))

/-- A multiplicity-k constraint at any of the three actual boundary points costs at most k. -/
theorem finrank_fullRiemannRochSpace25Two_le_sub_boundary_multiple
    (D : ProjectiveDivisor25Two) (t : FullBoundaryTag25Two) (k : ℕ) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two
        (D - (k : ℤ) • Finsupp.single (fullBoundaryAtomOfTag t) 1)) + k := by
  induction k generalizing D with
  | zero =>
      have hz : ((0 : ℕ) : ℤ) • Finsupp.single (fullBoundaryAtomOfTag t) (1 : ℤ) = 0 := by
        ext A
        simp [Finsupp.smul_apply]
      rw [hz, sub_zero, add_zero]
  | succ k ih =>
      have hstep := finrank_fullRiemannRochSpace25Two_le_sub_boundary_add_one D t
      have hrec := ih (D - Finsupp.single (fullBoundaryAtomOfTag t) 1)
      have he : Finsupp.single (fullBoundaryAtomOfTag t) (1 : ℤ) +
          (k : ℤ) • Finsupp.single (fullBoundaryAtomOfTag t) 1 =
          ((k + 1 : ℕ) : ℤ) • Finsupp.single (fullBoundaryAtomOfTag t) 1 := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]
      rw [sub_sub, he] at hrec
      omega

end MazurProof.N25F_BoundarySectionFiltration
