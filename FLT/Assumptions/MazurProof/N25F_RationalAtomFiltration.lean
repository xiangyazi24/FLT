import FLT.Assumptions.MazurProof.N25F_BoundarySectionFiltration
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalAddition
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# One rational point costs at most one section

For every closed point `A₀` of degree one on the N25 curve (boundary or not)
and every divisor `D`, `ℓ(D) ≤ ℓ(D - A₀) + 1`.  The residue field at `A₀` is
`F₂`, so two functions with the same order at `A₀` have a difference of
strictly larger order; this is the boundary argument of
`N25F_BoundarySectionFiltration`, now also run in the localisation of the
affine W-chart at a height-one prime of residue degree one.
-/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_RationalAtomFiltration
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients
open N25F_RiemannRochSpace N25F_SectionFiniteness N25F_SectionMultiplication
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_InfinityResidueFields N25F_BinaryResidueCancellation
open N25F_NonBoundaryPrincipalDivisor N25F_PrincipalOrderAddition
open N25F_BoundarySectionFiltration
open RationalPointsN25QuotientTwoClosedPointPartition
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- Equal-order leading terms cancel at every closed point of degree one. -/
theorem atom_principal_sub_gt_of_eq (A₀ : fullClosedPointGrading25Two.Atom)
    (hA₀ : fullClosedPointGrading25Two.atomDegree A₀ = 1)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 a ha)) A₀ =
      projectivePrincipalDivisor (Additive.ofMul (Units.mk0 b hb)) A₀) :
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 b hb)) A₀ <
      projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (a - b) (sub_ne_zero.mpr hab)))
        A₀ := by
  obtain ⟨s, rfl⟩ := boundaryNonBoundaryToFullAtom_surjective A₀
  cases s with
  | inl t => exact boundary_principal_sub_gt_of_eq t a b ha hb hab h
  | inr B =>
      simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_nonBoundary,
        nonBoundaryPrincipalDivisor_apply] at h ⊢
      let v := fullNonBoundaryAtomEquivHeightOne B
      letI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ v.ne_bot
          (Localization.AtPrime v.asIdeal)
      change FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ a) =
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ b) at h
      change FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ b) <
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton W⁰ (a - b))
      rw [count_spanSingleton_eq_log_ordFrac v a ha,
        count_spanSingleton_eq_log_ordFrac v b hb] at h
      rw [count_spanSingleton_eq_log_ordFrac v b hb,
        count_spanSingleton_eq_log_ordFrac v (a - b) (sub_ne_zero.mpr hab)]
      have hcard : Nat.card (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) = 2 := by
        have hmax : v.asIdeal.IsMaximal := IsDedekindDomain.HeightOneSpectrum.isMaximal v
        have h1 := fullNonBoundaryPrimeIdeal_residue_card B
        change Nat.card (W ⧸ fullNonBoundaryPrimeIdeal B) =
          2 ^ fullClosedPointGrading25Two.atomDegree (boundaryNonBoundaryToFullAtom (.inr B)) at h1
        rw [hA₀, pow_one] at h1
        exact (Nat.card_congr (Equiv.ofBijective _
          (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal))).symm.trans h1
      have hfin : Finite (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      letI := Fintype.ofFinite (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))
      have e := (ZMod.ringEquivOfPrime
        (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) Nat.prime_two
        (by rw [← Nat.card_eq_fintype_card, hcard])).symm
      exact log_ordFrac_sub_gt_of_log_eq e a b ha hb hab h

private theorem unit_mk0_eq' (f : Additive Kˣ) (hf : (f.toMul : K) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : K) hf) = f := by
  apply Additive.toMul.injective
  exact Units.ext rfl

theorem fullRiemannRochSpace25Two_sub_atom_le (D : ProjectiveDivisor25Two)
    (A₀ : fullClosedPointGrading25Two.Atom) :
    fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1) ≤
      fullRiemannRochSpace25Two D := by
  classical
  apply fullRiemannRochSpace25Two_mono
  intro A
  by_cases hA : A = A₀
  · subst A
    simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
    omega
  · simp [hA]

theorem mem_fullRiemannRochSpace25Two_sub_atom_iff (D : ProjectiveDivisor25Two)
    (A₀ : fullClosedPointGrading25Two.Atom)
    (_hA₀ : fullClosedPointGrading25Two.atomDegree A₀ = 1)
    (f : Additive Kˣ)
    (hf : (f.toMul : K) ∈ fullRiemannRochSpace25Two D) :
    (f.toMul : K) ∈ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1) ↔
      -D (A₀) < projectivePrincipalDivisor f (A₀) := by
  classical
  have hb : ∀ A, 0 ≤ D A + projectivePrincipalDivisor f A := by
    rcases hf with h | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero h).elim
    simpa only [unit_mk0_eq' f hf0] using hb
  constructor
  · intro hs
    rcases hs with h | ⟨hf0, hs⟩
    · exact (f.toMul.ne_zero h).elim
    have hp := hs (A₀)
    rw [unit_mk0_eq' f hf0, Finsupp.sub_apply, Finsupp.single_eq_same] at hp
    omega
  · intro hp
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq' f f.toMul.ne_zero]
    by_cases hA : A = A₀
    · subst A
      rw [Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · simpa [hA, Ne.symm hA] using hb A

theorem atom_principal_eq_neg_of_not_mem (D : ProjectiveDivisor25Two)
    (A₀ : fullClosedPointGrading25Two.Atom)
    (hA₀ : fullClosedPointGrading25Two.atomDegree A₀ = 1)
    (f : Additive Kˣ)
    (hf : (f.toMul : K) ∈ fullRiemannRochSpace25Two D)
    (hnot : (f.toMul : K) ∉ fullRiemannRochSpace25Two
      (D - Finsupp.single (A₀) 1)) :
    projectivePrincipalDivisor f (A₀) = -D (A₀) := by
  have hn := mt (mem_fullRiemannRochSpace25Two_sub_atom_iff D A₀ hA₀ f hf).mpr hnot
  rcases hf with h | ⟨hf0, hb⟩
  · exact (f.toMul.ne_zero h).elim
  have hp := hb (A₀)
  rw [unit_mk0_eq' f hf0] at hp
  omega

theorem sub_mem_fullRiemannRochSpace25Two_sub_atom (D : ProjectiveDivisor25Two)
    (A₀ : fullClosedPointGrading25Two.Atom)
    (hA₀ : fullClosedPointGrading25Two.atomDegree A₀ = 1)
    (a b : K) (ha : a ∈ fullRiemannRochSpace25Two D)
    (hb : b ∈ fullRiemannRochSpace25Two D)
    (hanot : a ∉ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1))
    (hbnot : b ∉ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1)) :
    a - b ∈ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1) := by
  by_cases hab : a = b
  · rw [hab, sub_self]
    exact (fullRiemannRochSpace25Two _).zero_mem
  have ha0 : a ≠ 0 := by
    intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have hb0 : b ≠ 0 := by
    intro h; apply hbnot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have hpa := atom_principal_eq_neg_of_not_mem D A₀ hA₀
    (Additive.ofMul (Units.mk0 a ha0)) ha hanot
  have hpb := atom_principal_eq_neg_of_not_mem D A₀ hA₀
    (Additive.ofMul (Units.mk0 b hb0)) hb hbnot
  have hp := atom_principal_sub_gt_of_eq A₀ hA₀ a b ha0 hb0 hab (hpa.trans hpb.symm)
  apply (mem_fullRiemannRochSpace25Two_sub_atom_iff D A₀ hA₀
    (Additive.ofMul (Units.mk0 (a - b) (sub_ne_zero.mpr hab)))
    ((fullRiemannRochSpace25Two D).sub_mem ha hb)).mpr
  omega

/-- Vanishing at one more rational point costs at most one dimension. -/
theorem finrank_fullRiemannRochSpace25Two_le_sub_atom_add_one
    (D : ProjectiveDivisor25Two) (A₀ : fullClosedPointGrading25Two.Atom)
    (hA₀ : fullClosedPointGrading25Two.atomDegree A₀ = 1) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
      Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1)) + 1 := by
  by_cases hle : fullRiemannRochSpace25Two D ≤
      fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1)
  · exact (Submodule.finrank_mono hle).trans (Nat.le_add_right _ _)
  obtain ⟨a, ha, hanot⟩ := SetLike.not_le_iff_exists.mp hle
  have ha0 : a ≠ 0 := by
    intro h; apply hanot; rw [h]; exact (fullRiemannRochSpace25Two _).zero_mem
  have he : fullRiemannRochSpace25Two D =
      fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1) ⊔
        Submodule.span (ZMod 2) ({a} : Set K) := by
    apply le_antisymm
    · intro b hb
      by_cases hbn : b ∈ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1)
      · exact Submodule.mem_sup_left hbn
      have hba := sub_mem_fullRiemannRochSpace25Two_sub_atom D A₀ hA₀ b a hb ha hbn hanot
      have haS : a ∈ fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1) ⊔
          Submodule.span (ZMod 2) ({a} : Set K) :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton a))
      simpa only [sub_add_cancel] using (Submodule.add_mem _ (Submodule.mem_sup_left hba) haS)
    · refine sup_le (fullRiemannRochSpace25Two_sub_atom_le D A₀) ?_
      apply Submodule.span_le.mpr
      intro b hb
      have hba : b = a := Set.mem_singleton_iff.mp hb
      subst b
      exact ha
  rw [he]
  simpa only [finrank_span_singleton ha0] using
    (Submodule.finrank_add_le_finrank_add_finrank
      (fullRiemannRochSpace25Two (D - Finsupp.single (A₀) 1))
      (Submodule.span (ZMod 2) ({a} : Set K)))

end MazurProof.N25F_RationalAtomFiltration
