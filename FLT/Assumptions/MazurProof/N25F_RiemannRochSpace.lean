import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalAddition
import FLT.Assumptions.MazurProof.N25F_ProjectiveProductFormula
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega

/-! Genuine bounded-pole spaces on the full actual N25 divisor carrier.
Addition follows from the established local order inequality; negative-degree
vanishing follows from the established projective product formula. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_RiemannRochSpace
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalAddition N25F_ProjectiveProductFormula
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- The actual F2-vector space of zero and rational functions whose poles
are bounded by D, using every full closed-point coefficient. -/
def fullRiemannRochSpace25Two (D : ProjectiveDivisor25Two) : Submodule (ZMod 2) CurveField where
  carrier := {f | f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
    0 ≤ D A + projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf)) A}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with hf | ⟨hf0, hf⟩
    · subst f
      simpa only [zero_add] using hg
    rcases hg with hg | ⟨hg0, hg⟩
    · subst g
      simp only [add_zero]
      exact Or.inr ⟨hf0, hf⟩
    by_cases hs : f + g = 0
    · exact Or.inl hs
    refine Or.inr ⟨hs, ?_⟩
    intro A
    have hm := projectivePrincipalDivisor_add_ge_min
      (Additive.ofMul (Units.mk0 f hf0)) (Additive.ofMul (Units.mk0 g hg0))
      (Additive.ofMul (Units.mk0 (f + g) hs)) rfl A
    have hfa := hf A
    have hga := hg A
    have hl : -D A ≤ min
        (projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf0)) A)
        (projectivePrincipalDivisor (Additive.ofMul (Units.mk0 g hg0)) A) :=
      le_min (by omega) (by omega)
    have hfinal := hl.trans hm
    omega
  smul_mem' := by
    intro a f hf
    rcases zmod_two_cases a with rfl | rfl
    · simp only [zero_smul]
      exact Or.inl rfl
    · simpa only [one_smul] using hf

@[simp]
theorem mem_fullRiemannRochSpace25Two (D : ProjectiveDivisor25Two) (f : CurveField) :
    f ∈ fullRiemannRochSpace25Two D ↔ f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
      0 ≤ D A + projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf)) A := Iff.rfl

/-- A nonzero bounded-pole function forces the bounding divisor's degree
to be nonnegative, by the genuine projective product formula. -/
theorem degree_nonneg_of_nonzero_mem (D : ProjectiveDivisor25Two) (f : CurveField)
    (hf : f ∈ fullRiemannRochSpace25Two D) (hne : f ≠ 0) :
    0 ≤ fullClosedPointGrading25Two.divisorDegree D := by
  rcases hf with hf | ⟨hf0, hb⟩
  · exact (hne hf).elim
  have hp := projectivePrincipalDivisor_degree_eq_zero (Additive.ofMul (Units.mk0 f hf0))
  have hd : 0 ≤ fullClosedPointGrading25Two.divisorDegree
      (D + projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf0))) := by
    change 0 ≤ (D + projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf0))).sum
      (fun A m => m * (fullClosedPointGrading25Two.atomDegree A : ℤ))
    apply Finsupp.sum_nonneg'
    intro A
    exact mul_nonneg (by simpa only [Finsupp.add_apply] using hb A) (Nat.cast_nonneg _)
  rw [map_add, hp, add_zero] at hd
  exact hd

/-- The actual Riemann--Roch space of a negative-degree full divisor is zero. -/
theorem fullRiemannRochSpace25Two_eq_bot_of_degree_neg (D : ProjectiveDivisor25Two)
    (hD : fullClosedPointGrading25Two.divisorDegree D < 0) :
    fullRiemannRochSpace25Two D = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hne
  have hp := degree_nonneg_of_nonzero_mem D f hf hne
  exact (not_le.mpr hD) hp

end MazurProof.N25F_RiemannRochSpace
