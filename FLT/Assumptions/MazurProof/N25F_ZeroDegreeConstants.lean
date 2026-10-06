import FLT.Assumptions.MazurProof.N25F_RiemannRochSpace
import FLT.Assumptions.MazurProof.N25F_BinaryResidueOrder
import FLT.Assumptions.MazurProof.N25F_InfinityResidueFields
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The genuine degree-zero section space is exactly the binary constants.
The proof uses the actual degree-one X point, its binary residue field,
and negative-degree vanishing, without a Riemann--Roch assumption. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ZeroDegreeConstants
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectiveDivisorDegree N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_RiemannRochSpace
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_InfinityResidueFields
open N25F_BinaryResidueOrder
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

private theorem unit_mk0_eq (f : Additive CurveFieldˣ) (hf : (f.toMul : CurveField) ≠ 0) :
    Additive.ofMul (Units.mk0 (f.toMul : CurveField) hf) = f := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem one_mem_fullRiemannRochSpace25Two_zero :
    (1 : CurveField) ∈ fullRiemannRochSpace25Two 0 := by
  refine Or.inr ⟨one_ne_zero, ?_⟩
  intro A
  have h1 : Additive.ofMul (Units.mk0 (1 : CurveField) one_ne_zero) = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  rw [h1, map_zero]
  simp

/-- A nonzero globally regular function cannot vanish at the actual X point:
that would place it in the already vanishing degree-minus-one space. -/
theorem xBoundaryOrder_eq_zero_of_mem_zero (f : Additive CurveFieldˣ)
    (hf : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two 0) :
    xBoundaryOrder f = 0 := by
  classical
  have hb : ∀ A, 0 ≤ projectivePrincipalDivisor f A := by
    rcases hf with hf | ⟨hf0, hb⟩
    · exact (f.toMul.ne_zero hf).elim
    intro A
    simpa only [unit_mk0_eq f hf0, Finsupp.zero_apply, zero_add] using hb A
  have hx := hb (fullBoundaryAtomOfTag .X)
  rw [projectivePrincipalDivisor_apply_X] at hx
  by_contra hne
  have hpos : 0 < xBoundaryOrder f := by omega
  have hD : fullClosedPointGrading25Two.divisorDegree
      (-(Finsupp.single (fullBoundaryAtomOfTag .X) (1 : ℤ))) < 0 := by
    rw [map_neg]
    simp [ClosedPointGrading.divisorDegree]
  have hmem : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two
      (-(Finsupp.single (fullBoundaryAtomOfTag .X) (1 : ℤ))) := by
    refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
    intro A
    rw [unit_mk0_eq f f.toMul.ne_zero]
    by_cases hA : A = fullBoundaryAtomOfTag .X
    · subst A
      simp only [Finsupp.neg_apply, Finsupp.single_eq_same, projectivePrincipalDivisor_apply_X]
      omega
    · simpa [hA, Ne.symm hA] using hb A
  rw [fullRiemannRochSpace25Two_eq_bot_of_degree_neg _ hD, Submodule.mem_bot] at hmem
  exact f.toMul.ne_zero hmem

/-- Every globally regular function on the actual full curve is zero or one. -/
theorem mem_fullRiemannRochSpace25Two_zero_iff (a : CurveField) :
    a ∈ fullRiemannRochSpace25Two 0 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    right
    by_contra ha1
    letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
    letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
    have hx := xBoundaryOrder_eq_zero_of_mem_zero (Additive.ofMul (Units.mk0 a ha0)) ha
    change WithZero.log (Ring.ordFrac XLocalRing a) = 0 at hx
    have hv : Ring.ordFrac XLocalRing a ≠ 0 :=
      ((isUnit_iff_ne_zero.mpr ha0).map (Ring.ordFrac XLocalRing)).ne_zero
    have he := WithZero.exp_log hv
    rw [hx, WithZero.exp_zero] at he
    have hp := log_ordFrac_sub_one_pos xLocalResidueRingEquivF2 a ha1 he.symm
    have hs : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hmem : a - 1 ∈ fullRiemannRochSpace25Two 0 :=
      (fullRiemannRochSpace25Two 0).sub_mem ha one_mem_fullRiemannRochSpace25Two_zero
    have hz := xBoundaryOrder_eq_zero_of_mem_zero (Additive.ofMul (Units.mk0 (a - 1) hs)) hmem
    change WithZero.log (Ring.ordFrac XLocalRing (a - 1)) = 0 at hz
    omega
  · rintro (rfl | rfl)
    · exact (fullRiemannRochSpace25Two 0).zero_mem
    · exact one_mem_fullRiemannRochSpace25Two_zero

/-- The degree-zero section space is the actual one-dimensional constant line. -/
theorem fullRiemannRochSpace25Two_zero_eq_span_one :
    fullRiemannRochSpace25Two 0 = Submodule.span (ZMod 2) ({1} : Set CurveField) := by
  apply le_antisymm
  · intro a ha
    rcases (mem_fullRiemannRochSpace25Two_zero_iff a).mp ha with rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact one_mem_fullRiemannRochSpace25Two_zero

instance fullRiemannRochSpace25Two_zero_finite :
    Module.Finite (ZMod 2) (fullRiemannRochSpace25Two 0) := by
  rw [fullRiemannRochSpace25Two_zero_eq_span_one]
  infer_instance

theorem finrank_fullRiemannRochSpace25Two_zero :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two 0) = 1 := by
  rw [fullRiemannRochSpace25Two_zero_eq_span_one]
  exact finrank_span_singleton one_ne_zero

/-- The full principal map has precisely the actual constant-function kernel;
over F2 the sole nonzero constant is the identity unit. -/
theorem fullPrincipalDivisor_eq_zero_iff (f : Additive CurveFieldˣ) :
    projectivePrincipalDivisor f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hm : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two 0 := by
      refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
      intro A
      rw [unit_mk0_eq f f.toMul.ne_zero, hf]
      simp
    rcases (mem_fullRiemannRochSpace25Two_zero_iff _).mp hm with h0 | h1
    · exact (f.toMul.ne_zero h0).elim
    · apply Additive.toMul.injective
      apply Units.ext
      exact h1
  · rintro rfl
    exact map_zero _

/-- The full principal divisor determines an actual nonzero function uniquely
because the binary field has only one nonzero constant. -/
theorem fullPrincipalDivisor_injective : Function.Injective projectivePrincipalDivisor := by
  intro f g h
  have hz : projectivePrincipalDivisor (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp ((fullPrincipalDivisor_eq_zero_iff _).mp hz)

end MazurProof.N25F_ZeroDegreeConstants
