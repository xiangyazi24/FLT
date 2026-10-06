import FLT.Assumptions.MazurProof.N25F_SectionClassFiber
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Multiplication by the actual principal representative transports sections
between linearly equivalent full divisors. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SectionPrincipalTransport
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_RiemannRochSpace N25F_SectionFiniteness N25F_FullPicardDegree
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The actual principal relation controls multiplication of bounded-pole functions. -/
theorem mul_mem_fullRiemannRochSpace25Two (D E : ProjectiveDivisor25Two)
    (f : Additive CurveFieldˣ) (hdiv : projectivePrincipalDivisor f = D - E)
    (a : CurveField) (ha : a ∈ fullRiemannRochSpace25Two D) :
    (f.toMul : CurveField) * a ∈ fullRiemannRochSpace25Two E := by
  rcases ha with rfl | ⟨ha, hbound⟩
  · exact Or.inl (mul_zero _)
  have hfa : (f.toMul : CurveField) * a ≠ 0 := mul_ne_zero (Units.ne_zero _) ha
  refine Or.inr ⟨hfa, ?_⟩
  have hunit : Additive.ofMul (Units.mk0 ((f.toMul : CurveField) * a) hfa) =
      f + Additive.ofMul (Units.mk0 a ha) := by
    change Units.mk0 ((f.toMul : CurveField) * a) hfa = f.toMul * Units.mk0 a ha
    exact Units.ext rfl
  intro A
  rw [hunit, map_add]
  have hA := congrArg (fun H : ProjectiveDivisor25Two => H A) hdiv
  simp only [Finsupp.sub_apply] at hA
  have hb := hbound A
  change 0 ≤ E A + (projectivePrincipalDivisor f A +
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 a ha)) A)
  omega

/-- Multiplication by an actual nonzero function is a linear equivalence of its section spaces. -/
def principalSectionLinearEquiv25Two (D E : ProjectiveDivisor25Two)
    (f : Additive CurveFieldˣ) (hdiv : projectivePrincipalDivisor f = D - E) :
    fullRiemannRochSpace25Two D ≃ₗ[ZMod 2] fullRiemannRochSpace25Two E where
  toFun a := ⟨(f.toMul : CurveField) * a.1,
    mul_mem_fullRiemannRochSpace25Two D E f hdiv a.1 a.2⟩
  invFun a := ⟨((-f).toMul : CurveField) * a.1,
    mul_mem_fullRiemannRochSpace25Two E D (-f)
      (by rw [map_neg, hdiv, neg_sub]) a.1 a.2⟩
  left_inv a := by
    apply Subtype.ext
    change (↑f.toMul⁻¹ : CurveField) * ((f.toMul : CurveField) * a.1) = a.1
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv a := by
    apply Subtype.ext
    change (f.toMul : CurveField) * ((↑f.toMul⁻¹ : CurveField) * a.1) = a.1
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' r a := by
    apply Subtype.ext
    exact mul_smul_comm _ _ _

/-- The actual section dimension depends only on the full divisor class. -/
theorem finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq
    (D E : ProjectiveDivisor25Two)
    (h : fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D =
      fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two E) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) := by
  obtain ⟨f, hf⟩ := (fullProjectiveClassOf_eq_iff_exists_principal D E).mp h
  exact (principalSectionLinearEquiv25Two D E f hf).finrank_eq

/-- The genuine section rank descended to the full divisor-class quotient. -/
def fullClassSectionRank25Two :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two → ℕ :=
  Quotient.lift (fun D => Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D))
    (fun D E h => finrank_fullRiemannRochSpace25Two_eq_of_classOf_eq D E (Quotient.sound h))

@[simp]
theorem fullClassSectionRank25Two_classOf (D : ProjectiveDivisor25Two) :
    fullClassSectionRank25Two
      (fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) := rfl

end MazurProof.N25F_SectionPrincipalTransport
