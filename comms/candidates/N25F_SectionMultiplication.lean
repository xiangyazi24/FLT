import FLT.Assumptions.MazurProof.N25F_RiemannRochSpace

/-! Monotonicity and multiplication for the actual bounded-pole submodules. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SectionMultiplication
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_RiemannRochSpace
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

theorem fullRiemannRochSpace25Two_mono (D E : ProjectiveDivisor25Two)
    (hDE : ∀ A, D A ≤ E A) : fullRiemannRochSpace25Two D ≤ fullRiemannRochSpace25Two E := by
  intro a ha
  rcases ha with rfl | ⟨ha, hb⟩
  · exact (fullRiemannRochSpace25Two E).zero_mem
  refine Or.inr ⟨ha, ?_⟩
  intro A
  have h1 := hDE A
  have h2 := hb A
  omega

/-- Orders add under multiplication of actual rational functions. -/
theorem mul_mem_fullRiemannRochSpace25Two (D E : ProjectiveDivisor25Two)
    (a b : K) (ha : a ∈ fullRiemannRochSpace25Two D) (hb : b ∈ fullRiemannRochSpace25Two E) :
    a * b ∈ fullRiemannRochSpace25Two (D + E) := by
  rcases ha with rfl | ⟨ha, hA⟩
  · rw [zero_mul]
    exact (fullRiemannRochSpace25Two _).zero_mem
  rcases hb with rfl | ⟨hb, hB⟩
  · rw [mul_zero]
    exact (fullRiemannRochSpace25Two _).zero_mem
  refine Or.inr ⟨mul_ne_zero ha hb, ?_⟩
  have hu : Additive.ofMul (Units.mk0 (a * b) (mul_ne_zero ha hb)) =
      Additive.ofMul (Units.mk0 a ha) + Additive.ofMul (Units.mk0 b hb) := by
    apply Additive.toMul.injective
    exact Units.ext rfl
  intro A
  rw [hu, map_add]
  simp only [Finsupp.add_apply]
  have h1 := hA A
  have h2 := hB A
  omega

end MazurProof.N25F_SectionMultiplication
