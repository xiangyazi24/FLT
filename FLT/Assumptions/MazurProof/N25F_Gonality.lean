import FLT.Assumptions.MazurProof.N25F_AtomFrobeniusOrder
import FLT.Assumptions.MazurProof.N25F_GhostDegreeBound
import FLT.Assumptions.MazurProof.N25F_ZeroDegreeConstants
import FLT.Assumptions.MazurProof.N25F_SectionMultiplication
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoMiddleRiemannRoch

/-!
# The N25 curve has no functions with at most two poles

Let `E` be an effective divisor of degree at most two on the genus-four N25
quotient curve over `F₂`.  Then `L(E)` consists of the constants only.

The proof is a point count and uses no Riemann–Roch input.  Suppose
`f ∈ L(E)` and `g = f ^ 8 - f ≠ 0`.  Put `F = div g + 9E`.  At a pole of `f`,
`ord g = 8 ord f`, so `F ≥ 8(ord f + E) + E ≥ E > 0` there; where `f` is regular,
`g` is regular, and at a closed point of degree one or three `g` vanishes
because the residue field is `F₂` or `F₈`.  So `F` is effective and positive at
each of the closed points of degree dividing three, whose degrees add up to
the `F₈`-point count `20`.  Hence `20 ≤ deg F = 9 deg E ≤ 18`, which is absurd.
Therefore `f ^ 8 = f`, so `8 · div f = div f`, `div f = 0`, and `f` is a
constant.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_Gonality
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_ProjectiveProductFormula
open N25F_RiemannRochSpace N25F_ZeroDegreeConstants N25F_SectionMultiplication
open N25F_AtomFrobeniusOrder N25F_GhostDegreeBound
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The closed points of degree one and three have total degree `20`. -/
theorem ghostCount_three_eq :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount fullClosedPointGrading25Two 3 = 20 :=
  RationalPointsN25QuotientMiddleRiemannRoch.ClosedPointBridge25TwoLE4.ghostCount_three
    fullClosedPointBridge25TwoLE4 |>.trans
    RationalPointsN25QuotientMiddleRiemannRoch.extensionPointCount25Two_three

/-- A nonzero function with `f ^ 8 = f` has trivial divisor. -/
private theorem principal_eq_zero_of_pow_eight (f : CurveField) (hf : f ≠ 0) (h8 : f ^ 8 = f)
    (A : fullClosedPointGrading25Two.Atom) :
    projectivePrincipalDivisor (Additive.ofMul (Units.mk0 f hf)) A = 0 := by
  have hu : (Units.mk0 f hf) ^ 8 = Units.mk0 f hf := Units.ext (by simpa using h8)
  have hadd : (8 : ℕ) • Additive.ofMul (Units.mk0 f hf) = Additive.ofMul (Units.mk0 f hf) := by
    rw [← ofMul_pow, hu]
  have h := congrArg (fun D => projectivePrincipalDivisor D A) hadd
  simp only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h
  push_cast at h
  omega

/-- **Gonality.**  Every function with poles bounded by an effective divisor
of degree at most two is constant. -/
theorem mem_fullRiemannRochSpace25Two_of_degree_le_two (E : ProjectiveDivisor25Two)
    (hE : ∀ A, 0 ≤ E A) (hdeg : fullClosedPointGrading25Two.divisorDegree E ≤ 2)
    (f : CurveField) (hf : f ∈ fullRiemannRochSpace25Two E) : f = 0 ∨ f = 1 := by
  classical
  rcases hf with h0 | ⟨hf0, hb⟩
  · exact Or.inl h0
  apply (mem_fullRiemannRochSpace25Two_zero_iff f).mp
  by_cases h8 : f ^ 8 - f = 0
  · refine Or.inr ⟨hf0, fun A => ?_⟩
    rw [principal_eq_zero_of_pow_eight f hf0 (sub_eq_zero.mp h8) A]
    simp
  exfalso
  set u : Additive CurveFieldˣ := Additive.ofMul (Units.mk0 f hf0) with hu
  set v : Additive CurveFieldˣ := Additive.ofMul (Units.mk0 (f ^ 8 - f) h8) with hv
  set F : ProjectiveDivisor25Two := projectivePrincipalDivisor v + (9 : ℕ) • E with hF
  have hFA : ∀ A, F A = projectivePrincipalDivisor v A + 9 * E A := by
    intro A
    simp [hF, nsmul_eq_mul]
  have hloc := fun A => projectivePrincipalDivisor_frobenius u v rfl A
  have hFnn : ∀ A, 0 ≤ F A := by
    intro A
    rw [hFA]
    have hbA := hb A
    have hEA := hE A
    obtain ⟨hpole, hreg, -⟩ := hloc A
    by_cases ho : projectivePrincipalDivisor u A < 0
    · rw [hpole ho]; omega
    · have := hreg (by omega); omega
  have hFpos : ∀ A, fullClosedPointGrading25Two.atomDegree A ∣ 3 → 1 ≤ F A := by
    intro A hd
    rw [hFA]
    have hbA := hb A
    have hEA := hE A
    obtain ⟨hpole, -, hvan⟩ := hloc A
    by_cases ho : projectivePrincipalDivisor u A < 0
    · rw [hpole ho]; omega
    · have := hvan hd (by omega); omega
  have hghost := ghostCount_le_divisorDegree fullClosedPointGrading25Two 3 F hFnn hFpos
  rw [ghostCount_three_eq] at hghost
  have hdegF : fullClosedPointGrading25Two.divisorDegree F =
      9 * fullClosedPointGrading25Two.divisorDegree E := by
    rw [hF, map_add, map_nsmul, projectivePrincipalDivisor_degree_eq_zero, nsmul_eq_mul]
    push_cast
    ring
  rw [hdegF] at hghost
  push_cast at hghost
  omega

/-- For an effective divisor of degree at most two, `L(E)` is the space of
constants. -/
theorem fullRiemannRochSpace25Two_eq_zero_of_degree_le_two (E : ProjectiveDivisor25Two)
    (hE : ∀ A, 0 ≤ E A) (hdeg : fullClosedPointGrading25Two.divisorDegree E ≤ 2) :
    fullRiemannRochSpace25Two E = fullRiemannRochSpace25Two 0 := by
  apply le_antisymm
  · intro f hf
    exact (mem_fullRiemannRochSpace25Two_zero_iff f).mpr
      (mem_fullRiemannRochSpace25Two_of_degree_le_two E hE hdeg f hf)
  · exact fullRiemannRochSpace25Two_mono 0 E (fun A => by simpa using hE A)

/-- `ℓ(E) = 1` for every effective divisor `E` of degree at most two. -/
theorem finrank_fullRiemannRochSpace25Two_of_degree_le_two (E : ProjectiveDivisor25Two)
    (hE : ∀ A, 0 ≤ E A) (hdeg : fullClosedPointGrading25Two.divisorDegree E ≤ 2) :
    Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) = 1 := by
  rw [fullRiemannRochSpace25Two_eq_zero_of_degree_le_two E hE hdeg,
    finrank_fullRiemannRochSpace25Two_zero]

end MazurProof.N25F_Gonality
