import FLT.Assumptions.MazurProof.N25F_ClassNumberLower

/-!
# Abel–Jacobi injectivity for the N25 curve over `𝔽₂`

The curve has gonality at least three: every function whose poles are bounded
by an effective divisor of degree at most two is constant
(`mem_fullRiemannRochSpace25Two_of_degree_le_two`).  Consequently two distinct
closed points `A ≠ B` of degree at most two are never linearly equivalent: if
`A - B = div f`, then `f ∈ L(B)`, so `f` is constant and `A = B` as divisors.

For rational points this says that the Abel–Jacobi map
`P ↦ [P - X]` from degree-one closed points to `Pic⁰` is injective.  This is
the special-fibre half of the reduction argument for the rational points of
the level-25 quotient: a rational point whose class reduces to the class of a
known point must reduce to that point.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_AbelJacobi
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_FullPicardDegree
open N25F_RiemannRochSpace N25F_Gonality N25F_ClassNumberUpper
open N25F_OrderCalculus N25F_RationalPointOrders N25F_CertificateDivisors
open N25F_ClassNumberLower
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The divisor class of `A - B` for two closed points. -/
abbrev pointDiffClass (A B : fullClosedPointGrading25Two.Atom) :
    fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two :=
  fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
    (Finsupp.single A 1 - Finsupp.single B 1)

/-- **Distinct points of degree at most two are not linearly equivalent.**
If `A - B = div f`, then `f` has poles bounded by `B`, a divisor of degree at
most two, so `f` is constant by gonality; then `div f = 0` forces `A = B`. -/
theorem pointDiffClass_ne_zero {A B : fullClosedPointGrading25Two.Atom} (hAB : A ≠ B)
    (hB : fullClosedPointGrading25Two.atomDegree B ≤ 2) : pointDiffClass A B ≠ 0 := by
  classical
  intro h
  obtain ⟨g, hg⟩ := (QuotientAddGroup.eq_zero_iff
    (Finsupp.single A (1 : ℤ) - Finsupp.single B 1)).mp h
  set f : K := ((Additive.toMul g : Kˣ) : K) with hf
  have hf0 : f ≠ 0 := Units.ne_zero _
  have hgf : Additive.ofMul (Units.mk0 f hf0) = g := by
    apply Additive.toMul.injective
    ext
    rfl
  have hmem : f ∈ fullRiemannRochSpace25Two (Finsupp.single B 1) := by
    refine Or.inr ⟨hf0, fun C => ?_⟩
    rw [hgf, hg, Finsupp.sub_apply, add_sub_cancel]
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  have hBnn : ∀ C, 0 ≤ (Finsupp.single B (1 : ℤ)) C := fun C => by
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  have hdeg : fullClosedPointGrading25Two.divisorDegree (Finsupp.single B (1 : ℤ)) ≤ 2 := by
    change (Finsupp.single B (1 : ℤ)).sum
      (fun x m => m * (fullClosedPointGrading25Two.atomDegree x : ℤ)) ≤ 2
    rw [Finsupp.sum_single_index (by simp)]
    exact_mod_cast (by simpa using hB)
  rcases mem_fullRiemannRochSpace25Two_of_degree_le_two _ hBnn hdeg f hmem with h0 | h1
  · exact hf0 h0
  · have hg0 : g = 0 := by
      rw [← hgf]
      apply Additive.toMul.injective
      ext
      exact h1
    have := congrArg (fun D => D A) hg
    simp [hg0, hAB.symm] at this

/-- **Abel–Jacobi injectivity.**  For a fixed base point `O`, the map
`A ↦ [A - O]` is injective on closed points of degree at most two. -/
theorem pointDiffClass_injective (O : fullClosedPointGrading25Two.Atom)
    {A B : fullClosedPointGrading25Two.Atom}
    (hB : fullClosedPointGrading25Two.atomDegree B ≤ 2)
    (h : pointDiffClass A O = pointDiffClass B O) : A = B := by
  by_contra hAB
  apply pointDiffClass_ne_zero hAB hB
  have : pointDiffClass A B = pointDiffClass A O - pointDiffClass B O := by
    simp only [pointDiffClass, ← map_sub]
    congr 1
    abel
  rw [this, h, sub_self]

end MazurProof.N25F_AbelJacobi
