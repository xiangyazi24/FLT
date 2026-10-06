import FLT.Assumptions.MazurProof.N25F_RationalAtomFiltration
import FLT.Assumptions.MazurProof.N25F_GhostDegreeBound
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoMiddleRiemannRoch

/-!
# The N25 curve has no closed points of degree two

The curve has `5` points over `F₂` and `5` points over `F₄`.  A closed point of
degree two would contribute two `F₄`-points that are not `F₂`-points, so the
`F₄`-count would be at least `7`.  Hence every closed point of degree at most
two is rational, and an effective divisor of degree at most two is a sum of
rational points.  With the one-point filtration of
`N25F_RationalAtomFiltration` this gives `ℓ(D) ≤ ℓ(D - E) + deg E` for such `E`.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_NoQuadraticPoints
open CurveZetaEffectiveDivisors CurveZetaMarkedDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_RationalAtomFiltration

/-- A closed point of degree two adds two slots to the degree-two ghost count
beyond those of the rational points. -/
theorem ghostCount_one_add_two_le (C : CurveZetaEffectiveDivisors.ClosedPointGrading)
    (x : C.Atom) (hx : C.atomDegree x = 2) :
    ClosedPointGrading.ghostCount C 1 + 2 ≤ ClosedPointGrading.ghostCount C 2 := by
  classical
  haveI : Finite (ClosedPointGrading.ExactGhostSlot C 2) := by
    unfold ClosedPointGrading.ExactGhostSlot; infer_instance
  haveI : Finite (ClosedPointGrading.ExactGhostSlot C 1) := by
    unfold ClosedPointGrading.ExactGhostSlot; infer_instance
  let φ : ClosedPointGrading.ExactGhostSlot C 1 ⊕ Fin 2 →
      ClosedPointGrading.ExactGhostSlot C 2 := fun s =>
    match s with
    | Sum.inl ⟨⟨y, hy⟩, ⟨⟨r, hr1⟩, hr⟩, t⟩ =>
        ⟨⟨y, by omega⟩, ⟨⟨2, by omega⟩, by
          refine ⟨by norm_num, ?_⟩
          have hpos := C.atomDegree_pos y
          have : C.atomDegree y = 1 := by
            have h := hr.2
            simp only at h
            nlinarith
          simp [this]⟩, t⟩
    | Sum.inr i => ⟨⟨x, by omega⟩, ⟨⟨1, by omega⟩, by simp [hx]⟩, Fin.cast hx.symm i⟩
  have hφ : Function.Injective φ := by
    intro s s' h
    have hc := congrArg (ClosedPointGrading.exactGhostCoordinates C 2) h
    rcases s with ⟨⟨y, hy⟩, ⟨⟨r, hr1⟩, hr⟩, t⟩ | i <;>
      rcases s' with ⟨⟨y', hy'⟩, ⟨⟨r', hr1'⟩, hr'⟩, t'⟩ | i'
    · have hr1 : r = 1 := by
        have h := hr.2; have := C.atomDegree_pos y; simp only at h; nlinarith
      have hr1' : r' = 1 := by
        have h := hr'.2; have := C.atomDegree_pos y'; simp only at h; nlinarith
      simp only [φ, ClosedPointGrading.exactGhostCoordinates, Prod.mk.injEq] at hc
      obtain ⟨rfl, -, ht⟩ := hc
      congr 1
      apply ClosedPointGrading.exactGhostCoordinates_injective C 1
      change (y, r, t.1) = (y, r', t'.1)
      rw [hr1, hr1', ht]
    · simp [φ, ClosedPointGrading.exactGhostCoordinates] at hc
    · simp [φ, ClosedPointGrading.exactGhostCoordinates] at hc
    · simp only [φ, ClosedPointGrading.exactGhostCoordinates, Prod.mk.injEq] at hc
      exact congrArg Sum.inr (Fin.ext hc.2.2)
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
  exact this

/-- The full N25 grading has no closed point of degree two. -/
theorem atomDegree_ne_two (A : fullClosedPointGrading25Two.Atom) :
    fullClosedPointGrading25Two.atomDegree A ≠ 2 := by
  intro hA
  have h := ghostCount_one_add_two_le fullClosedPointGrading25Two A hA
  rw [RationalPointsN25QuotientMiddleRiemannRoch.ClosedPointBridge25TwoLE4.ghostCount_one
      fullClosedPointBridge25TwoLE4,
    RationalPointsN25QuotientMiddleRiemannRoch.ClosedPointBridge25TwoLE4.ghostCount_two
      fullClosedPointBridge25TwoLE4,
    RationalPointsN25QuotientMiddleRiemannRoch.extensionPointCount25Two_one,
    RationalPointsN25QuotientMiddleRiemannRoch.extensionPointCount25Two_two] at h
  omega

/-- The value of an effective divisor at one point, times its degree, is at
most the total degree. -/
theorem le_divisorDegree_of_nonneg (E : ProjectiveDivisor25Two) (hE : ∀ A, 0 ≤ E A)
    (A : fullClosedPointGrading25Two.Atom) :
    E A * (fullClosedPointGrading25Two.atomDegree A : ℤ) ≤
      fullClosedPointGrading25Two.divisorDegree E := by
  classical
  change _ ≤ E.sum fun x m => m * (fullClosedPointGrading25Two.atomDegree x : ℤ)
  by_cases hA : A ∈ E.support
  · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hA]
    have : 0 ≤ ∑ x ∈ E.support.erase A,
        E x * (fullClosedPointGrading25Two.atomDegree x : ℤ) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hE x) (Nat.cast_nonneg _)
    linarith
  · rw [Finsupp.notMem_support_iff.mp hA, zero_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hE x) (Nat.cast_nonneg _)

/-- Every point in the support of an effective divisor of degree at most two
is rational. -/
theorem atomDegree_eq_one_of_pos (E : ProjectiveDivisor25Two) (hE : ∀ A, 0 ≤ E A)
    (hdeg : fullClosedPointGrading25Two.divisorDegree E ≤ 2)
    (A : fullClosedPointGrading25Two.Atom) (hA : 0 < E A) :
    fullClosedPointGrading25Two.atomDegree A = 1 := by
  have h := le_divisorDegree_of_nonneg E hE A
  have hpos := fullClosedPointGrading25Two.atomDegree_pos A
  have hne := atomDegree_ne_two A
  have : (fullClosedPointGrading25Two.atomDegree A : ℤ) ≤ 2 := by nlinarith
  omega

/-- Removing an effective divisor of degree `n ≤ 2` costs at most `n`
sections. -/
theorem finrank_le_sub_add_degree (D : ProjectiveDivisor25Two) :
    ∀ (n : ℕ) (E : ProjectiveDivisor25Two), (∀ A, 0 ≤ E A) →
      fullClosedPointGrading25Two.divisorDegree E = n → n ≤ 2 →
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) ≤
        Module.finrank (ZMod 2) (fullRiemannRochSpace25Two (D - E)) + n := by
  intro n
  induction n with
  | zero =>
      intro E hE hdeg _
      have hE0 : E = 0 := by
        ext A
        have h := le_divisorDegree_of_nonneg E hE A
        have hpos := fullClosedPointGrading25Two.atomDegree_pos A
        have := hE A
        rw [hdeg] at h
        push_cast at h
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        nlinarith
      rw [hE0, sub_zero]; omega
  | succ n ih =>
      intro E hE hdeg hn
      obtain ⟨A, hA⟩ : ∃ A, 0 < E A := by
        by_contra hcon
        push Not at hcon
        have : E = 0 := by
          ext A; have := hE A; have := hcon A; simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
        rw [this, map_zero] at hdeg
        omega
      have hA1 := atomDegree_eq_one_of_pos E hE (by rw [hdeg]; exact_mod_cast hn) A hA
      set E' := E - Finsupp.single A 1 with hE'
      have hE'nn : ∀ B, 0 ≤ E' B := by
        intro B
        by_cases hB : B = A
        · subst hB; simp [hE']; omega
        · simp [hE', Ne.symm hB, hE B]
      have hdeg' : fullClosedPointGrading25Two.divisorDegree E' = n := by
        rw [hE', map_sub, hdeg]
        change _ - (Finsupp.single A (1 : ℤ)).sum
          (fun x m => m * (fullClosedPointGrading25Two.atomDegree x : ℤ)) = _
        rw [Finsupp.sum_single_index (by simp), hA1]
        push_cast; ring
      have h1 := ih E' hE'nn hdeg' (by omega)
      have h2 := finrank_fullRiemannRochSpace25Two_le_sub_atom_add_one (D - E') A hA1
      have hDE : D - E' - Finsupp.single A 1 = D - E := by rw [hE']; abel
      rw [hDE] at h2
      omega

end MazurProof.N25F_NoQuadraticPoints
