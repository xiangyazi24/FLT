import FLT.Assumptions.MazurProof.CurveZetaMarkedDivisors
import FLT.Assumptions.MazurProof.CurveDivisorPicard

/-!
# Ghost counts bound the degree of a divisor covering them

For a graded curve `C` and `k ≥ 0`, the intrinsic ghost count
`ghostCount C k` equals `∑ deg x` over the closed points `x` whose degree
divides `k` (each such point contributes one copy count and `deg x` residue
positions).  Consequently a nonnegative divisor that is at least one at every
such point has degree at least `ghostCount C k`.

For the N25 curve with `k = 3` the ghost count is the number `20` of
`F₈`-points, which is the bound used in the gonality argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace MazurProof.N25F_GhostDegreeBound
open CurveZetaEffectiveDivisors CurveZetaMarkedDivisors

variable (C : CurveZetaEffectiveDivisors.ClosedPointGrading)

/-- A nonnegative divisor that is positive at every closed point of degree
dividing `k` has degree at least the `k`th ghost count. -/
theorem ghostCount_le_divisorDegree (k : ℕ) (D : C.Divisor) (hD : ∀ x, 0 ≤ D x)
    (hk : ∀ x : C.Atom, C.atomDegree x ∣ k → 1 ≤ D x) :
    (CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C k : ℤ) ≤ C.divisorDegree D := by
  classical
  let T := Σ x : D.support, Fin (C.atomDegree x.1)
  let φ : CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot C k → T :=
    fun s => ⟨⟨s.1.1, Finsupp.mem_support_iff.mpr (by
      have h1 := hk s.1.1 (Dvd.intro_left _ s.2.1.2.2)
      omega)⟩, s.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨x, hx⟩, ⟨⟨r, hrk⟩, hr⟩, t⟩ ⟨⟨y, hy⟩, ⟨⟨s, hsk⟩, hs⟩, u⟩ h
    have hxy : x = y := congrArg (fun p : T => p.1.1) h
    have htu : t.1 = u.1 := congrArg (fun p : T => p.2.1) h
    subst hxy
    have hrs : r = s :=
      Nat.eq_of_mul_eq_mul_right (C.atomDegree_pos x) (hr.2.trans hs.2.symm)
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective C k
    change (x, r, t.1) = (x, s, u.1)
    rw [hrs, htu]
  have hcard : CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C k ≤
      ∑ x ∈ D.support, C.atomDegree x := by
    unfold CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount
    calc Nat.card (CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot C k)
        ≤ Nat.card T := Nat.card_le_card_of_injective φ hφ
      _ = ∑ x : D.support, C.atomDegree x.1 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          simp
      _ = ∑ x ∈ D.support, C.atomDegree x := Finset.sum_coe_sort D.support (C.atomDegree ·)
  have hdeg : C.divisorDegree D = ∑ x ∈ D.support, D x * (C.atomDegree x : ℤ) := rfl
  rw [hdeg]
  calc (CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C k : ℤ)
      ≤ ∑ x ∈ D.support, (C.atomDegree x : ℤ) := by exact_mod_cast hcard
    _ ≤ ∑ x ∈ D.support, D x * (C.atomDegree x : ℤ) := by
        apply Finset.sum_le_sum
        intro x hx
        have h1 : 1 ≤ D x := by
          have := Finsupp.mem_support_iff.mp hx
          have := hD x
          omega
        nlinarith [(Nat.cast_nonneg (C.atomDegree x) : (0 : ℤ) ≤ _)]

end MazurProof.N25F_GhostDegreeBound
