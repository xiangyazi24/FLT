import FLT.Assumptions.MazurProof.N18RouteC_Split

/-!
# Coefficient extraction in the fixed N18 cubic field

The field is presented as `Q[pi] / (pi^3 + 3*pi^2 - 3)` and `a = pi + 1`.
This file records the linear independence of `1, a, a^2` in a form suited to
the finite fiber computations.
-/

namespace MazurProof.N18RouteC.FieldBasis

noncomputable section

open Polynomial

private def quadraticInPi (c0 c1 c2 : ℚ) : ℚ[X] :=
  C (c0 + c1 + c2) + C (c1 + 2 * c2) * X + C c2 * X ^ 2

private theorem quadraticInPi_natDegree_lt (c0 c1 c2 : ℚ) :
    (quadraticInPi c0 c1 c2).natDegree < 3 := by
  unfold quadraticInPi
  compute_degree <;> norm_num

private theorem mk_quadraticInPi (c0 c1 c2 : ℚ) :
    AdjoinRoot.mk cubicPoly (quadraticInPi c0 c1 c2) =
      (c0 : L) + c1 * a + c2 * a ^ 2 := by
  simp [quadraticInPi, a, pi]
  ring

/-- The coefficients of a quadratic expression in `a` are unique. -/
theorem quadratic_eq_zero_iff (c0 c1 c2 : ℚ) :
    (c0 : L) + c1 * a + c2 * a ^ 2 = 0 ↔
      c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  constructor
  · intro h
    have hmk : AdjoinRoot.mk cubicPoly (quadraticInPi c0 c1 c2) = 0 := by
      rw [mk_quadraticInPi]
      exact h
    have hp : quadraticInPi c0 c1 c2 = 0 :=
      Polynomial.eq_zero_of_dvd_of_natDegree_lt
        (AdjoinRoot.mk_eq_zero.mp hmk)
        (by rw [cubicPoly_natDegree]; exact quadraticInPi_natDegree_lt c0 c1 c2)
    have h0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) hp
    have h1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) hp
    have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) hp
    simp [quadraticInPi] at h0 h1 h2
    constructor
    · linarith
    · constructor <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem quadratic_eq_zero {c0 c1 c2 : ℚ}
    (h : (c0 : L) + c1 * a + c2 * a ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 :=
  (quadratic_eq_zero_iff c0 c1 c2).mp h

theorem quadratic_ne_zero {c0 c1 c2 : ℚ}
    (h : c0 ≠ 0 ∨ c1 ≠ 0 ∨ c2 ≠ 0) :
    (c0 : L) + c1 * a + c2 * a ^ 2 ≠ 0 := by
  intro hz
  obtain ⟨h0, h1, h2⟩ := quadratic_eq_zero hz
  simp [h0, h1, h2] at h

end

end MazurProof.N18RouteC.FieldBasis
