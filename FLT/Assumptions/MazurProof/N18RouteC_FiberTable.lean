import FLT.Assumptions.MazurProof.N18RouteC_FieldBasis
import FLT.Assumptions.MazurProof.N18RouteC_TorsionTable

/-!
# The rational part of the N18 plus-quotient fiber table

For every rational affine point, equality of its plus-quotient with one of
the twenty affine entries in the order-21 table forces `x = 0` or `x = -1`.
The proof is the promised finite coefficient computation in the basis
`1, a, a^2`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.FiberTable

open Isogeny Quotients TorsionTable

noncomputable section

local macro "n18f_ring" : tactic =>
  `(tactic|
    (ring_nf <;>
     simp only [Quotients.a_pow_thirty, Quotients.a_pow_twenty_nine,
       Quotients.a_pow_twenty_eight, Quotients.a_pow_twenty_seven,
       Quotients.a_pow_twenty_six, Quotients.a_pow_twenty_five,
       Quotients.a_pow_twenty_four, Quotients.a_pow_twenty_three,
       Quotients.a_pow_twenty_two, Quotients.a_pow_twenty_one,
       Quotients.a_pow_twenty, Quotients.a_pow_nineteen,
       Quotients.a_pow_eighteen, Quotients.a_pow_seventeen,
       Quotients.a_pow_sixteen, Quotients.a_pow_fifteen,
       a_pow_fourteen, a_pow_thirteen, a_pow_twelve, a_pow_eleven,
       a_pow_ten, a_pow_nine, a_pow_eight, a_pow_seven, a_pow_six,
       a_pow_five, a_pow_four, a_cubic] <;>
     ring))

theorem rational_ne_rm (x : ℚ) : (x : L) ≠ rm := by
  intro hx
  have hz : (x : L) + (1 : ℚ) * a + (1 : ℚ) * a ^ 2 = 0 := by
    rw [hx]
    simp only [rm, A0, q0]
    ring
  have hc := FieldBasis.quadratic_eq_zero hz
  norm_num at hc

/-- The plus quotient on the regular affine chart. -/
def qPlusAffine {x y : L}
    (hC : y ^ 2 = curveF x) (hx : x ≠ rm) : E0Point :=
  .some (plusIsoX (plusRawX x)) (plusIsoY (plusRawX x) (plusRawY x y)) <| by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    apply sub_eq_zero.mp
    rw [plus_change_residual, plusRaw_on_curve hC hx, mul_zero]

def fiberCoeff0 (i : Fin 20) (t : ℚ) : ℚ := ![
  -2 * t * (8 * t - 5),
  -2 * (t - 4) * (t + 1),
  2 * t + 1,
  -2 * (5 * t + 16),
  2 * (t + 1) * (2 * t + 1),
  2 * (t ^ 2 + 2 * t + 3),
  2 * (t ^ 2 + t + 1),
  2 * (t ^ 2 - t - 3),
  (2 * t - 1) * (2 * t + 1),
  2 * (3 * t ^ 2 + t + 2),
  2 * (3 * t ^ 2 + t + 2),
  (2 * t - 1) * (2 * t + 1),
  2 * (t ^ 2 - t - 3),
  2 * (t ^ 2 + t + 1),
  2 * (t ^ 2 + 2 * t + 3),
  2 * (t + 1) * (2 * t + 1),
  -2 * (5 * t + 16),
  2 * t + 1,
  -2 * (t - 4) * (t + 1),
  -2 * t * (8 * t - 5)] i

def fiberCoeff1 (i : Fin 20) (t : ℚ) : ℚ := ![
  2 * t * (t + 2),
  2 * (2 * t ^ 2 + 6 * t + 13),
  3 * t ^ 2 + 2 * t + 1,
  -4 * (10 * t + 29),
  2 * (t + 1) * (5 * t + 1),
  5 * t ^ 2 + 10 * t + 18,
  4 * (t ^ 2 + t + 1),
  2 * (t - 6) * (t + 2),
  4 * t ^ 2 - 7,
  2 * (3 * t ^ 2 + 4 * t + 5),
  2 * (3 * t ^ 2 + 4 * t + 5),
  4 * t ^ 2 - 7,
  2 * (t - 6) * (t + 2),
  4 * (t ^ 2 + t + 1),
  5 * t ^ 2 + 10 * t + 18,
  2 * (t + 1) * (5 * t + 1),
  -4 * (10 * t + 29),
  3 * t ^ 2 + 2 * t + 1,
  2 * (2 * t ^ 2 + 6 * t + 13),
  2 * t * (t + 2)] i

def fiberCoeff2 (i : Fin 20) (t : ℚ) : ℚ := ![
  2 * t * (4 * t - 1),
  2 * (2 * t ^ 2 + 3 * t + 7),
  3 * t ^ 2 + 2 * t + 1,
  -2 * (11 * t + 31),
  -2 * (t + 1) * (t + 2),
  2 * t ^ 2 + 4 * t + 9,
  2 * (t ^ 2 + t + 1),
  2 * (t - 3) * (t + 2),
  (t - 2) * (t + 2),
  2 * (t + 2),
  2 * (t + 2),
  (t - 2) * (t + 2),
  2 * (t - 3) * (t + 2),
  2 * (t ^ 2 + t + 1),
  2 * t ^ 2 + 4 * t + 9,
  -2 * (t + 1) * (t + 2),
  -2 * (11 * t + 31),
  3 * t ^ 2 + 2 * t + 1,
  2 * (2 * t ^ 2 + 3 * t + 7),
  2 * t * (4 * t - 1)] i

set_option maxHeartbeats 0 in
theorem quotient_x_numerator_coefficients (i : Fin 20) (t : ℚ) :
    alphaPlus * c3 * ((t : L) - rp) ^ 2 +
        ((3 / 2 : L) - torsionX i) * ((t : L) - rm) ^ 2 =
      (fiberCoeff0 i t : L) + fiberCoeff1 i t * a + fiberCoeff2 i t * a ^ 2 := by
  fin_cases i <;>
    simp [fiberCoeff0, fiberCoeff1, fiberCoeff2, torsionX,
      alphaPlus, c3, D0, rp, rm, A0, q0] <;>
    n18f_ring

theorem quotient_x_eq_target_coefficients
    (i : Fin 20) (t : ℚ) (y : L)
    (hC : y ^ 2 = curveF (t : L))
    (h : qPlusAffine hC (rational_ne_rm t) = torsionAffine i) :
    fiberCoeff0 i t = 0 ∧ fiberCoeff1 i t = 0 ∧ fiberCoeff2 i t = 0 := by
  have hx : plusIsoX (plusRawX (t : L)) = torsionX i := by
    simpa [qPlusAffine, torsionAffine] using
      congrArg (fun P : E0Point ↦ match P with
        | 0 => (0 : L)
        | .some x _ _ => x) h
  have hd : (t : L) - rm ≠ 0 := sub_ne_zero.mpr (rational_ne_rm t)
  have hnum :
      alphaPlus * c3 * ((t : L) - rp) ^ 2 +
          ((3 / 2 : L) - torsionX i) * ((t : L) - rm) ^ 2 = 0 := by
    unfold plusIsoX plusRawX at hx
    field_simp [hd] at hx
    linear_combination hx
  rw [quotient_x_numerator_coefficients] at hnum
  exact FieldBasis.quadratic_eq_zero hnum

theorem coefficients_force_cusp_x
    (i : Fin 20) (t : ℚ)
    (h0 : fiberCoeff0 i t = 0)
    (h1 : fiberCoeff1 i t = 0)
    (h2 : fiberCoeff2 i t = 0) :
    t = 0 ∨ t = -1 := by
  fin_cases i <;>
    simp [fiberCoeff0, fiberCoeff1, fiberCoeff2] at h0 h1 h2 <;>
    nlinarith

theorem rational_affine_target_forces_cusp_x
    (x y : ℚ) (hC : y ^ 2 = curvePolynomial x)
    (n : Fin 21)
    (h : qPlusAffine
        (by simpa using congrArg (algebraMap ℚ L) hC)
        (rational_ne_rm x) = torsionPoint n) :
    x = 0 ∨ x = -1 := by
  refine Fin.cases ?_ (fun i ↦ ?_) n
  · intro hzero
    simpa [qPlusAffine] using hzero
  · intro hi
    have hc := quotient_x_eq_target_coefficients i x (y : L)
      (by simpa using congrArg (algebraMap ℚ L) hC) (by simpa [torsionPoint] using hi)
    exact coefficients_force_cusp_x i x hc.1 hc.2.1 hc.2.2

theorem rational_affine_target_is_cusp
    (x y : ℚ) (hC : y ^ 2 = curvePolynomial x)
    (n : Fin 21)
    (h : qPlusAffine
        (by simpa using congrArg (algebraMap ℚ L) hC)
        (rational_ne_rm x) = torsionPoint n) :
    CurvePoint.IsCusp (.affine x y hC) := by
  have hx := rational_affine_target_forces_cusp_x x y hC n h
  have hy : y = 1 ∨ y = -1 := by
    rcases hx with rfl | rfl
    · apply sq_eq_one_iff.mp
      simpa [curvePolynomial] using hC
    · apply sq_eq_one_iff.mp
      simpa [curvePolynomial] using hC
  exact hx.elim (fun h0 ↦ Or.inl ⟨h0, hy⟩)
    (fun h1 ↦ Or.inr ⟨h1, hy⟩)

/-- Once the elliptic quotient has been exhausted by the verified order-21
table, the finite coefficient check proves that every rational curve point
is one of the six cusps. -/
theorem all_rational_points_are_cusps
    (hexhaust : ∀ Q : E0Point, ∃ n : Fin 21, Q = torsionPoint n) :
    ∀ P : CurvePointQ, CurvePoint.IsCusp P := by
  intro P
  cases P with
  | infinityPlus => trivial
  | infinityMinus => trivial
  | affine x y hC =>
      let Q : E0Point := qPlusAffine
        (by simpa using congrArg (algebraMap ℚ L) hC)
        (rational_ne_rm x)
      obtain ⟨n, hn⟩ := hexhaust Q
      exact rational_affine_target_is_cusp x y hC n hn

end

end MazurProof.N18RouteC.FiberTable
