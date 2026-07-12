import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_Quotients

/-!
# The explicit order-21 table on the N18 elliptic quotient

The point `generator21` is the generator returned by the finite descent
calculation.  This file verifies the twenty affine multiples directly in the
fixed cubic field.  No database torsion assertion is used.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.TorsionTable

open Isogeny

noncomputable section

local macro "n18t_ring" : tactic =>
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

/-- The x-coordinates of `P, 2P, ..., 20P`. -/
def torsionX : Fin 20 → L := ![
  -6 * a ^ 2 + 2 * a + 19,
  -2 * a ^ 2 + 5,
  -a ^ 2 + a + 3,
  2 * a ^ 2 + 4 * a + 3,
  4 * a ^ 2 - 6 * a - 1,
  -a + 1,
  1,
  2 * a + 1,
  a ^ 2 - 1,
  2 * a ^ 2 - 2 * a - 3,
  2 * a ^ 2 - 2 * a - 3,
  a ^ 2 - 1,
  2 * a + 1,
  1,
  -a + 1,
  4 * a ^ 2 - 6 * a - 1,
  2 * a ^ 2 + 4 * a + 3,
  -a ^ 2 + a + 3,
  -2 * a ^ 2 + 5,
  -6 * a ^ 2 + 2 * a + 19]

/-- The y-coordinates of `P, 2P, ..., 20P`. -/
def torsionY : Fin 20 → L := ![
  30 * a ^ 2 - 10 * a - 88,
  4 * a ^ 2 - 12,
  2 * a ^ 2 - 2 * a - 5,
  -10 * a ^ 2 - 20 * a - 8,
  16 * a ^ 2 - 24 * a - 12,
  2 * a - 1,
  -2,
  -4 * a - 4,
  a ^ 2 - 3,
  2 * a ^ 2 - 2 * a - 2,
  -4 * a ^ 2 + 4 * a + 4,
  -2 * a ^ 2 + 3,
  2 * a + 2,
  0,
  -a - 1,
  -20 * a ^ 2 + 30 * a + 12,
  8 * a ^ 2 + 16 * a + 4,
  -a ^ 2 + a + 1,
  -2 * a ^ 2 + 6,
  -24 * a ^ 2 + 8 * a + 68]

set_option maxHeartbeats 0 in
-- Each entry is an independent normalization in the fixed cubic basis.
theorem torsion_on_curve (i : Fin 20) :
    affineResidual E0 (torsionX i) (torsionY i) = 0 := by
  fin_cases i <;>
    simp [torsionX, torsionY] <;>
    unfold affineResidual E0 <;>
    n18t_ring

/-- The twenty nonzero entries of the cyclic table. -/
def torsionAffine (i : Fin 20) : E0Point :=
  .some (torsionX i) (torsionY i) <| by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    exact sub_eq_zero.mp (torsion_on_curve i)

/-- `0, P, 2P, ..., 20P`. -/
def torsionPoint : Fin 21 → E0Point :=
  Fin.cases 0 torsionAffine

def generator21 : E0Point := torsionAffine 0

@[simp] theorem torsionPoint_zero : torsionPoint 0 = 0 := rfl

@[simp] theorem torsionPoint_one : torsionPoint 1 = generator21 := rfl

/-! ## The consecutive-addition table -/

/-- Inverses of `x(nP) - x(P)` for `n = 2, ..., 19`. -/
def xDiffInv : Fin 18 → L := ![
  -(1 / 6 : L) * a ^ 2 + (1 / 6 : L) * a,
  -(2 / 3 : L) * a ^ 2 - a - 1 / 3,
  -(5 / 6 : L) * a ^ 2 + (4 / 3 : L) * a + 1 / 2,
  (1 / 2 : L) * a ^ 2 + (5 / 6 : L) * a + 1 / 6,
  (1 / 3 : L) * a ^ 2 - (2 / 3 : L) * a - 1 / 3,
  -(1 / 2 : L) * a ^ 2,
  (1 / 6 : L) * a,
  -(1 / 3 : L) * a ^ 2 + a + 1 / 3,
  -(1 / 3 : L) * a - 1 / 6,
  -(1 / 3 : L) * a - 1 / 6,
  -(1 / 3 : L) * a ^ 2 + a + 1 / 3,
  (1 / 6 : L) * a,
  -(1 / 2 : L) * a ^ 2,
  (1 / 3 : L) * a ^ 2 - (2 / 3 : L) * a - 1 / 3,
  (1 / 2 : L) * a ^ 2 + (5 / 6 : L) * a + 1 / 6,
  -(5 / 6 : L) * a ^ 2 + (4 / 3 : L) * a + 1 / 2,
  -(2 / 3 : L) * a ^ 2 - a - 1 / 3,
  -(1 / 6 : L) * a ^ 2 + (1 / 6 : L) * a]

theorem x_diff_mul_inv (i : Fin 18) :
    (torsionX ⟨i + 1, by omega⟩ - torsionX 0) * xDiffInv i = 1 := by
  fin_cases i <;>
    simp [torsionX, xDiffInv] <;>
    n18t_ring

theorem x_ne_generator (i : Fin 18) :
    torsionX ⟨i + 1, by omega⟩ ≠ torsionX 0 := by
  intro h
  have hzero :
      (torsionX ⟨i + 1, by omega⟩ - torsionX 0) * xDiffInv i = 0 := by
    rw [h, sub_self, zero_mul]
  rw [x_diff_mul_inv] at hzero
  exact one_ne_zero hzero

/-- Slopes of the secants from `2P, ..., 19P` to `P`. -/
def secantSlope : Fin 18 → L := ![
  2 * a ^ 2 - a - 6,
  2 * a ^ 2 + a - 5,
  -5,
  3 * a ^ 2 - 2 * a - 6,
  a ^ 2 - 5,
  2 * a ^ 2 - 5,
  a ^ 2 - a - 5,
  a ^ 2 + a - 4,
  2 * a ^ 2 - 2 * a - 5,
  a ^ 2 + a - 4,
  a ^ 2 - a - 5,
  2 * a ^ 2 - 5,
  a ^ 2 - 5,
  3 * a ^ 2 - 2 * a - 6,
  -5,
  2 * a ^ 2 + a - 5,
  2 * a ^ 2 - a - 6,
  2 * a ^ 2 - 7]

theorem slope_consecutive (i : Fin 18) :
    WeierstrassCurve.Affine.slope E0
        (torsionX ⟨i + 1, by omega⟩) (torsionX 0)
        (torsionY ⟨i + 1, by omega⟩) (torsionY 0) = secantSlope i := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x_ne_generator i)]
  have hinv :
      (torsionX ⟨i + 1, by omega⟩ - torsionX 0)⁻¹ = xDiffInv i :=
    inv_eq_of_mul_eq_one_right (x_diff_mul_inv i)
  rw [div_eq_mul_inv, hinv]
  fin_cases i <;>
    simp [torsionX, torsionY, secantSlope, xDiffInv] <;>
    n18t_ring

set_option maxHeartbeats 0 in
theorem add_generator_consecutive (i : Fin 18) :
    torsionAffine ⟨i + 1, by omega⟩ + generator21 =
      torsionAffine ⟨i + 2, by omega⟩ := by
  unfold generator21
  unfold torsionAffine
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (x_ne_generator i)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  rw [slope_consecutive]
  constructor <;>
    fin_cases i <;>
    simp [torsionX, torsionY, secantSlope, E0,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY] <;>
    n18t_ring

theorem tangent_difference_unit :
    (torsionY 0 - WeierstrassCurve.Affine.negY E0 (torsionX 0) (torsionY 0)) *
        ((1 / 2 : L) * a + 1 / 6) = 1 := by
  simp [torsionX, torsionY, E0, WeierstrassCurve.Affine.negY]
  n18t_ring

theorem tangent_y_ne_negY :
    torsionY 0 ≠ WeierstrassCurve.Affine.negY E0 (torsionX 0) (torsionY 0) := by
  intro h
  have hsub :
      torsionY 0 - WeierstrassCurve.Affine.negY E0 (torsionX 0) (torsionY 0) = 0 :=
    sub_eq_zero.mpr h
  have hzero :
      (torsionY 0 - WeierstrassCurve.Affine.negY E0 (torsionX 0) (torsionY 0)) *
          ((1 / 2 : L) * a + 1 / 6) = 0 := by
    rw [hsub, zero_mul]
  rw [tangent_difference_unit] at hzero
  exact one_ne_zero hzero

theorem tangentSlope :
    WeierstrassCurve.Affine.slope E0 (torsionX 0) (torsionX 0)
      (torsionY 0) (torsionY 0) = 2 * a ^ 2 - 7 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl tangent_y_ne_negY]
  have hinv :
      (torsionY 0 - WeierstrassCurve.Affine.negY E0 (torsionX 0) (torsionY 0))⁻¹ =
        (1 / 2 : L) * a + 1 / 6 :=
    inv_eq_of_mul_eq_one_right tangent_difference_unit
  rw [div_eq_mul_inv, hinv]
  simp [torsionX, torsionY, E0, WeierstrassCurve.Affine.negY]
  n18t_ring

set_option maxHeartbeats 0 in
theorem two_nsmul_generator :
    (2 : ℕ) • generator21 = torsionAffine 1 := by
  rw [two_nsmul]
  unfold generator21
  unfold torsionAffine
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne tangent_y_ne_negY]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  rw [tangentSlope]
  constructor <;>
    simp [torsionX, torsionY, E0, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY] <;>
    n18t_ring

theorem last_add_generator : torsionAffine 19 + generator21 = 0 := by
  unfold generator21
  unfold torsionAffine
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq
  · simp [torsionX]
  · simp [torsionX, torsionY, E0, WeierstrassCurve.Affine.negY]
    n18t_ring

theorem add_generator_table (i : Fin 20) :
    torsionPoint i.castSucc + generator21 = torsionPoint i.succ := by
  fin_cases i
  · rfl
  · change generator21 + generator21 = torsionAffine 1
    simpa only [two_nsmul] using two_nsmul_generator
  · change torsionAffine 1 + generator21 = torsionAffine 2
    exact add_generator_consecutive 0
  · change torsionAffine 2 + generator21 = torsionAffine 3
    exact add_generator_consecutive 1
  · change torsionAffine 3 + generator21 = torsionAffine 4
    exact add_generator_consecutive 2
  · change torsionAffine 4 + generator21 = torsionAffine 5
    exact add_generator_consecutive 3
  · change torsionAffine 5 + generator21 = torsionAffine 6
    exact add_generator_consecutive 4
  · change torsionAffine 6 + generator21 = torsionAffine 7
    exact add_generator_consecutive 5
  · change torsionAffine 7 + generator21 = torsionAffine 8
    exact add_generator_consecutive 6
  · change torsionAffine 8 + generator21 = torsionAffine 9
    exact add_generator_consecutive 7
  · change torsionAffine 9 + generator21 = torsionAffine 10
    exact add_generator_consecutive 8
  · change torsionAffine 10 + generator21 = torsionAffine 11
    exact add_generator_consecutive 9
  · change torsionAffine 11 + generator21 = torsionAffine 12
    exact add_generator_consecutive 10
  · change torsionAffine 12 + generator21 = torsionAffine 13
    exact add_generator_consecutive 11
  · change torsionAffine 13 + generator21 = torsionAffine 14
    exact add_generator_consecutive 12
  · change torsionAffine 14 + generator21 = torsionAffine 15
    exact add_generator_consecutive 13
  · change torsionAffine 15 + generator21 = torsionAffine 16
    exact add_generator_consecutive 14
  · change torsionAffine 16 + generator21 = torsionAffine 17
    exact add_generator_consecutive 15
  · change torsionAffine 17 + generator21 = torsionAffine 18
    exact add_generator_consecutive 16
  · change torsionAffine 18 + generator21 = torsionAffine 19
    exact add_generator_consecutive 17

theorem nsmul_generator (i : Fin 21) :
    (i : ℕ) • generator21 = torsionPoint i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      calc
        (i.succ : ℕ) • generator21 =
            (i.castSucc : ℕ) • generator21 + generator21 := by
              simp only [Fin.val_succ, Fin.val_castSucc, add_nsmul, one_nsmul]
        _ = torsionPoint i.castSucc + generator21 := by rw [ih]
        _ = torsionPoint i.succ := add_generator_table i

theorem twenty_one_nsmul_generator : (21 : ℕ) • generator21 = 0 := by
  calc
    (21 : ℕ) • generator21 = (20 : ℕ) • generator21 + generator21 := by
      rw [show (21 : ℕ) = 20 + 1 by norm_num, add_nsmul, one_nsmul]
    _ = torsionPoint (20 : Fin 21) + generator21 := by
      exact congrArg (fun Q : E0Point ↦ Q + generator21)
        (by simpa using nsmul_generator (20 : Fin 21))
    _ = torsionAffine 19 + generator21 := rfl
    _ = 0 := last_add_generator

private theorem divisor_twenty_one {d : ℕ} (hd : d ∣ 21) :
    d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 21 := by
  have hdle : d ≤ 21 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d
  all_goals norm_num at hd
  all_goals simp

theorem addOrderOf_generator21 : addOrderOf generator21 = 21 := by
  have hd : addOrderOf generator21 ∣ 21 :=
    addOrderOf_dvd_of_nsmul_eq_zero twenty_one_nsmul_generator
  rcases divisor_twenty_one hd with h1 | h3 | h7 | h21
  · rw [AddMonoid.addOrderOf_eq_one_iff] at h1
    exfalso
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _) h1
  · have hz : (3 : ℕ) • generator21 = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (h3 ▸ dvd_rfl)
    have hz' : torsionPoint (3 : Fin 21) = 0 := by
      rw [← nsmul_generator (3 : Fin 21)]
      exact hz
    exfalso
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _) hz'
  · have hz : (7 : ℕ) • generator21 = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (h7 ▸ dvd_rfl)
    have hz' : torsionPoint (7 : Fin 21) = 0 := by
      rw [← nsmul_generator (7 : Fin 21)]
      exact hz
    exfalso
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _) hz'
  · exact h21

end

end MazurProof.N18RouteC.TorsionTable
