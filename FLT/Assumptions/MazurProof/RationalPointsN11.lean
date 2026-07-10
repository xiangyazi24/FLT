import FLT.Assumptions.MazurProof.TateNFDivision

/-!
# Reduction of the order-11 Tate equation to the curve 11a3

The compact Tate factor `F11(b,c)=0`, with `b≠0`, produces a noncuspidal
rational point on

`Y² = X³ + 8X² + 16X + 16`.

The only remaining arithmetic input is that every rational affine point on
this curve has `X=0` or `X=-4`.  This file proves the reduction to that exact
boundary statement by rational algebra.
-/

namespace MazurProof.RationalPointsN11

def E11AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16

def E11DegenerateParameter (X : ℚ) : Prop :=
  X = 0 ∨ X = -4

theorem F11_param_identity (c t : ℚ) :
    TateNFDivision.F11 (c + c ^ 2 * t) c =
      -(c ^ 8 *
        (t ^ 5 * c ^ 2 +
          t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
          (t - 1) ^ 3)) := by
  unfold TateNFDivision.F11
  ring

private theorem c_ne_zero_of_F11 {b c : ℚ}
    (hb : b ≠ 0) (hF11 : TateNFDivision.F11 b c = 0) : c ≠ 0 := by
  intro hc
  subst c
  have hb5 : b ^ 5 = 0 := by
    simpa [TateNFDivision.F11] using hF11
  exact hb ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hb5)

theorem nondegenerate_E11_point_of_F11
    {b c : ℚ} (hb : b ≠ 0) (hF11 : TateNFDivision.F11 b c = 0) :
    ∃ X Y : ℚ,
      E11AffineEquation X Y ∧ ¬ E11DegenerateParameter X := by
  have hc : c ≠ 0 := c_ne_zero_of_F11 hb hF11
  let t : ℚ := (b - c) / c ^ 2
  have hb_param : b = c + c ^ 2 * t := by
    dsimp [t]
    field_simp [hc]
    ring
  have hparam := F11_param_identity c t
  rw [← hb_param, hF11] at hparam
  have hprod : c ^ 8 *
      (t ^ 5 * c ^ 2 +
        t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
        (t - 1) ^ 3) = 0 := by
    linarith
  have hQ :
      t ^ 5 * c ^ 2 +
        t * (t - 1) * (2 * t ^ 2 - 2 * t + 1) * c +
        (t - 1) ^ 3 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 8 hc)
  have ht0 : t ≠ 0 := by
    intro ht
    rw [ht] at hQ
    norm_num at hQ
  have ht1 : t ≠ 1 := by
    intro ht
    rw [ht] at hQ
    norm_num at hQ
    exact hc hQ
  let numerator : ℚ :=
    2 * t ^ 5 * c + t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)
  let denominator : ℚ := t * (t - 1)
  have hden : denominator ≠ 0 := by
    exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
  have hdisc :
      numerator ^ 2 =
        denominator ^ 2 * (1 - 4 * t * (t - 1) ^ 2) := by
    dsimp [numerator, denominator]
    calc
      (2 * t ^ 5 * c +
          t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)) ^ 2 =
          (t * (t - 1) * (2 * t ^ 2 - 2 * t + 1)) ^ 2 -
            4 * t ^ 5 * (t - 1) ^ 3 := by
              linear_combination 4 * t ^ 5 * hQ
      _ = (t * (t - 1)) ^ 2 * (1 - 4 * t * (t - 1) ^ 2) := by
        ring
  let y : ℚ := numerator / denominator
  have hy : y ^ 2 = 1 - 4 * t * (t - 1) ^ 2 := by
    dsimp [y]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hden)]
    simpa [mul_comm] using hdisc
  refine ⟨-4 * t, 4 * y, ?_, ?_⟩
  · unfold E11AffineEquation
    calc
      (4 * y) ^ 2 = 16 * y ^ 2 := by ring
      _ = 16 * (1 - 4 * t * (t - 1) ^ 2) := by rw [hy]
      _ = (-4 * t) ^ 3 + 8 * (-4 * t) ^ 2 + 16 * (-4 * t) + 16 := by ring
  · intro hdeg
    rcases hdeg with hzero | hneg4
    · exact ht0 (by linarith)
    · exact ht1 (by linarith)

theorem no_F11_solution_of_E11_boundary
    (hboundary : ∀ {X Y : ℚ}, E11AffineEquation X Y → E11DegenerateParameter X) :
    ¬ ∃ b c : ℚ, b ≠ 0 ∧ TateNFDivision.F11 b c = 0 := by
  rintro ⟨b, c, hb, hF11⟩
  obtain ⟨X, Y, hcurve, hnondeg⟩ :=
    nondegenerate_E11_point_of_F11 hb hF11
  exact hnondeg (hboundary hcurve)

end MazurProof.RationalPointsN11
