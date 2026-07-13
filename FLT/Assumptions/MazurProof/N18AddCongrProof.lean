import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18RouteC_TorsionTable

/-!
# Audit of the proposed `N18AddCongr.add_congr` statement

The concrete chart polynomial identities are recorded first.  The proposed
valuation statement cannot be proved: the explicit order-21 table already in
the repository supplies a counterexample.
-/

open scoped Classical
open scoped WeierstrassCurve.Affine

namespace MazurProof.N18Block5Instantiation.AddCongrProof

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18RouteC.TorsionTable
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

/-! ## The concrete chart algebra -/

def G (t w : L) : L :=
  w - t * w + t ^ 2 * w - w ^ 2 + 5 * t * w ^ 2 - 5 * w ^ 3 - t ^ 3

def A (m : L) : L := 1 - m - 5 * m ^ 2 + 5 * m ^ 3

def B (m b : L) : L := m - b + m ^ 2 - 10 * m * b + 15 * m ^ 2 * b

def C (m b : L) : L := m - b - 2 * m * b + 5 * b ^ 2 - 15 * m * b ^ 2

def D (b : L) : L := b - b ^ 2 - 5 * b ^ 3

def H (m b : L) : L := -8 * m + 16 * m ^ 2 - 4 * b + 20 * m * b

theorem G_line (t m b : L) :
    G t (m * t + b) =
      -A m * t ^ 3 - B m b * t ^ 2 + C m b * t + D b := by
  simp only [G, A, B, C, D]
  ring

theorem BC_factor (m b : L) :
    B m b * (1 - b) - (1 + m) * C m b = b * H m b := by
  simp only [B, C, H]
  ring

/-- Identity (8), implied by the first two Vieta equations and `BC_factor`. -/
theorem identity8 (m b t₁ t₂ u t₃ d : L)
    (hsum : A m * (t₁ + t₂ + u) + B m b = 0)
    (hpair : A m * (t₁ * t₂ + (t₁ + t₂) * u) + C m b = 0)
    (hd : d = 1 - (1 + m) * u - b)
    (ht₃ : d * t₃ = -u) :
    A m * d * (t₃ - t₁ - t₂) =
      b * H m b - A m * (t₁ * t₂) * (1 + m) - A m * b * u := by
  have hBC := BC_factor m b
  rw [hd] at ht₃ ⊢
  linear_combination
    A m * ht₃ + (b - 1) * hsum + (1 + m) * hpair + hBC

/-! ## Exact valuation lemmas for the counterexample -/

private theorem add_ne_zero_of_ordPi_ne {x y : L}
    (hxy : ordPi x ≠ ordPi y) : x + y ≠ 0 := by
  intro h
  have hy : y = -x := by linear_combination h
  apply hxy
  rw [hy, ordPi_neg]

private theorem pi_ne_zero : pi ≠ 0 := by
  intro h
  have hv := ordPi_pi
  rw [h, ordPi_zero] at hv
  omega

private theorem ordPi_two : ordPi (2 : L) = 0 := by
  have hnegone : ordPi (-1 : L) = 0 := by rw [ordPi_neg, ordPi_one]
  calc
    ordPi (2 : L) = ordPi ((-1 : L) + 3) := by norm_num
    _ = ordPi (-1 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [hnegone, ordPi_three]; omega)
    _ = 0 := hnegone

private theorem ordPi_five : ordPi (5 : L) = 0 := by
  calc
    ordPi (5 : L) = ordPi ((2 : L) + 3) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two, ordPi_three]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_nine : ordPi (9 : L) = 6 := by
  rw [show (9 : L) = 3 * 3 by norm_num, ordPi_mul (by norm_num) (by norm_num),
    ordPi_three]
  norm_num

private theorem ordPi_ten : ordPi (10 : L) = 0 := by
  calc
    ordPi (10 : L) = ordPi ((1 : L) + 9) := by norm_num
    _ = ordPi (1 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_one, ordPi_nine]; omega)
    _ = 0 := ordPi_one

private theorem ordPi_fifty : ordPi (50 : L) = 0 := by
  have h48 : 3 ≤ ordPi (48 : L) := by
    rw [show (48 : L) = 3 * 16 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three]
    have : 0 ≤ ordPi (16 : L) := by
      simpa only [Int.cast_ofNat] using zero_le_ordPi_intCast 16
    omega
  calc
    ordPi (50 : L) = ordPi ((2 : L) + 48) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_sixty_eight : ordPi (68 : L) = 0 := by
  have h66 : 3 ≤ ordPi (66 : L) := by
    rw [show (66 : L) = 3 * 22 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three]
    have : 0 ≤ ordPi (22 : L) := by
      simpa only [Int.cast_ofNat] using zero_le_ordPi_intCast 22
    omega
  calc
    ordPi (68 : L) = ordPi ((2 : L) + 66) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_generator21_z : ordPi (zParam generator21) = 1 := by
  let qx : L := 9 + 5 * pi
  let ux : L := -10 + pi * qx
  let qy : L := 50 + 30 * pi
  have h5pi : ordPi (5 * pi) = 1 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, ordPi_five, ordPi_pi]
    norm_num
  have hqx : ordPi qx = 1 := by
    change ordPi (9 + 5 * pi) = 1
    rw [add_comm, ordPi_add_eq_of_lt (mul_ne_zero (by norm_num) pi_ne_zero) (by norm_num)]
    · exact h5pi
    · rw [h5pi, ordPi_nine]
      omega
  have hqx0 : qx ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hqx
    omega
  have hpqx : ordPi (pi * qx) = 2 := by
    rw [ordPi_mul pi_ne_zero hqx0, ordPi_pi, hqx]
    norm_num
  have hux : ordPi ux = 0 := by
    change ordPi ((-10 : L) + pi * qx) = 0
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero pi_ne_zero hqx0)]
    · rw [ordPi_neg, ordPi_ten]
    · rw [ordPi_neg, ordPi_ten, hpqx]
      omega
  have hux0 : ux ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_neg, ordPi_ten, hpqx]
    omega
  have hxform : torsionX 0 = pi * ux := by
    change -6 * a ^ 2 + 2 * a + 19 = pi * (-10 + pi * (9 + 5 * pi))
    unfold a
    linear_combination -5 * pi_relation
  have hx0 : torsionX 0 ≠ 0 := by rw [hxform]; exact mul_ne_zero pi_ne_zero hux0
  have hxv : ordPi (torsionX 0) = 1 := by
    rw [hxform, ordPi_mul pi_ne_zero hux0, ordPi_pi, hux]
    norm_num
  have h30 : ordPi (30 : L) = 3 := by
    rw [show (30 : L) = 3 * 10 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three, ordPi_ten]
    norm_num
  have h30pi : ordPi (30 * pi) = 4 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, h30, ordPi_pi]
    norm_num
  have hqy : ordPi qy = 0 := by
    change ordPi ((50 : L) + 30 * pi) = 0
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero (by norm_num) pi_ne_zero)]
    · exact ordPi_fifty
    · rw [ordPi_fifty, h30pi]
      omega
  have hqy0 : qy ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_fifty, h30pi]
    omega
  have hpy : ordPi (pi * qy) = 1 := by
    rw [ordPi_mul pi_ne_zero hqy0, ordPi_pi, hqy]
    norm_num
  have hyform : torsionY 0 = -68 + pi * qy := by
    change 30 * a ^ 2 - 10 * a - 88 = -68 + pi * (50 + 30 * pi)
    unfold a
    ring
  have hy0 : torsionY 0 ≠ 0 := by
    rw [hyform]
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_neg, ordPi_sixty_eight, hpy]
    omega
  have hyv : ordPi (torsionY 0) = 0 := by
    rw [hyform, ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero pi_ne_zero hqy0)]
    · rw [ordPi_neg, ordPi_sixty_eight]
    · rw [ordPi_neg, ordPi_sixty_eight, hpy]
      omega
  change ordPi (-torsionX 0 / torsionY 0) = 1
  rw [ordPi_div (neg_ne_zero.mpr hx0) hy0, ordPi_neg, hxv, hyv]
  omega

private theorem ordPi_six_generator_z : ordPi (zParam (torsionAffine 5)) = 1 := by
  have h2pi : ordPi (2 * pi) = 1 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, ordPi_two, ordPi_pi]
    norm_num
  have hy0 : (1 : L) + 2 * pi ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_one, h2pi]
    omega
  have hyv : ordPi ((1 : L) + 2 * pi) = 0 := by
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero (by norm_num) pi_ne_zero)]
    · exact ordPi_one
    · rw [ordPi_one, h2pi]
      omega
  change ordPi (-(-a + 1) / (2 * a - 1)) = 1
  have hx : -a + 1 = -pi := by unfold a; ring
  have hy : 2 * a - 1 = 1 + 2 * pi := by unfold a; ring
  rw [hx, hy, neg_neg, ordPi_div pi_ne_zero hy0, ordPi_pi, hyv]
  omega

private theorem seven_generator_z : zParam (torsionAffine 6) = (1 / 2 : L) := by
  change -((1 : L)) / (-2) = 1 / 2
  norm_num

private theorem ordPi_seven_generator_z : ordPi (zParam (torsionAffine 6)) = 0 := by
  rw [seven_generator_z, ordPi_div (by norm_num) (by norm_num), ordPi_one, ordPi_two]
  omega

private theorem generator_add_six_generator :
    generator21 + torsionAffine 5 = torsionAffine 6 := by
  have := add_generator_consecutive (4 : Fin 18)
  rw [add_comm] at this
  convert this using 2 <;> rfl

private theorem ordPi_counterexample_error :
    ordPi (zParam (generator21 + torsionAffine 5) -
      zParam generator21 - zParam (torsionAffine 5)) = 0 := by
  rw [generator_add_six_generator]
  have hz7 : zParam (torsionAffine 6) ≠ 0 := by
    rw [seven_generator_z]
    norm_num
  have hz1 : zParam generator21 ≠ 0 := by
    intro h
    have hv := ordPi_generator21_z
    rw [h, ordPi_zero] at hv
    omega
  have hz6 : zParam (torsionAffine 5) ≠ 0 := by
    intro h
    have hv := ordPi_six_generator_z
    rw [h, ordPi_zero] at hv
    omega
  have hfirst0 :
      ordPi (zParam (torsionAffine 6) + -zParam generator21) = 0 := by
    rw [ordPi_add_eq_of_lt hz7 (neg_ne_zero.mpr hz1)]
    · exact ordPi_seven_generator_z
    · rw [ordPi_seven_generator_z, ordPi_neg, ordPi_generator21_z]
      omega
  have hfirstne : zParam (torsionAffine 6) + -zParam generator21 ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_seven_generator_z, ordPi_neg, ordPi_generator21_z]
    omega
  rw [show zParam (torsionAffine 6) - zParam generator21 - zParam (torsionAffine 5) =
      (zParam (torsionAffine 6) + -zParam generator21) + -zParam (torsionAffine 5) by
        ring]
  rw [ordPi_add_eq_of_lt hfirstne (neg_ne_zero.mpr hz6) (by
    rw [hfirst0, ordPi_neg, ordPi_six_generator_z]
    omega), hfirst0]

/-- The requested signature is false on two entries of the existing explicit
order-21 point table. -/
theorem not_add_congr_signature :
    ¬ ∀ (P Q : E0Point),
      (1 ≤ v (zParam P)) → (1 ≤ v (zParam Q)) →
        v (zParam P) + v (zParam Q) ≤
          v (zParam (P + Q) - zParam P - zParam Q) := by
  intro h
  have hbad := h generator21 (torsionAffine 5)
    (by change 1 ≤ ordPi (zParam generator21); rw [ordPi_generator21_z])
    (by change 1 ≤ ordPi (zParam (torsionAffine 5)); rw [ordPi_six_generator_z])
  change ordPi (zParam generator21) + ordPi (zParam (torsionAffine 5)) ≤
    ordPi (zParam (generator21 + torsionAffine 5) -
      zParam generator21 - zParam (torsionAffine 5)) at hbad
  rw [ordPi_generator21_z, ordPi_six_generator_z, ordPi_counterexample_error] at hbad
  omega

end

end MazurProof.N18Block5Instantiation.AddCongrProof
