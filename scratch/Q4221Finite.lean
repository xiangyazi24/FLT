import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

/-- The affine duplication slope on `Y²=X³-31X²+240X`. -/
def dupSlopeN15 (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 62 * x + 240) / (2 * y)

def dupXN15 (x y : ℚ) : ℚ :=
  dupSlopeN15 x y ^ 2 + 31 - 2 * x

lemma duplication_identity_x0 (x : ℚ) :
    (3 * x ^ 2 - 62 * x + 240) ^ 2 -
        4 * x * (x - 15) * (x - 16) * (2 * x - 31) =
      (x ^ 2 - 240) ^ 2 := by
  ring

lemma duplication_identity_x15 (x : ℚ) :
    (3 * x ^ 2 - 62 * x + 240) ^ 2 -
        4 * x * (x - 15) * (x - 16) * (2 * x - 16) =
      (x ^ 2 - 30 * x + 240) ^ 2 := by
  ring

lemma duplication_identity_x16 (x : ℚ) :
    (3 * x ^ 2 - 62 * x + 240) ^ 2 -
        4 * x * (x - 15) * (x - 16) * (2 * x - 15) =
      (x ^ 2 - 32 * x + 240) ^ 2 := by
  ring

lemma no_rat_sq_240 (x : ℚ) : x ^ 2 ≠ 240 := by
  intro h
  have hnum := congrArg Rat.num h
  have hden := congrArg Rat.den h
  have hden1 : x.den * x.den = 1 := by
    simpa [pow_two, Rat.mul_self_den] using hden
  have hxden : x.den = 1 := by omega
  have hx : x = (x.num : ℚ) := by
    rw [← Rat.num_divInt_den x, hxden]
    simp
  rw [hx] at h
  norm_cast at h
  have hmod3 := congrArg (fun z : ℤ => z % 3) h
  norm_num [Int.pow_emod] at hmod3

lemma duplicate_to_x0_impossible {x y : ℚ}
    (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x - 15) * (x - 16))
    (hdup : dupXN15 x y = 0) : False := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hraw : (3 * x ^ 2 - 62 * x + 240) ^ 2 =
      4 * y ^ 2 * (2 * x - 31) := by
    unfold dupXN15 dupSlopeN15 at hdup
    field_simp [h2y] at hdup
    nlinarith
  rw [hcurve] at hraw
  have hs : (x ^ 2 - 240) ^ 2 = 0 := by
    rw [← duplication_identity_x0 x]
    nlinarith
  have hx : x ^ 2 = 240 := by nlinarith [sq_nonneg (x ^ 2 - 240)]
  exact no_rat_sq_240 x hx

lemma duplicate_to_x15_impossible {x y : ℚ}
    (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x - 15) * (x - 16))
    (hdup : dupXN15 x y = 15) : False := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hraw : (3 * x ^ 2 - 62 * x + 240) ^ 2 =
      4 * y ^ 2 * (2 * x - 16) := by
    unfold dupXN15 dupSlopeN15 at hdup
    field_simp [h2y] at hdup
    nlinarith
  rw [hcurve] at hraw
  have hs : (x ^ 2 - 30 * x + 240) ^ 2 = 0 := by
    rw [← duplication_identity_x15 x]
    nlinarith
  have hq : x ^ 2 - 30 * x + 240 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 30 * x + 240)]
  nlinarith [sq_nonneg (2 * x - 30)]

lemma duplicate_to_x16_classifies {x y : ℚ}
    (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x - 15) * (x - 16))
    (hdup : dupXN15 x y = 16) :
    (x = 12 ∧ (y = 12 ∨ y = -12)) ∨
      (x = 20 ∧ (y = 20 ∨ y = -20)) := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hraw : (3 * x ^ 2 - 62 * x + 240) ^ 2 =
      4 * y ^ 2 * (2 * x - 15) := by
    unfold dupXN15 dupSlopeN15 at hdup
    field_simp [h2y] at hdup
    nlinarith
  rw [hcurve] at hraw
  have hs : (x ^ 2 - 32 * x + 240) ^ 2 = 0 := by
    rw [← duplication_identity_x16 x]
    nlinarith
  have hq : x ^ 2 - 32 * x + 240 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 32 * x + 240)]
  have hfac : (x - 12) * (x - 20) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with hx | hx
  · left
    have hx12 : x = 12 := by linarith
    refine ⟨hx12, ?_⟩
    rw [hx12] at hcurve
    norm_num at hcurve
    have := sq_eq_sq_iff_eq_or_eq_neg.mp hcurve
    norm_num at this ⊢
    exact this
  · right
    have hx20 : x = 20 := by linarith
    refine ⟨hx20, ?_⟩
    rw [hx20] at hcurve
    norm_num at hcurve
    have := sq_eq_sq_iff_eq_or_eq_neg.mp hcurve
    norm_num at this ⊢
    exact this

/-- Once `2P` is known to be a nonzero rational two-torsion point, the only
possible affine halves are `(12,±12)` and `(20,±20)`. -/
theorem finite_duplication_endpoint {x y : ℚ}
    (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x - 15) * (x - 16))
    (h2tors : dupXN15 x y = 0 ∨ dupXN15 x y = 15 ∨ dupXN15 x y = 16) :
    (x = 12 ∧ (y = 12 ∨ y = -12)) ∨
      (x = 20 ∧ (y = 20 ∨ y = -20)) := by
  rcases h2tors with h0 | h15 | h16
  · exact (duplicate_to_x0_impossible hy hcurve h0).elim
  · exact (duplicate_to_x15_impossible hy hcurve h15).elim
  · exact duplicate_to_x16_classifies hy hcurve h16

end N15FormalBackup
