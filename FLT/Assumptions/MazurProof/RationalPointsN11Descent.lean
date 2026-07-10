import Mathlib

/-!
# The parity tail in the Billing--Mahler descent for 11a3

Billing and Mahler reduce the non-torsion part of the rational-point problem
for the order-11 modular curve to integral coefficients satisfying, among
other identities,

`18 z² = c² + 2ab + 4bc`,

where `z` is odd and `a` is even.  Modulo four this says that a square is
congruent to two.  This file verifies that final obstruction independently of
the still-missing cubic-field descent which produces the coefficients.
-/

namespace MazurProof.RationalPointsN11Descent

/-! ## The integral cubic used by Billing and Mahler -/

def MordellEquation (ξ η : ℚ) : Prop :=
  η ^ 2 = ξ ^ 3 - 432 * ξ + 8208

/-- The affine model `Y²=X³+8X²+16X+16` maps to the integral cubic by
`ξ=9X+24`, `η=27Y`. -/
theorem mordellEquation_of_E11
    {X Y : ℚ} (hE11 : Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16) :
    MordellEquation (9 * X + 24) (27 * Y) := by
  unfold MordellEquation
  linear_combination 729 * hE11

/-- The denominator of the monic cubic is the cube of the denominator of
its argument. -/
private theorem den_mordell_cubic (u : ℚ) :
    ((u ^ 3 - 432 * u + 8208).den : ℤ) = (u.den : ℤ) ^ 3 := by
  set a : ℤ := u.num
  set d : ℤ := (u.den : ℤ)
  have hdpos : (0 : ℤ) < d := by positivity
  have hdne : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hdpos)
  have hred : IsCoprime a d := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [a, d, Int.natAbs_natCast]
    exact u.reduced
  set N : ℤ := a ^ 3 - 432 * a * d ^ 2 + 8208 * d ^ 3
  have hNd : IsCoprime N d := by
    have h1 : IsCoprime (a ^ 3) d := hred.pow_left
    have h2 : IsCoprime
        (a ^ 3 + d * (-432 * a * d + 8208 * d ^ 2)) d :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hNd3 : IsCoprime N (d ^ 3) := hNd.pow_right
  have hNd3_nat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hNd3
  have hrepr : u ^ 3 - 432 * u + 8208 = (N : ℚ) / (d ^ 3 : ℚ) := by
    have hu : u = (a : ℚ) / (d : ℚ) := by
      simp only [a, d]
      push_cast
      exact (Rat.num_div_den u).symm
    rw [hu]
    field_simp [hdne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hNd3_nat

/-- A rational point on the integral cubic has a square denominator in its
first coordinate. -/
theorem mordell_rat_denom_square (ξ η : ℚ)
    (h : MordellEquation ξ η) :
    ∃ x z : ℤ, 0 < z ∧ Int.gcd x z = 1 ∧
      ξ = (x : ℚ) / (z : ℚ) ^ 2 := by
  have hsq : IsSquare (ξ ^ 3 - 432 * ξ + 8208) := by
    refine ⟨η, ?_⟩
    rw [← h]
    ring
  have hden_sq : IsSquare (ξ ^ 3 - 432 * ξ + 8208).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hden_eq : (ξ ^ 3 - 432 * ξ + 8208).den = ξ.den ^ 3 := by
    exact_mod_cast den_mordell_cubic ξ
  have hden3_sq : IsSquare (ξ.den ^ 3) := hden_eq ▸ hden_sq
  have hden_sq' : IsSquare ξ.den := by
    rcases hden3_sq with ⟨w, hw⟩
    have hdvd : ξ.den ^ 2 ∣ w ^ 2 := ⟨ξ.den, by rw [sq w, ← hw]; ring⟩
    have hdvdw : ξ.den ∣ w := by
      rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
        Nat.ceilRoot_pow_self two_ne_zero] at hdvd
    obtain ⟨v, rfl⟩ := hdvdw
    refine ⟨v, mul_left_cancel₀ (pow_ne_zero 2 ξ.den_ne_zero) ?_⟩
    calc
      ξ.den ^ 2 * ξ.den = ξ.den ^ 3 := by ring
      _ = ξ.den * v * (ξ.den * v) := hw
      _ = ξ.den ^ 2 * (v * v) := by ring
  obtain ⟨z₀, hz₀⟩ := hden_sq'
  have hz₀pos : 0 < z₀ := by
    rcases Nat.eq_zero_or_pos z₀ with hz | hz
    · simp [hz] at hz₀
    · exact hz
  refine ⟨ξ.num, (z₀ : ℤ), by exact_mod_cast hz₀pos, ?_, ?_⟩
  · have hzdiv : z₀ ∣ ξ.den := ⟨z₀, hz₀⟩
    have := ξ.reduced.coprime_dvd_right hzdiv
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      ξ = (ξ.num : ℚ) / (ξ.den : ℚ) := by
        simpa using (Rat.num_div_den ξ).symm
      _ = (ξ.num : ℚ) / ((z₀ : ℚ) ^ 2) := by
        rw [hz₀]
        push_cast
        ring

/-- Clearing the square denominator gives the primitive integral cubic used
in the descent. -/
theorem mordell_integral_model_of_rational_point (ξ η : ℚ)
    (h : MordellEquation ξ η) :
    ∃ x z y : ℤ,
      0 < z ∧ Int.gcd x z = 1 ∧
        ξ = (x : ℚ) / (z : ℚ) ^ 2 ∧
        y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 := by
  obtain ⟨x, z, hzpos, hcop, hξ⟩ := mordell_rat_denom_square ξ η h
  have hz : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hzpos)
  have hrat : (η * (z : ℚ) ^ 3) ^ 2 =
      ((x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 : ℤ) : ℚ) := by
    unfold MordellEquation at h
    rw [hξ] at h
    push_cast at h ⊢
    field_simp [hz] at h ⊢
    nlinarith
  have hsquare : IsSquare
      ((x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 : ℤ) : ℚ) :=
    ⟨η * (z : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsquare
  obtain ⟨y, hy⟩ := hsquare
  refine ⟨x, z, y, hzpos, hcop, hξ, ?_⟩
  rw [sq y]
  linarith

/-! ## The finite exceptional-point certificate -/

def mordellDiscriminantAbs : ℕ := 1496537856

private def squareMod (m : ℕ) (n : ℤ) : Bool :=
  decide (∃ r : Fin m,
    (r.1 : ℤ) ^ 2 % (m : ℤ) = n % (m : ℤ))

private theorem squareMod_of_sq (m : ℕ) (hm : 0 < m) (x y : ℤ)
    (h : y ^ 2 = x) : squareMod m x = true := by
  simp only [squareMod, decide_eq_true_eq]
  have hmInt : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hryNonneg : 0 ≤ y % (m : ℤ) :=
    Int.emod_nonneg y (ne_of_gt hmInt)
  have hryLt : y % (m : ℤ) < (m : ℤ) :=
    Int.emod_lt_of_pos y hmInt
  have hryCast : (((y % (m : ℤ)).toNat : ℕ) : ℤ) = y % (m : ℤ) :=
    Int.toNat_of_nonneg hryNonneg
  have hryNatLt : (y % (m : ℤ)).toNat < m := by
    exact_mod_cast (hryCast ▸ hryLt)
  refine ⟨⟨(y % (m : ℤ)).toNat, hryNatLt⟩, ?_⟩
  rw [hryCast, ← h]
  simp [pow_two, Int.mul_emod]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks 1227 candidates against eleven small moduli.
/-- Exhaustive bounded check of the integral cubic.  The first coordinate is
in `[-27,1199]` by elementary inequalities.  For each of these 1227 integers
we use quadratic-residue filters modulo `16,3,5,...,31`. -/
private theorem exceptional_integral_points_certificate :
    ∀ i : Fin 1227,
      let x : ℤ := (i.1 : ℤ) - 27
      let value := x ^ 3 - 432 * x + 8208
      squareMod 16 value = true →
      squareMod 3 value = true →
      squareMod 5 value = true →
      squareMod 7 value = true →
      squareMod 11 value = true →
      squareMod 13 value = true →
      squareMod 17 value = true →
      squareMod 19 value = true →
      squareMod 23 value = true →
      squareMod 29 value = true →
      squareMod 31 value = true →
      x = -12 ∨ x = 24 := by
  decide

/-- The finite half of the Billing--Mahler argument: an integral point whose
ordinate satisfies the Lutz--Nagell discriminant divisibility condition is
one of the four affine boundary points. -/
theorem exceptional_integral_point_boundary
    (x y : ℤ)
    (hcurve : y ^ 2 = x ^ 3 - 432 * x + 8208)
    (hy : y ^ 2 = 0 ∨ y ^ 2 ∣ (mordellDiscriminantAbs : ℤ)) :
    x = -12 ∨ x = 24 := by
  have hyBound : y ^ 2 ≤ (mordellDiscriminantAbs : ℤ) := by
    rcases hy with hy0 | hyD
    · rw [hy0]
      exact_mod_cast (Nat.zero_le mordellDiscriminantAbs)
    · have hyNatD : y.natAbs ^ 2 ∣ mordellDiscriminantAbs := by
        simpa [Int.natAbs_pow, mordellDiscriminantAbs] using
          (Int.natAbs_dvd_natAbs.mpr hyD)
      have hyNatLe : y.natAbs ^ 2 ≤ mordellDiscriminantAbs :=
        Nat.le_of_dvd (by norm_num [mordellDiscriminantAbs]) hyNatD
      have hyCast : (y.natAbs : ℤ) ^ 2 ≤
          (mordellDiscriminantAbs : ℤ) := by
        exact_mod_cast hyNatLe
      have hySq : y ^ 2 = (y.natAbs : ℤ) ^ 2 := by
        simp only [Int.natCast_natAbs, sq_abs]
      rw [hySq]
      exact hyCast
  have hxLower : -27 ≤ x := by
    by_contra hnot
    have hx28 : x + 28 ≤ 0 := by omega
    have hquad : 0 ≤ x ^ 2 - 28 * x + 352 := by
      nlinarith [sq_nonneg (x - 14)]
    have hprod : (x + 28) * (x ^ 2 - 28 * x + 352) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hx28 hquad
    have hid : x ^ 3 - 432 * x + 8208 =
        (x + 28) * (x ^ 2 - 28 * x + 352) - 1648 := by
      ring
    nlinarith [sq_nonneg y]
  have hxUpper : x ≤ 1199 := by
    change y ^ 2 ≤ 1496537856 at hyBound
    by_contra hnot
    have hx1200 : 0 ≤ x - 1200 := by omega
    have hquad : 0 ≤ x ^ 2 + 1200 * x + 1439568 := by
      nlinarith [sq_nonneg x]
    have hprod : 0 ≤ (x - 1200) * (x ^ 2 + 1200 * x + 1439568) :=
      mul_nonneg hx1200 hquad
    have hid : x ^ 3 - 432 * x + 8208 =
        (x - 1200) * (x ^ 2 + 1200 * x + 1439568) + 1727489808 := by
      ring
    nlinarith
  have hxShiftNonneg : 0 ≤ x + 27 := by omega
  have hxShiftEq : (((x + 27).toNat : ℕ) : ℤ) = x + 27 := by
    exact Int.toNat_of_nonneg hxShiftNonneg
  have hxShiftLt : (x + 27).toNat < 1227 := by
    omega
  let i : Fin 1227 := ⟨(x + 27).toNat, hxShiftLt⟩
  let value : ℤ := ((i.1 : ℤ) - 27) ^ 3 -
    432 * ((i.1 : ℤ) - 27) + 8208
  have hvalue : y ^ 2 = value := by
    dsimp [value, i]
    rw [hxShiftEq]
    norm_num
    exact hcurve
  have hcert := exceptional_integral_points_certificate i
    (squareMod_of_sq 16 (by norm_num) value y hvalue)
    (squareMod_of_sq 3 (by norm_num) value y hvalue)
    (squareMod_of_sq 5 (by norm_num) value y hvalue)
    (squareMod_of_sq 7 (by norm_num) value y hvalue)
    (squareMod_of_sq 11 (by norm_num) value y hvalue)
    (squareMod_of_sq 13 (by norm_num) value y hvalue)
    (squareMod_of_sq 17 (by norm_num) value y hvalue)
    (squareMod_of_sq 19 (by norm_num) value y hvalue)
    (squareMod_of_sq 23 (by norm_num) value y hvalue)
    (squareMod_of_sq 29 (by norm_num) value y hvalue)
    (squareMod_of_sq 31 (by norm_num) value y hvalue)
  simpa [i, hxShiftEq] using hcert

/-! ## The final parity obstruction -/

private theorem zmod_four_square_ne_two (u : ZMod 4) : u ^ 2 ≠ 2 := by
  fin_cases u <;> decide

/-- The final mod-4 contradiction in the Billing--Mahler descent. -/
theorem no_billing_mahler_middle_equation
    (z a b c : ℤ) (hz : Odd z) (ha : Even a)
    (hmid : 18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c) : False := by
  rcases hz with ⟨z₀, hz⟩
  rcases ha with ⟨a₀, ha⟩
  rw [hz, ha] at hmid
  have hmid4 := congrArg (fun q : ℤ ↦ (q : ZMod 4)) hmid
  push_cast at hmid4
  ring_nf at hmid4
  rw [show (4 : ZMod 4) = 0 by decide,
    show (18 : ZMod 4) = 2 by decide,
    show (72 : ZMod 4) = 0 by decide] at hmid4
  simp only [mul_zero, zero_add, add_zero] at hmid4
  have hc : (c : ZMod 4) ^ 2 = 2 := by
    exact hmid4.symm
  exact zmod_four_square_ne_two (c : ZMod 4) hc

/-- The three coefficient identities in the Billing--Mahler cubic-field
descent are inconsistent for a primitive pair `(x,z)`.  In particular, the
parity hypotheses used by `no_billing_mahler_middle_equation` are consequences,
not additional descent assumptions. -/
theorem no_billing_mahler_coefficient_system
    (x z a b c : ℤ)
    (hcop : Int.gcd x z = 1)
    (hfirst : -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c)
    (hmid : 18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c)
    (hthird : x = 2 * (b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2)) : False := by
  have hxEven : Even x := by
    refine ⟨b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2, ?_⟩
    rw [hthird]
    ring
  rcases hxEven with ⟨x₀, hx₀⟩
  have haSqEven : Even (a ^ 2) := by
    refine ⟨-x₀ + 12 * z ^ 2 - 2 * b * c, ?_⟩
    rw [hx₀] at hfirst
    nlinarith
  have haEven : Even a :=
    (Int.even_pow' (m := a) (n := 2) (by norm_num)).mp haSqEven
  have hxEven : Even x := ⟨x₀, hx₀⟩
  have hzOdd : Odd z := by
    rcases Int.even_or_odd z with hzEven | hzOdd
    · have hcop' : IsCoprime x z :=
        (Int.isCoprime_iff_gcd_eq_one).mpr hcop
      have hunit : IsUnit (2 : ℤ) :=
        hcop'.isUnit_of_dvd' hxEven.two_dvd hzEven.two_dvd
      rw [Int.isUnit_iff] at hunit
      norm_num at hunit
    · exact hzOdd
  exact no_billing_mahler_middle_equation z a b c hzOdd haEven hmid

end MazurProof.RationalPointsN11Descent
