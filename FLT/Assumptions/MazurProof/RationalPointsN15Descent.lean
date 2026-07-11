import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN15C0

/-!
# First full-two-torsion descent layer for the order-15 curve

Scaling the curve from `RationalPointsN15C0` by `X = 4s`, `Y = 4v`
gives

`Y² = X(X+1)(X+16) = X³ + 17X² + 16X`.

This file carries out the elementary front end of a full `2`-descent:

* square-denominator normalization and an integral primitive model;
* pairwise gcd bounds for the three linear factors;
* extraction of the finite squareclasses of the `X` coordinate;
* the analogous squareclass computation on the `2`-isogenous curve
  `Y² = X³ - 34X² + 225X`;
* kernel-checked local exclusions of the remaining `2`- and `3`-supported
  squareclasses.

No rank or rational-point exhaustion statement is made here.
-/

namespace MazurProof.RationalPointsN15Descent

open RationalPointsN15C0

/-! ## Scaling and the two integral cubics -/

def FullTwoEquation (x y : ℚ) : Prop :=
  y ^ 2 = x * (x + 1) * (x + 16)

def IsogenousEquation (x y : ℚ) : Prop :=
  y ^ 2 = x * (x - 9) * (x - 25)

theorem fullTwoEquation_cubic (x y : ℚ) :
    FullTwoEquation x y ↔ y ^ 2 = x ^ 3 + 17 * x ^ 2 + 16 * x := by
  unfold FullTwoEquation
  constructor <;> intro h
  · rw [h]
    ring
  · rw [h]
    ring

theorem isogenousEquation_cubic (x y : ℚ) :
    IsogenousEquation x y ↔ y ^ 2 = x ^ 3 - 34 * x ^ 2 + 225 * x := by
  unfold IsogenousEquation
  constructor <;> intro h
  · rw [h]
    ring
  · rw [h]
    ring

theorem scaled_fullTwoEquation {s v : ℚ} (h : C0Equation s v) :
    FullTwoEquation (4 * s) (4 * v) := by
  unfold C0Equation at h
  unfold FullTwoEquation
  linear_combination 16 * h

theorem unscaled_C0Equation {x y : ℚ} (h : FullTwoEquation x y) :
    C0Equation (x / 4) (y / 4) := by
  unfold FullTwoEquation at h
  unfold C0Equation
  linear_combination (1 / 16 : ℚ) * h

/-- The explicit degree-two isogeny on affine non-kernel points. -/
theorem to_isogenous_curve {x y : ℚ} (hx : x ≠ 0)
    (h : FullTwoEquation x y) :
    IsogenousEquation (y ^ 2 / x ^ 2)
      (y * (16 - x ^ 2) / x ^ 2) := by
  unfold FullTwoEquation at h
  unfold IsogenousEquation
  field_simp [hx]
  rw [h]
  ring

/-- The dual degree-two isogeny, followed by the scaling identifying the
double quotient with the original curve. -/
theorem from_isogenous_curve {x y : ℚ} (hx : x ≠ 0)
    (h : IsogenousEquation x y) :
    FullTwoEquation (y ^ 2 / x ^ 2 / 4)
      (y * (225 - x ^ 2) / x ^ 2 / 8) := by
  unfold IsogenousEquation at h
  unfold FullTwoEquation
  field_simp [hx]
  rw [h]
  ring

/-! ## Generic square-denominator normalization -/

private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

/-- The denominator of a monic cubic with zero constant term is the cube of
the denominator of its argument. -/
private theorem den_monic_cubic (a b : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D)) D :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

theorem rat_denom_square_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den = x.den ^ 3 := by
    exact_mod_cast den_monic_cubic a b x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

/-- Denominator clearing for any monic cubic `y²=x³+ax²+bx`. -/
theorem integral_model_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4) := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ := rat_denom_square_monic a b x y h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  rw [sq C]
  exact hC.symm

theorem fullTwo_integral_model {x y : ℚ} (h : FullTwoEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2) := by
  have hcubic := (fullTwoEquation_cubic x y).mp h
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    integral_model_monic 17 16 x y hcubic
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  calc
    C ^ 2 = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := hC
    _ = A * (A + B ^ 2) * (A + 16 * B ^ 2) := by ring

theorem isogenous_integral_model {x y : ℚ} (h : IsogenousEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) := by
  have hcubic := (isogenousEquation_cubic x y).mp h
  have hcubic' : y ^ 2 =
      x ^ 3 + ((-34 : ℤ) : ℚ) * x ^ 2 + ((225 : ℤ) : ℚ) * x := by
    push_cast
    linarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    integral_model_monic (-34) 225 x y hcubic'
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  calc
    C ^ 2 = A * (A ^ 2 - 34 * A * B ^ 2 + 225 * B ^ 4) := by
      simpa [sub_eq_add_neg] using hC
    _ = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) := by ring

/-! ## Pairwise gcd bounds for the full-two-torsion factors -/

theorem gcd_linear_factor_denominator (A B k : ℤ)
    (hcop : Int.gcd A B = 1) :
    Int.gcd (A + k * B ^ 2) B = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  obtain ⟨u, v, huv⟩ := hAB
  exact ⟨u, v - u * k * B, by rw [← huv]; ring⟩

private theorem coprime_of_dvd_left {a b d : ℤ} (hab : IsCoprime a b)
    (hd : d ∣ a) : IsCoprime d b := by
  rcases hab with ⟨u, v, huv⟩
  rcases hd with ⟨k, rfl⟩
  exact ⟨u * k, v, by rw [← huv]; ring⟩

theorem fullTwo_gcd_zero_one (A B : ℤ) (hcop : Int.gcd A B = 1) :
    Int.gcd A (A + B ^ 2) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hAB2 := hAB.pow_right (n := 2)
  obtain ⟨u, v, huv⟩ := hAB2
  exact ⟨u - v, v, by rw [← huv]; ring⟩

theorem fullTwo_gcd_zero_sixteen_dvd (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    ((Int.gcd A (A + 16 * B ^ 2) : ℕ) : ℤ) ∣ (16 : ℤ) := by
  let d : ℤ := (Int.gcd A (A + 16 * B ^ 2) : ℤ)
  have hdA : d ∣ A := Int.gcd_dvd_left _ _
  have hdF : d ∣ A + 16 * B ^ 2 := Int.gcd_dvd_right _ _
  have hd16B2 : d ∣ 16 * B ^ 2 := by
    rw [show 16 * B ^ 2 = (A + 16 * B ^ 2) - A by ring]
    exact dvd_sub hdF hdA
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hdB : IsCoprime d (B ^ 2) :=
    (coprime_of_dvd_left hAB hdA).pow_right
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hd16B2
    (Int.isCoprime_iff_gcd_eq_one.mp hdB)

theorem fullTwo_gcd_one_sixteen_dvd (A B : ℤ)
    (hcop : Int.gcd A B = 1) :
    ((Int.gcd (A + B ^ 2) (A + 16 * B ^ 2) : ℕ) : ℤ) ∣ (15 : ℤ) := by
  let d : ℤ := (Int.gcd (A + B ^ 2) (A + 16 * B ^ 2) : ℤ)
  have hd1 : d ∣ A + B ^ 2 := Int.gcd_dvd_left _ _
  have hd16 : d ∣ A + 16 * B ^ 2 := Int.gcd_dvd_right _ _
  have hd15B2 : d ∣ 15 * B ^ 2 := by
    rw [show 15 * B ^ 2 =
      (A + 16 * B ^ 2) - (A + B ^ 2) by ring]
    exact dvd_sub hd16 hd1
  have hF1B : IsCoprime (A + B ^ 2) B := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using gcd_linear_factor_denominator A B 1 hcop
  have hdB : IsCoprime d (B ^ 2) :=
    (coprime_of_dvd_left hF1B hd1).pow_right
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hd15B2
    (Int.isCoprime_iff_gcd_eq_one.mp hdB)

/-! ## Squarefree cores and finite squareclasses -/

/-- If `a*q` is a square and `d` is the squarefree core in
`a = r²*d`, then `d` divides `q`. -/
private theorem squarefree_core_dvd_other {a q c d r : ℕ}
    (ha0 : a ≠ 0) (hdecomp : r ^ 2 * d = a) (hd : Squarefree d)
    (hsq : c ^ 2 = a * q) : d ∣ q := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    simp at hdecomp
    exact ha0 hdecomp.symm
  have hr2dvd : r ^ 2 ∣ c ^ 2 := by
    refine ⟨d * q, ?_⟩
    rw [hsq, ← hdecomp]
    ring
  have hrdvd : r ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hr2dvd
  obtain ⟨k, rfl⟩ := hrdvd
  have hk : k ^ 2 = d * q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hr0)
    calc
      r ^ 2 * k ^ 2 = (r * k) ^ 2 := by ring
      _ = a * q := hsq
      _ = (r ^ 2 * d) * q := by rw [hdecomp]
      _ = r ^ 2 * (d * q) := by ring
  have hdk2 : d ∣ k ^ 2 := ⟨q, hk⟩
  have hdk : d ∣ k := (hd.dvd_pow_iff_dvd two_ne_zero).mp hdk2
  obtain ⟨l, rfl⟩ := hdk
  have hcancel : d * (d * l ^ 2) = d * q := by
    calc
      d * (d * l ^ 2) = (d * l) ^ 2 := by ring
      _ = d * q := hk
  have hq : d * l ^ 2 = q := mul_left_cancel₀ hd.ne_zero hcancel
  exact ⟨l ^ 2, hq.symm⟩

/-- In a primitive integral model
`C²=A(A²+aAB²+bB⁴)`, the squarefree core of `|A|` divides `|b|`. -/
theorem squarefree_core_dvd_cubic_coefficient
    {a b A B C : ℤ} {d r : ℕ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4))
    (hdecomp : r ^ 2 * d = A.natAbs) (hd : Squarefree d) :
    d ∣ b.natAbs := by
  let Q : ℤ := A ^ 2 + a * A * B ^ 2 + b * B ^ 4
  have hAabs0 : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA0
  have habs : C.natAbs ^ 2 = A.natAbs * Q.natAbs := by
    simpa [Q, Int.natAbs_pow, Int.natAbs_mul] using
      congrArg Int.natAbs hmodel
  have hdQ : d ∣ Q.natAbs :=
    squarefree_core_dvd_other hAabs0 hdecomp hd habs
  have hdA : d ∣ A.natAbs := by
    exact hdecomp ▸ dvd_mul_left d (r ^ 2)
  have hdAZ : (d : ℤ) ∣ A := Int.natCast_dvd.mpr hdA
  have hdQZ : (d : ℤ) ∣ Q := Int.natCast_dvd.mpr hdQ
  have hdbB4 : (d : ℤ) ∣ b * B ^ 4 := by
    rw [show b * B ^ 4 = Q - A * (A + a * B ^ 2) by
      simp only [Q]
      ring]
    exact dvd_sub hdQZ (dvd_mul_of_dvd_left hdAZ _)
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hdB4 : IsCoprime (d : ℤ) (B ^ 4) :=
    (coprime_of_dvd_left hAB hdAZ).pow_right
  have hdbZ : (d : ℤ) ∣ b := hdB4.dvd_of_dvd_mul_right hdbB4
  exact Int.natCast_dvd.mp hdbZ

/-- Finite squareclass extraction for the first coordinate of a primitive
monic-cubic model. -/
theorem first_coordinate_squareclass
    {a b A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ d r : ℕ, Squarefree d ∧ d ∣ b.natAbs ∧
      (A = (d : ℤ) * (r : ℤ) ^ 2 ∨
       A = -((d : ℤ) * (r : ℤ) ^ 2)) := by
  obtain ⟨d, r, hdecomp, hd⟩ := Nat.sq_mul_squarefree A.natAbs
  have hdb := squarefree_core_dvd_cubic_coefficient hcop hA0 hmodel hdecomp hd
  have habs : (A.natAbs : ℤ) = (d : ℤ) * (r : ℤ) ^ 2 := by
    have hcast : (A.natAbs : ℤ) = ((r ^ 2 * d : ℕ) : ℤ) := by
      exact_mod_cast hdecomp.symm
    rw [hcast]
    push_cast
    ring
  refine ⟨d, r, hd, hdb, ?_⟩
  rcases Int.natAbs_eq A with hpos | hneg
  · left
    rw [hpos, habs]
  · right
    rw [hneg, habs]

theorem squarefree_dvd_sixteen {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 16) : d = 1 ∨ d = 2 := by
  have hpow : d ∣ 2 ^ 4 := by simpa using hdiv
  have hd2 : d ∣ 2 := (hd.dvd_pow_iff_dvd (by norm_num : 4 ≠ 0)).mp hpow
  exact (Nat.dvd_prime Nat.prime_two).mp hd2

theorem squarefree_dvd_two_twenty_five {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 225) : d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15 := by
  have hpow : d ∣ 15 ^ 2 := by norm_num at hdiv ⊢; exact hdiv
  have hd15 : d ∣ 15 := (hd.dvd_pow_iff_dvd two_ne_zero).mp hpow
  have hdle : d ≤ 15 := Nat.le_of_dvd (by norm_num) hd15
  interval_cases d <;> norm_num at hd15
  all_goals simp

/-- Before local solubility, the first-coordinate squareclass on the original
curve is one of `±1, ±2`. -/
theorem fullTwo_first_squareclasses {A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2)) :
    ∃ r : ℤ,
      A = r ^ 2 ∨ A = -(r ^ 2) ∨
      A = 2 * r ^ 2 ∨ A = -(2 * r ^ 2) := by
  have hmodel' :
      C ^ 2 = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by
    calc
      C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2) := hmodel
      _ = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by ring
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  rcases squarefree_dvd_sixteen hd (by simpa using hdiv) with rfl | rfl
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · left; simpa using h
    · right; left; simpa using h
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · right; right; left; simpa using h
    · right; right; right; simpa using h

/-- Before local solubility, the first-coordinate squareclass on the
`2`-isogenous curve is one of `±1, ±3, ±5, ±15`. -/
theorem isogenous_first_squareclasses {A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2)) :
    ∃ r : ℤ,
      A = r ^ 2 ∨ A = -(r ^ 2) ∨
      A = 3 * r ^ 2 ∨ A = -(3 * r ^ 2) ∨
      A = 5 * r ^ 2 ∨ A = -(5 * r ^ 2) ∨
      A = 15 * r ^ 2 ∨ A = -(15 * r ^ 2) := by
  have hmodel' :
      C ^ 2 = A * (A ^ 2 - 34 * A * B ^ 2 + 225 * B ^ 4) := by
    calc
      C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) := hmodel
      _ = A * (A ^ 2 - 34 * A * B ^ 2 + 225 * B ^ 4) := by ring
  have hmodel'' :
      C ^ 2 = A * (A ^ 2 + (-34) * A * B ^ 2 + 225 * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel'
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass (a := -34) (b := 225) hcop hA0 hmodel''
  rcases squarefree_dvd_two_twenty_five hd (by simpa using hdiv) with
      rfl | rfl | rfl | rfl
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · left; simpa using h
    · right; left; simpa using h
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · right; right; left; simpa using h
    · right; right; right; left; simpa using h
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · right; right; right; right; left; simpa using h
    · right; right; right; right; right; left; simpa using h
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · right; right; right; right; right; right; left; simpa using h
    · right; right; right; right; right; right; right; simpa using h

/-! ## Homogeneous quartic covers and local squareclass exclusions -/

/-- Substituting `A=d*r²` in the primitive cubic model produces the standard
homogeneous quartic for the `d`-squareclass. -/
theorem quartic_cover_of_squareclass
    {a b d e A B C r : ℤ} (hd : d ≠ 0) (hr : r ≠ 0)
    (hb : b = d * e) (hA : A = d * r ^ 2)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ z : ℤ,
      z ^ 2 = d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4 := by
  let Q : ℤ := d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4
  have hfactor : C ^ 2 = (d * r) ^ 2 * Q := by
    rw [hmodel, hA, hb]
    simp only [Q]
    ring
  have hfactor' : C ^ 2 = d ^ 2 * r ^ 2 * Q := by
    calc
      C ^ 2 = (d * r) ^ 2 * Q := hfactor
      _ = d ^ 2 * r ^ 2 * Q := by ring
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hrq : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrat : ((C : ℚ) / ((d : ℚ) * (r : ℚ))) ^ 2 = (Q : ℚ) := by
    field_simp [hdq, hrq]
    exact_mod_cast hfactor'
  have hsq : IsSquare (Q : ℚ) :=
    ⟨(C : ℚ) / ((d : ℚ) * (r : ℚ)), by
      rw [← sq]
      exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨z, hz⟩ := hsq
  refine ⟨z, ?_⟩
  rw [sq]
  exact hz.symm

theorem root_coprime_denominator {d r A B : ℤ}
    (hcop : Int.gcd A B = 1) (hA : A = d * r ^ 2) :
    Int.gcd r B = 1 := by
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hrA : r ∣ A := by
    rw [hA]
    exact ⟨d * r, by ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_dvd_left hAB hrA)

private def reduce16to2 : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private def reduce9to3 : ZMod 9 →+* ZMod 3 :=
  ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `16³` residue triples for this cover.
private theorem no_pos_two_cover_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ 2 * r ^ 4 + 17 * r ^ 2 * B ^ 2 + 8 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `16³` residue triples for this cover.
private theorem no_neg_two_cover_mod16 :
    ∀ r B z : ZMod 16,
      (reduce16to2 r ≠ 0 ∨ reduce16to2 B ≠ 0) →
      z ^ 2 ≠ -(2 * r ^ 4) + 17 * r ^ 2 * B ^ 2 - 8 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `9³` residue triples for this cover.
private theorem no_three_cover_mod9 :
    ∀ r B z : ZMod 9,
      (reduce9to3 r ≠ 0 ∨ reduce9to3 B ≠ 0) →
      z ^ 2 ≠ 3 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 75 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `9³` residue triples for this cover.
private theorem no_fifteen_cover_mod9 :
    ∀ r B z : ZMod 9,
      (reduce9to3 r ≠ 0 ∨ reduce9to3 B ≠ 0) →
      z ^ 2 ≠ 15 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 15 * B ^ 4 := by
  decide

private theorem primitive_mod_two {r B : ℤ} (hcop : Int.gcd r B = 1) :
    reduce16to2 (r : ZMod 16) ≠ 0 ∨
      reduce16to2 (B : ZMod 16) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [reduce16to2, ZMod.castHom_apply] using hmod2

private theorem primitive_mod_three {r B : ℤ} (hcop : Int.gcd r B = 1) :
    reduce9to3 (r : ZMod 9) ≠ 0 ∨
      reduce9to3 (B : ZMod 9) ≠ 0 := by
  have hnot : ¬ ((3 : ℤ) ∣ r ∧ (3 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h3g : (3 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h3g
    norm_num at h3g
  have hmod3 : (r : ZMod 3) ≠ 0 ∨ (B : ZMod 3) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 3).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd B 3).mp h.2⟩
  simpa [reduce9to3, ZMod.castHom_apply] using hmod3

theorem no_primitive_pos_two_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 + 17 * r ^ 2 * B ^ 2 + 8 * B ^ 4) : False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (no_pos_two_cover_mod16 (r : ZMod 16) (B : ZMod 16)
    (z : ZMod 16) (primitive_mod_two hcop)) hmod

theorem no_primitive_neg_two_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -(2 * r ^ 4) + 17 * r ^ 2 * B ^ 2 - 8 * B ^ 4) : False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (no_neg_two_cover_mod16 (r : ZMod 16) (B : ZMod 16)
    (z : ZMod 16) (primitive_mod_two hcop)) hmod

theorem no_primitive_three_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 3 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 75 * B ^ 4) : False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 9)) h
  push_cast at hmod
  exact (no_three_cover_mod9 (r : ZMod 9) (B : ZMod 9)
    (z : ZMod 9) (primitive_mod_three hcop)) hmod

theorem no_primitive_fifteen_cover (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 15 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 15 * B ^ 4) : False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 9)) h
  push_cast at hmod
  exact (no_fifteen_cover_mod9 (r : ZMod 9) (B : ZMod 9)
    (z : ZMod 9) (primitive_mod_three hcop)) hmod

/-! ## The two squareclass images after local solubility -/

/-- The mod-`16` checks remove both `±2` classes on the original curve. -/
theorem fullTwo_first_squareclasses_reduced {A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2)) :
    ∃ r : ℤ, A = r ^ 2 ∨ A = -(r ^ 2) := by
  obtain ⟨r, hpos | hneg | htwo | hnegTwo⟩ :=
    fullTwo_first_squareclasses hcop hA0 hmodel
  · exact ⟨r, Or.inl hpos⟩
  · exact ⟨r, Or.inr hneg⟩
  · have hr0 : r ≠ 0 := by
      intro hr
      apply hA0
      calc
        A = 2 * r ^ 2 := htwo
        _ = 0 := by simp [hr]
    have hmodel' :
        C ^ 2 = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by
      calc
        C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2) := hmodel
        _ = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by ring
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 17) (b := 16) (d := 2) (e := 8)
      (by norm_num) hr0 (by norm_num) htwo hmodel'
    exact (no_primitive_pos_two_cover r B z
      (root_coprime_denominator hcop htwo) hz).elim
  · have hr0 : r ≠ 0 := by
      intro hr
      apply hA0
      calc
        A = -(2 * r ^ 2) := hnegTwo
        _ = 0 := by simp [hr]
    have hA : A = (-2) * r ^ 2 := by linarith
    have hmodel' :
        C ^ 2 = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by
      calc
        C ^ 2 = A * (A + B ^ 2) * (A + 16 * B ^ 2) := hmodel
        _ = A * (A ^ 2 + 17 * A * B ^ 2 + 16 * B ^ 4) := by ring
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := 17) (b := 16) (d := -2) (e := -8)
      (by norm_num) hr0 (by norm_num) hA hmodel'
    have hz' : z ^ 2 =
        -(2 * r ^ 4) + 17 * r ^ 2 * B ^ 2 - 8 * B ^ 4 := by
      simpa [sub_eq_add_neg] using hz
    exact (no_primitive_neg_two_cover r B z
      (root_coprime_denominator hcop hA) hz').elim

theorem isogenous_first_factor_nonnegative {A B C : ℤ}
    (hmodel : C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2)) :
    0 ≤ A := by
  by_contra hA
  have hAneg : A < 0 := lt_of_not_ge hA
  have h9neg : A - 9 * B ^ 2 < 0 := by nlinarith [sq_nonneg B]
  have h25neg : A - 25 * B ^ 2 < 0 := by nlinarith [sq_nonneg B]
  have hp : 0 < A * (A - 9 * B ^ 2) := mul_pos_of_neg_of_neg hAneg h9neg
  have hn : A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) < 0 :=
    mul_neg_of_pos_of_neg hp h25neg
  nlinarith [sq_nonneg C]

/-- Negativity and the two mod-`9` checks leave only squareclasses `1` and
`5` on the `2`-isogenous curve. -/
theorem isogenous_first_squareclasses_reduced {A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2)) :
    ∃ r : ℤ, A = r ^ 2 ∨ A = 5 * r ^ 2 := by
  have hAnonneg := isogenous_first_factor_nonnegative hmodel
  have hApos : 0 < A := lt_of_le_of_ne hAnonneg (Ne.symm hA0)
  obtain ⟨r, h1 | hn1 | h3 | hn3 | h5 | hn5 | h15 | hn15⟩ :=
    isogenous_first_squareclasses hcop hA0 hmodel
  · exact ⟨r, Or.inl h1⟩
  · exfalso; nlinarith [sq_nonneg r]
  · have hr0 : r ≠ 0 := by
      intro hr
      apply hA0
      calc
        A = 3 * r ^ 2 := h3
        _ = 0 := by simp [hr]
    have hmodel' :
        C ^ 2 = A * (A ^ 2 + (-34) * A * B ^ 2 + 225 * B ^ 4) := by
      calc
        C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) := hmodel
        _ = A * (A ^ 2 + (-34) * A * B ^ 2 + 225 * B ^ 4) := by ring
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := -34) (b := 225) (d := 3) (e := 75)
      (by norm_num) hr0 (by norm_num) h3 hmodel'
    have hz' : z ^ 2 =
        3 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 75 * B ^ 4 := by
      simpa [sub_eq_add_neg] using hz
    exact (no_primitive_three_cover r B z
      (root_coprime_denominator hcop h3) hz').elim
  · exfalso; nlinarith [sq_nonneg r]
  · exact ⟨r, Or.inr h5⟩
  · exfalso; nlinarith [sq_nonneg r]
  · have hr0 : r ≠ 0 := by
      intro hr
      apply hA0
      calc
        A = 15 * r ^ 2 := h15
        _ = 0 := by simp [hr]
    have hmodel' :
        C ^ 2 = A * (A ^ 2 + (-34) * A * B ^ 2 + 225 * B ^ 4) := by
      calc
        C ^ 2 = A * (A - 9 * B ^ 2) * (A - 25 * B ^ 2) := hmodel
        _ = A * (A ^ 2 + (-34) * A * B ^ 2 + 225 * B ^ 4) := by ring
    obtain ⟨z, hz⟩ := quartic_cover_of_squareclass
      (a := -34) (b := 225) (d := 15) (e := 15)
      (by norm_num) hr0 (by norm_num) h15 hmodel'
    have hz' : z ^ 2 =
        15 * r ^ 4 - 34 * r ^ 2 * B ^ 2 + 15 * B ^ 4 := by
      simpa [sub_eq_add_neg] using hz
    exact (no_primitive_fifteen_cover r B z
      (root_coprime_denominator hcop h15) hz').elim
  · exfalso; nlinarith [sq_nonneg r]

/-! ## Rational-coordinate consequences -/

theorem square_denominator_one_of_linear_factor_zero
    (A B k : ℤ) (hBpos : 0 < B) (hcop : Int.gcd A B = 1)
    (hzero : A + k * B ^ 2 = 0) : B = 1 := by
  have hBdvdA : B ∣ A := by
    refine ⟨-(k * B), ?_⟩
    nlinarith
  have hBdvdG : B ∣ ((Int.gcd A B : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hBdvdA dvd_rfl
  have hBdvd1 : B ∣ (1 : ℤ) := by simpa [hcop] using hBdvdG
  have hunit : IsUnit B := isUnit_iff_dvd_one.mpr hBdvd1
  rw [Int.isUnit_iff_abs_eq] at hunit
  rwa [abs_of_pos hBpos] at hunit

/-- A vanishing linear factor gives one of the three rational `2`-torsion
abscissas `0,-1,-16`. -/
theorem fullTwo_zero_factor_known_x
    {A B : ℤ} {x : ℚ} (hBpos : 0 < B) (hcop : Int.gcd A B = 1)
    (hx : x = (A : ℚ) / (B : ℚ) ^ 2)
    (hzero : A = 0 ∨ A + B ^ 2 = 0 ∨ A + 16 * B ^ 2 = 0) :
    x = 0 ∨ x = -1 ∨ x = -16 := by
  rcases hzero with hA | h1 | h16
  · left; rw [hx, hA]; simp
  · have hB1 := square_denominator_one_of_linear_factor_zero
      A B 1 hBpos hcop (by simpa using h1)
    have hA : A = -1 := by
      rw [hB1] at h1
      norm_num at h1
      linarith
    right; left
    rw [hx, hB1, hA]
    norm_num
  · have hB1 := square_denominator_one_of_linear_factor_zero
      A B 16 hBpos hcop h16
    have hA : A = -16 := by
      rw [hB1] at h16
      norm_num at h16
      linarith
    right; right
    rw [hx, hB1, hA]
    norm_num

/-- For a nonzero rational point on the original curve, `x` has squareclass
`1` or `-1`. -/
theorem fullTwo_rational_x_squareclass {x y : ℚ}
    (h : FullTwoEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = -(q ^ 2) := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ := fullTwo_integral_model h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    simp
  obtain ⟨r, hr | hr⟩ :=
    fullTwo_first_squareclasses_reduced hcop hA0 hmodel
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    rw [hx, hr]
    push_cast
    field_simp [hBne]
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    rw [hx, hr]
    push_cast
    field_simp [hBne]

/-- For a nonzero rational point on the `2`-isogenous curve, `x` has
squareclass `1` or `5`. -/
theorem isogenous_rational_x_squareclass {x y : ℚ}
    (h : IsogenousEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = 5 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ := isogenous_integral_model h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    simp
  obtain ⟨r, hr | hr⟩ :=
    isogenous_first_squareclasses_reduced hcop hA0 hmodel
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    rw [hx, hr]
    push_cast
    field_simp [hBne]
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    rw [hx, hr]
    push_cast
    field_simp [hBne]

end MazurProof.RationalPointsN15Descent
