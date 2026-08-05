import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.X017RationalPoints

/-!
# An explicit map from the order-seventeen equation

This file gives the algebraic map from the Tate order-seventeen equation to
the integral model

`y² + xy + y = x³ - x² - x - 14`

used for `X₀(17)`.  The map factors through the elliptic curves

`E₇₂ : y² + xy + y = x³ - x² - x`

and

`E₃₆ : y² + xy + y = x³ - x² - 6x - 4`.

The three displayed maps are checked by polynomial identities.  The rational
point classification on the final curve leaves two possible affine fibres.
Their rational points are excluded by a quartic modulo three and by the
irrationality of `√17`.

Only this algebraic implication is used below.  No modular interpretation of
the displayed maps is needed or asserted.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder17Quotient

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model

noncomputable section

/-! ## Normalized Tate coordinates -/

/-- After writing `b = c(d+1)`, the equation `F₁₇(b,c)=0` is
`c¹² H₁₇(d,c)=0`. -/
def H17 (d c : ℚ) : ℚ :=
    c ^ 7 * d + c ^ 7
      - c ^ 6 * d ^ 5 - 5 * c ^ 6 * d ^ 4
      - 10 * c ^ 6 * d ^ 3 - 12 * c ^ 6 * d ^ 2
      - 6 * c ^ 6 * d
      + 9 * c ^ 5 * d ^ 6 + 39 * c ^ 5 * d ^ 5
      + 60 * c ^ 5 * d ^ 4 + 45 * c ^ 5 * d ^ 3
      + 15 * c ^ 5 * d ^ 2
      - 31 * c ^ 4 * d ^ 7 - 112 * c ^ 4 * d ^ 6
      - 141 * c ^ 4 * d ^ 5 - 80 * c ^ 4 * d ^ 4
      - 20 * c ^ 4 * d ^ 3
      + 50 * c ^ 3 * d ^ 8 + 154 * c ^ 3 * d ^ 7
      + 163 * c ^ 3 * d ^ 6 + 75 * c ^ 3 * d ^ 5
      + 15 * c ^ 3 * d ^ 4
      - 39 * c ^ 2 * d ^ 9 - 102 * c ^ 2 * d ^ 8
      - 93 * c ^ 2 * d ^ 7 - 36 * c ^ 2 * d ^ 6
      - 6 * c ^ 2 * d ^ 5
      + 10 * c * d ^ 10 + 25 * c * d ^ 9
      + 21 * c * d ^ 8 + 7 * c * d ^ 7 + c * d ^ 6
      + d ^ 12 + 2 * d ^ 11 + d ^ 10

set_option maxHeartbeats 0 in
/-- The exact normalization identity for the Tate division factor. -/
theorem F17_normalized (d c : ℚ) :
    TateNFDivision.F17 (c * (d + 1)) c = c ^ 12 * H17 d c := by
  simp only [TateNFDivision.F17, H17]
  ring

/-- The normalized order-six factor: `F₆(c(d+1),c) = -c·r₆(d,c)`. -/
def r6 (d c : ℚ) : ℚ := c - d

/-- The normalized order-seven factor: `F₇(c(d+1),c) = c²·r₇(d,c)`. -/
def r7 (d c : ℚ) : ℚ := c - d ^ 2 - d

/-- The normalized order-eight factor: `F₈(c(d+1),c) = -c²·r₈(d,c)`. -/
def r8 (d c : ℚ) : ℚ := c * d + c - 2 * d ^ 2 - d

/-- The normalized order-nine factor satisfies
`F₉(c(d+1),c) = -c³·q(d,c)` and is the numerator of the horizontal
coordinate on `E₇₂`. -/
def q (d c : ℚ) : ℚ := c ^ 2 - c * d - d ^ 3

/-- Polynomial quotient in the division of `H₁₇` by `q`. -/
def quotientS (d c : ℚ) : ℚ :=
    c ^ 5 * (d + 1)
      + c ^ 4 * (-d ^ 5 - 5 * d ^ 4 - 10 * d ^ 3 - 11 * d ^ 2 - 5 * d)
      + c ^ 3 * (8 * d ^ 6 + 34 * d ^ 5 + 51 * d ^ 4 + 35 * d ^ 3
        + 10 * d ^ 2)
      + c ^ 2 * (-d ^ 8 - 28 * d ^ 7 - 88 * d ^ 6 - 101 * d ^ 5
        - 50 * d ^ 4 - 10 * d ^ 3)
      + c * (7 * d ^ 9 + 56 * d ^ 8 + 117 * d ^ 7 + 97 * d ^ 6
        + 35 * d ^ 5 + 5 * d ^ 4)
      - d ^ 11 - 21 * d ^ 10 - 71 * d ^ 9 - 86 * d ^ 8
      - 46 * d ^ 7 - 11 * d ^ 6 - d ^ 5

/-- The linear remainder after division of `H₁₇` by `q`. -/
def remainderL (d c : ℚ) : ℚ :=
    6 * c * d ^ 5 + 35 * c * d ^ 4 + 56 * c * d ^ 3
      + 36 * c * d ^ 2 + 10 * c * d + c
      - d ^ 7 - 21 * d ^ 6 - 70 * d ^ 5 - 84 * d ^ 4
      - 45 * d ^ 3 - 11 * d ^ 2 - d

/-- The normalized division identity used to exclude the cusp fibre. -/
theorem H17_division_identity (d c : ℚ) :
    H17 d c = q d c * quotientS d c + d ^ 7 * remainderL d c := by
  simp only [H17, q, quotientS, remainderL]
  ring

/-- First coefficient in the Bézout certificate for `q` and its remainder. -/
def bezoutA (d : ℚ) : ℚ :=
  (d + 1) ^ 2 * (2 * d + 1) ^ 2 * (3 * d + 1) ^ 2 *
    (d ^ 2 + 4 * d + 1) ^ 2

/-- Second coefficient in the Bézout certificate for `q` and its remainder. -/
def bezoutB (d c : ℚ) : ℚ :=
    -6 * c * d ^ 5 - 35 * c * d ^ 4 - 56 * c * d ^ 3
      - 36 * c * d ^ 2 - 10 * c * d - c
      - d ^ 7 - 15 * d ^ 6 - 35 * d ^ 5 - 28 * d ^ 4
      - 9 * d ^ 3 - d ^ 2

/-- A compact Bézout identity proving that `q=0` and the remainder cannot
occur when `d ≠ 0`. -/
theorem q_remainder_bezout (d c : ℚ) :
    bezoutA d * q d c + bezoutB d c * remainderL d c = d ^ 14 := by
  simp only [bezoutA, bezoutB, q, remainderL]
  ring

/-- The specialization `d=0` of the normalized order-seventeen equation. -/
@[simp] theorem H17_zero (c : ℚ) : H17 0 c = c ^ 7 := by
  simp [H17]

/-- The order-six denominator specialization. -/
theorem H17_r6_zero (d : ℚ) : H17 d d = d ^ 12 := by
  simp only [H17]
  ring

/-- The order-seven denominator specialization. -/
theorem H17_r7_zero (d : ℚ) :
    H17 d (d ^ 2 + d) = -d ^ 15 * (d + 1) ^ 2 := by
  simp only [H17]
  ring

/-- The order-eight denominator specialization. -/
theorem H17_r8_zero (d : ℚ) (hd1 : d + 1 ≠ 0) :
    H17 d (d * (2 * d + 1) / (d + 1)) =
      d ^ 18 / (d + 1) ^ 6 := by
  simp only [H17]
  field_simp [hd1]
  ring

/-- The normalized order-seventeen equation excludes the order-six
denominator. -/
theorem r6_ne_zero {d c : ℚ} (hd : d ≠ 0) (hH : H17 d c = 0) :
    r6 d c ≠ 0 := by
  intro hr6
  have hc : c = d := by
    simpa [r6] using sub_eq_zero.mp hr6
  rw [hc, H17_r6_zero] at hH
  exact hd (eq_zero_of_pow_eq_zero hH)

/-- The normalized order-seventeen equation excludes the order-seven
denominator. -/
theorem r7_ne_zero {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) : r7 d c ≠ 0 := by
  intro hr7
  have hc : c = d ^ 2 + d := by
    simp only [r7] at hr7
    linarith
  rw [hc, H17_r7_zero] at hH
  exact (mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 15 hd))
    (pow_ne_zero 2 hd1)) hH

/-- The normalized order-seventeen equation excludes the order-eight
denominator. -/
theorem r8_ne_zero {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) : r8 d c ≠ 0 := by
  intro hr8
  have hc : c = d * (2 * d + 1) / (d + 1) := by
    apply (eq_div_iff hd1).2
    simp only [r8] at hr8
    linarith
  rw [hc, H17_r8_zero d hd1] at hH
  have hd18 : d ^ 18 = 0 := by
    simpa [pow_ne_zero 6 hd1] using hH
  exact hd (eq_zero_of_pow_eq_zero hd18)

/-- The numerator `q` does not vanish on the normalized
order-seventeen locus. -/
theorem q_ne_zero {d c : ℚ} (hd : d ≠ 0) (hH : H17 d c = 0) :
    q d c ≠ 0 := by
  intro hq
  have hdL : d ^ 7 * remainderL d c = 0 := by
    calc
      d ^ 7 * remainderL d c =
          H17 d c - q d c * quotientS d c := by
            rw [H17_division_identity]
            ring
      _ = 0 := by rw [hH, hq]; ring
  have hL : remainderL d c = 0 :=
    (mul_eq_zero.mp hdL).resolve_left (pow_ne_zero 7 hd)
  have hd14 : d ^ 14 = 0 := by
    calc
      d ^ 14 = bezoutA d * q d c + bezoutB d c * remainderL d c :=
        (q_remainder_bezout d c).symm
      _ = 0 := by rw [hq, hL]; ring
  exact hd (eq_zero_of_pow_eq_zero hd14)

/-! ## The quotient through `E₇₂` and `E₃₆` -/

/-- Numerator of the vertical coordinate on `E₇₂`. -/
def e72YNumerator (d c : ℚ) : ℚ :=
    c ^ 4 * d + 2 * c ^ 4
      - 5 * c ^ 3 * d ^ 2 - 7 * c ^ 3 * d - c ^ 3
      + 9 * c ^ 2 * d ^ 3 + 13 * c ^ 2 * d ^ 2 + 3 * c ^ 2 * d
      - c * d ^ 5 - 12 * c * d ^ 4 - 13 * c * d ^ 3 - 3 * c * d ^ 2
      + 3 * d ^ 6 + 7 * d ^ 5 + 5 * d ^ 4 + d ^ 3

/-- Horizontal coordinate of the normalized point on `E₇₂`. -/
def e72X (d c : ℚ) : ℚ := q d c / (d * r8 d c)

/-- Vertical coordinate of the normalized point on `E₇₂`. -/
def e72Y (d c : ℚ) : ℚ :=
  e72YNumerator d c / (r7 d c * r8 d c ^ 2)

/-- Residual of the affine equation of `E₇₂`. -/
def E72Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + x

set_option maxHeartbeats 0 in
/-- The explicit quotient coordinates satisfy `E₇₂` when `H₁₇=0`. -/
theorem e72_residual_identity {d c : ℚ}
    (hd : d ≠ 0) (hr7 : r7 d c ≠ 0) (hr8 : r8 d c ≠ 0) :
    E72Residual (e72X d c) (e72Y d c) =
      -(q d c) * H17 d c /
        (d ^ 3 * r7 d c ^ 2 * r8 d c ^ 4) := by
  simp only [E72Residual, e72X, e72Y]
  field_simp [hd, hr7, hr8]
  simp only [e72YNumerator, H17, q, r7, r8]
  ring

/-- The first degree-two quotient horizontal coordinate. -/
def e36X (x : ℚ) : ℚ :=
  (x ^ 3 - 2 * x ^ 2 + 2 * x - 1) / (x - 1) ^ 2

/-- The first degree-two quotient vertical coordinate. -/
def e36Y (x y : ℚ) : ℚ :=
  (y * x ^ 3 + (-3 * y - 1) * x ^ 2 + (2 * y + 1) * x) /
    (x - 1) ^ 3

/-- Residual of the affine equation of `E₃₆`. -/
def E36Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + 6 * x + 4

/-- The first degree-two map preserves the Weierstrass equations. -/
theorem e36_residual_identity {x y : ℚ} (hx : x ≠ 1) :
    E36Residual (e36X x) (e36Y x y) =
      x ^ 2 * (x - 2) ^ 2 / (x - 1) ^ 4 * E72Residual x y := by
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  simp only [E36Residual, E72Residual, e36X, e36Y]
  field_simp [hx']
  ring

/-- The second degree-two quotient horizontal coordinate. -/
def x017X (x : ℚ) : ℚ :=
  (x ^ 3 + 2 * x ^ 2 - 1) / (x + 1) ^ 2

/-- The second degree-two quotient vertical coordinate. -/
def x017Y (x y : ℚ) : ℚ :=
  (y * x ^ 3 + (3 * y + 1) * x ^ 2 + (4 * y + 2) * x +
      (2 * y + 1)) / (x + 1) ^ 3

/-- Residual of the integral `X₀(17)` equation. -/
def X017Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + x + 14

/-- The second degree-two map preserves the Weierstrass equations. -/
theorem x017_residual_identity {x y : ℚ} (hx : x ≠ -1) :
    X017Residual (x017X x) (x017Y x y) =
      (x ^ 2 + 2 * x + 2) ^ 2 / (x + 1) ^ 4 *
        E36Residual x y := by
  have hx' : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  simp only [X017Residual, E36Residual, x017X, x017Y]
  field_simp [hx']
  ring

/-- The first quotient horizontal coordinate satisfies a useful kernel
identity. -/
theorem e36X_add_one {x : ℚ} (hx : x ≠ 1) :
    e36X x + 1 = x ^ 2 / (x - 1) := by
  simp only [e36X]
  field_simp [sub_ne_zero.mpr hx]
  ring

/-- The composite horizontal coordinate, written only in terms of the
`E₇₂` horizontal coordinate. -/
def compositeX (x : ℚ) : ℚ :=
  (x ^ 4 - x ^ 3 + 2 * x - 1) / (x ^ 2 * (x - 1))

/-- The two degree-two maps have the displayed composite horizontal
coordinate. -/
theorem x017X_e36X {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    x017X (e36X x) = compositeX x := by
  have hu : e36X x + 1 ≠ 0 := by
    rw [e36X_add_one hx1]
    exact div_ne_zero (pow_ne_zero 2 hx0) (sub_ne_zero.mpr hx1)
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [x017X, compositeX]
  field_simp [hx0, hx', hu]
  simp only [e36X]
  field_simp [hx']
  ring

/-! ## The two remaining affine fibres -/

/-- The polynomial forced by the affine fibre with integral
horizontal coordinate `7`. -/
def sevenFiber : Polynomial ℤ :=
  X ^ 4 - C 8 * X ^ 3 + C 7 * X ^ 2 + C 2 * X - C 1

/-- The fibre polynomial is monic over the integers. -/
theorem sevenFiber_monic : sevenFiber.Monic := by
  unfold sevenFiber
  monicity!

/-- The fibre polynomial has no root modulo three. -/
theorem sevenFiber_no_root_mod3 (z : ZMod 3) :
    aeval z sevenFiber ≠ 0 := by
  fin_cases z <;> simp [sevenFiber, aeval_def] <;> decide

/-- Hence the fibre polynomial has no rational root. -/
theorem sevenFiber_no_rational_root (x : ℚ) :
    aeval x sevenFiber ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ :=
    exists_integer_of_is_root_of_monic sevenFiber_monic hx
  have hint : aeval z sevenFiber = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) sevenFiber = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 3) z) sevenFiber = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact sevenFiber_no_root_mod3 _ hmod

/-- Seventeen is not a square in the rational numbers. -/
theorem sq_ne_seventeen (x : ℚ) : x ^ 2 ≠ 17 := by
  intro hx
  let p : Polynomial ℤ := X ^ 2 - C 17
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    linarith
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hzsq : z ^ 2 = (17 : ℤ) := by
    rw [hz] at hx
    apply Int.cast_injective (α := ℚ)
    simpa using hx
  have hzlt : z < 5 := by
    nlinarith [sq_nonneg (z - 5)]
  have hzgt : -5 < z := by
    nlinarith [sq_nonneg (z + 5)]
  interval_cases z <;> norm_num at hzsq

/-- The fibre `x=7` gives the monic quartic `sevenFiber`. -/
theorem compositeX_eq_seven {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h : compositeX x = 7) :
    x ^ 4 - 8 * x ^ 3 + 7 * x ^ 2 + 2 * x - 1 = 0 := by
  simp only [compositeX] at h
  field_simp [hx0, sub_ne_zero.mpr hx1] at h
  linarith

/-- The fibre `x=11/4` splits into a double linear factor and a quadratic
of discriminant seventeen. -/
theorem compositeX_eq_eleven_fourths {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h : compositeX x = 11 / 4) :
    (x - 2) ^ 2 * (4 * x ^ 2 + x - 1) = 0 := by
  simp only [compositeX] at h
  field_simp [hx0, sub_ne_zero.mpr hx1] at h
  nlinarith

/-! ## Assembly -/

/-- The integral-to-standard coordinate change carries the integral residual
to sixty-four times itself. -/
theorem standard_residual_identity (x y : ℚ) :
    (8 * y + 4 * x + 4) ^ 2 -
        (4 * x - 11) * ((4 * x - 11) ^ 2 +
          30 * (4 * x - 11) + 289) =
      64 * X017Residual x y := by
  simp only [X017Residual]
  ring

set_option maxHeartbeats 0 in
/-- The explicit quotient of a nondegenerate Tate solution gives an affine
point on the standard `X₀(17)` model whose integral horizontal coordinate is
one of the two possible affine values. -/
theorem quotient_integral_x_eq
    {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) :
    let ex := e72X d c
    let ux := e36X ex
    let vx := x017X ux
    vx = 7 ∨ vx = 11 / 4 := by
  have hr6 := r6_ne_zero hd hH
  have hr7 := r7_ne_zero hd hd1 hH
  have hr8 := r8_ne_zero hd hd1 hH
  have hq := q_ne_zero hd hH
  let ex := e72X d c
  let ey := e72Y d c
  have hex0 : ex ≠ 0 := by
    exact div_ne_zero hq (mul_ne_zero hd hr8)
  have hex1 : ex ≠ 1 := by
    intro hex
    have hnum : q d c = d * r8 d c := by
      dsimp [ex, e72X] at hex
      field_simp [hd, hr8] at hex
      exact hex
    have hprod : r6 d c * r7 d c = 0 := by
      simp only [q, r6, r7, r8] at hnum ⊢
      linear_combination hnum
    exact (mul_ne_zero hr6 hr7) hprod
  have hE72 : E72Residual ex ey = 0 := by
    rw [e72_residual_identity hd hr7 hr8, hH]
    ring
  let ux := e36X ex
  let uy := e36Y ex ey
  have hE36 : E36Residual ux uy = 0 := by
    dsimp [ux, uy]
    rw [e36_residual_identity hex1, hE72]
    ring
  have hux1 : ux ≠ -1 := by
    have hplus : ux + 1 ≠ 0 := by
      dsimp [ux]
      rw [e36X_add_one hex1]
      exact div_ne_zero (pow_ne_zero 2 hex0) (sub_ne_zero.mpr hex1)
    exact fun h => hplus (by rw [h]; norm_num)
  let vx := x017X ux
  let vy := x017Y ux uy
  have hX017 : X017Residual vx vy = 0 := by
    dsimp [vx, vy]
    rw [x017_residual_identity hux1, hE36]
    ring
  let Xs : ℚ := 4 * vx - 11
  let Ys : ℚ := 8 * vy + 4 * vx + 4
  have hstandard : Ys ^ 2 = Xs * (Xs ^ 2 + 30 * Xs + 289) := by
    have h := standard_residual_identity vx vy
    rw [hX017, mul_zero] at h
    dsimp [Xs, Ys]
    linarith
  have hns : Nonsingular standard Xs Ys := by
    apply equation_iff_nonsingular.mp
    rw [StandardTwoIsogeny.curve_equation]
    norm_num [a17, b17, veluT]
    exact hstandard
  let P : Point standard := Point.some Xs Ys hns
  rcases X017RationalPoints.eq_zero_or_K_or_T_or_neg_T P with
      hP | hP | hP | hP
  · exact False.elim ((Point.some_ne_zero hns) hP)
  · right
    dsimp [P] at hP
    unfold K StandardTwoIsogeny.kernelPoint at hP
    rw [Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]
  · left
    dsimp [P] at hP
    unfold T at hP
    rw [Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]
  · left
    dsimp [P] at hP
    unfold T at hP
    rw [Point.neg_some, Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]

set_option maxHeartbeats 0 in
/-- The Tate residual `F₁₇` has no rational solution with `b ≠ 0`. -/
theorem no_F17_rational_solution
    (b c : ℚ) (hb : b ≠ 0) :
    TateNFDivision.F17 b c ≠ 0 := by
  intro hF17
  have hc : c ≠ 0 := by
    intro hc
    subst c
    norm_num [TateNFDivision.F17] at hF17
    exact hb hF17
  let d : ℚ := b / c - 1
  have hbcoord : b = c * (d + 1) := by
    dsimp [d]
    field_simp [hc]
    ring
  have hH : H17 d c = 0 := by
    rw [hbcoord, F17_normalized] at hF17
    exact (mul_eq_zero.mp hF17).resolve_left (pow_ne_zero 12 hc)
  have hd : d ≠ 0 := by
    intro hd
    rw [hd, H17_zero] at hH
    exact hc (eq_zero_of_pow_eq_zero hH)
  have hd1 : d + 1 ≠ 0 := by
    intro hd1
    rw [hd1, mul_zero] at hbcoord
    exact hb hbcoord
  have hxcase := quotient_integral_x_eq hd hd1 hH
  let ex := e72X d c
  let ey := e72Y d c
  let ux := e36X ex
  let uy := e36Y ex ey
  let vx := x017X ux
  have hr6 := r6_ne_zero hd hH
  have hr7 := r7_ne_zero hd hd1 hH
  have hr8 := r8_ne_zero hd hd1 hH
  have hq := q_ne_zero hd hH
  have hex0 : ex ≠ 0 :=
    div_ne_zero hq (mul_ne_zero hd hr8)
  have hex1 : ex ≠ 1 := by
    intro hex
    have hnum : q d c = d * r8 d c := by
      dsimp [ex, e72X] at hex
      field_simp [hd, hr8] at hex
      exact hex
    have hprod : r6 d c * r7 d c = 0 := by
      simp only [q, r6, r7, r8] at hnum ⊢
      linear_combination hnum
    exact (mul_ne_zero hr6 hr7) hprod
  have hcomposite : vx = compositeX ex := by
    dsimp [vx, ux]
    exact x017X_e36X hex0 hex1
  rcases hxcase with hx7 | hx11
  · have hroot :
        ex ^ 4 - 8 * ex ^ 3 + 7 * ex ^ 2 + 2 * ex - 1 = 0 :=
      compositeX_eq_seven hex0 hex1 (by
        rw [← hcomposite]
        simpa only [vx, ux, ex] using hx7)
    apply sevenFiber_no_rational_root ex
    simp [sevenFiber, aeval_def]
    exact hroot
  · have hfactor :
        (ex - 2) ^ 2 * (4 * ex ^ 2 + ex - 1) = 0 :=
      compositeX_eq_eleven_fourths hex0 hex1
        (by
          rw [← hcomposite]
          simpa only [vx, ux, ex] using hx11)
    rcases mul_eq_zero.mp hfactor with hex2 | hquad
    · have hex2' : ex = 2 :=
        sub_eq_zero.mp (eq_zero_of_pow_eq_zero hex2)
      have hE72 : E72Residual ex ey = 0 := by
        rw [e72_residual_identity hd hr7 hr8, hH]
        ring
      have hsquare : (2 * ey + 3) ^ 2 = 17 := by
        rw [hex2'] at hE72
        simp only [E72Residual] at hE72
        nlinarith
      exact sq_ne_seventeen (2 * ey + 3) hsquare
    · have hsquare : (8 * ex + 1) ^ 2 = 17 := by
        nlinarith
      exact sq_ne_seventeen (8 * ex + 1) hsquare

end

end MazurProof.TateOrder17Quotient
