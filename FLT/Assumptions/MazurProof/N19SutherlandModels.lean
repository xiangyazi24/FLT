import FLT.Assumptions.MazurProof.TateNFDivision

/-!
# Explicit affine models for the order-nineteen Tate equation

This file records Sutherland's raw and optimized affine models of `X₁(19)`.
It also gives the direct algebraic quotient of the optimized model by the
order-three diamond action:

`V² + V = U³ + U² + U`.

All maps are verified by polynomial identities.  No modular interpretation
of the formulas is used below.
-/

namespace MazurProof.N19SutherlandModels

noncomputable section

/-! ## The raw and optimized equations -/

/-- Sutherland's raw equation in the Tate parameters
`b = r s (r - 1)` and `c = s (r - 1)`. -/
def rawF19 (r s : ℚ) : ℚ :=
    r ^ 6
      - r ^ 5 * s ^ 7 + 11 * r ^ 5 * s ^ 6 - 48 * r ^ 5 * s ^ 5
      + 105 * r ^ 5 * s ^ 4 - 121 * r ^ 5 * s ^ 3
      + 69 * r ^ 5 * s ^ 2 - 20 * r ^ 5 * s - r ^ 5
      - 2 * r ^ 4 * s ^ 7 + 12 * r ^ 4 * s ^ 6 - 9 * r ^ 4 * s ^ 5
      - 60 * r ^ 4 * s ^ 4 + 144 * r ^ 4 * s ^ 3
      - 105 * r ^ 4 * s ^ 2 + 35 * r ^ 4 * s
      - 3 * r ^ 3 * s ^ 7 + 3 * r ^ 3 * s ^ 6 + 21 * r ^ 3 * s ^ 5
      - 30 * r ^ 3 * s ^ 4 - 41 * r ^ 3 * s ^ 3
      + 51 * r ^ 3 * s ^ 2 - 21 * r ^ 3 * s
      + r ^ 2 * s ^ 9 - 6 * r ^ 2 * s ^ 8 + 21 * r ^ 2 * s ^ 7
      - 50 * r ^ 2 * s ^ 6 + 66 * r ^ 2 * s ^ 5
      - 31 * r ^ 2 * s ^ 4 + 25 * r ^ 2 * s ^ 3
      - 18 * r ^ 2 * s ^ 2 + 7 * r ^ 2 * s
      + 3 * r * s ^ 6 - 15 * r * s ^ 5 + 10 * r * s ^ 4
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6

set_option maxHeartbeats 0 in
/-- The repository division factor and the raw equation differ only by
the displayed Tate-boundary factors. -/
theorem F19_raw_identity (r s : ℚ) :
    TateNFDivision.F19 (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 15 * (r - 1) ^ 24 * rawF19 r s := by
  simp only [TateNFDivision.F19, rawF19]
  ring

/-- Sutherland's optimized affine plane equation for `X₁(19)`. -/
def optF19 (x y : ℚ) : ℚ :=
    y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2

/-! ## The raw-to-optimized chart -/

/-- The common denominator in Sutherland's raw-to-optimized chart. -/
def rawDelta (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

/-- The first numerator in the raw-to-optimized chart. -/
def rawXFactor (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

/-- The horizontal coordinate in Sutherland's optimized chart. -/
def rawToOptX (r s : ℚ) : ℚ :=
  -(s - 1) * rawXFactor r s / rawDelta r s

/-- The second numerator in the raw-to-optimized chart. -/
def rawYNumerator (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1

/-- The vertical coordinate in Sutherland's optimized chart. -/
def rawToOptY (r s : ℚ) : ℚ :=
  (s - 1) * rawYNumerator r s / ((r - s) * rawDelta r s)

/-- Specializing the raw equation to `r=s` leaves only boundary factors. -/
theorem rawF19_r_eq_s (s : ℚ) :
    rawF19 s s = -s ^ 2 * (s - 1) ^ 10 := by
  simp only [rawF19]
  ring

/-- Specializing the raw equation to `s=1` leaves the factor `(r-1)⁶`. -/
theorem rawF19_s_one (r : ℚ) :
    rawF19 r 1 = (r - 1) ^ 6 := by
  simp only [rawF19]
  ring

/-- The raw equation after solving `rawXFactor r s = 0` for `s`. -/
theorem rawF19_x_factor_zero (r : ℚ) (hr : r ≠ 0) :
    rawF19 r ((2 * r - 1) / r) = (r - 1) ^ 13 / r ^ 7 := by
  simp only [rawF19]
  field_simp [hr]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The raw equation after solving `rawDelta r s = 0` for `r`. -/
theorem rawF19_delta_zero (s : ℚ) (hsq : s ^ 2 - 3 * s + 1 ≠ 0) :
    rawF19 (-s ^ 2 / (s ^ 2 - 3 * s + 1)) s =
      s ^ 3 * (s - 1) ^ 18 / (s ^ 2 - 3 * s + 1) ^ 6 := by
  let q : ℚ := s ^ 2 - 3 * s + 1
  have hq : q ≠ 0 := by simpa [q] using hsq
  change rawF19 (-s ^ 2 / q) s = s ^ 3 * (s - 1) ^ 18 / q ^ 6
  apply (eq_div_iff (pow_ne_zero 6 hq)).2
  simp only [rawF19]
  field_simp [hq]
  dsimp only [q]
  ring

/-- A nonboundary raw point does not lie on the diagonal `r=s`. -/
theorem raw_r_sub_s_ne_zero {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    r - s ≠ 0 := by
  intro hrs
  have hrseq : r = s := sub_eq_zero.mp hrs
  rw [hrseq, rawF19_r_eq_s] at hraw
  exact (mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 2 hs))
    (pow_ne_zero 10 (sub_ne_zero.mpr (by
      intro h
      apply hr1
      rw [hrseq, h]
      norm_num)))) hraw

/-- A nonboundary raw point has `s ≠ 1`. -/
theorem raw_s_sub_one_ne_zero {r s : ℚ}
    (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    s - 1 ≠ 0 := by
  intro hs
  have hseq : s = 1 := sub_eq_zero.mp hs
  rw [hseq, rawF19_s_one] at hraw
  exact pow_ne_zero 6 hr1 hraw

/-- The first horizontal numerator is nonzero at a nonboundary raw point. -/
theorem rawXFactor_ne_zero {r s : ℚ}
    (hr : r ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    rawXFactor r s ≠ 0 := by
  intro hx
  have hs : s = (2 * r - 1) / r := by
    apply (eq_div_iff hr).2
    simp only [rawXFactor] at hx
    linarith
  rw [hs, rawF19_x_factor_zero r hr] at hraw
  have : (r - 1) ^ 13 = 0 := by
    simpa [pow_ne_zero 7 hr] using hraw
  exact hr1 (eq_zero_of_pow_eq_zero this)

/-- The common chart denominator is nonzero at a nonboundary raw point. -/
theorem rawDelta_ne_zero {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    rawDelta r s ≠ 0 := by
  intro hdelta
  have hcoef : s ^ 2 - 3 * s + 1 ≠ 0 := by
    intro hzero
    have hs2 : s ^ 2 = 0 := by
      simp only [rawDelta] at hdelta
      linear_combination hdelta - r * hzero
    exact hs (eq_zero_of_pow_eq_zero hs2)
  have hr : r = -s ^ 2 / (s ^ 2 - 3 * s + 1) := by
    apply (eq_div_iff hcoef).2
    simp only [rawDelta] at hdelta
    linear_combination hdelta
  rw [hr, rawF19_delta_zero s hcoef] at hraw
  have hprod : s ^ 3 * (s - 1) ^ 18 = 0 := by
    simpa [pow_ne_zero 6 hcoef] using hraw
  rcases mul_eq_zero.mp hprod with hs3 | hs1
  · exact hs (eq_zero_of_pow_eq_zero hs3)
  · have hsone : s = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs1)
    rw [hsone] at hr
    norm_num at hr
    exact hr1 (sub_eq_zero.mpr hr)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The raw-to-optimized chart carries the raw equation to the optimized
equation, with an explicit residual factor. -/
theorem raw_to_opt_residual_identity {r s : ℚ}
    (hrs : r - s ≠ 0) (hdelta : rawDelta r s ≠ 0) :
    optF19 (rawToOptX r s) (rawToOptY r s) =
      (s - 1) ^ 2 * (s ^ 2 - r - s + 1) ^ 2 *
          rawXFactor r s ^ 4 /
        ((s - r) ^ 5 * rawDelta r s ^ 7) * rawF19 r s := by
  simp only [optF19, rawToOptX, rawToOptY]
  have hsr : s - r ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hrs))
  have hry : (r - s) * rawDelta r s ≠ 0 :=
    mul_ne_zero hrs hdelta
  field_simp [hrs, hsr, hdelta, hry]
  simp only [rawYNumerator, rawXFactor, rawDelta, rawF19]
  ring

/-- The optimized horizontal coordinate is nonzero on the nonboundary
raw locus. -/
theorem rawToOptX_ne_zero {r s : ℚ}
    (hs1 : s - 1 ≠ 0) (hx : rawXFactor r s ≠ 0)
    (hdelta : rawDelta r s ≠ 0) :
    rawToOptX r s ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hs1) hx) hdelta

/-! ## The order-three quotient of the optimized model -/

/-- Numerator of the horizontal quotient coordinate. -/
def diamondUNumerator (x y : ℚ) : ℚ :=
    y ^ 4
      - (x ^ 2 + 1) * y ^ 3
      - x * (2 * x ^ 2 + 3 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 3 + 3 * x ^ 2 + 5 * x + 4) * y
      - x ^ 2 * (x + 1)

/-- Numerator of the vertical quotient coordinate. -/
def diamondVNumerator (x y : ℚ) : ℚ :=
    (x + 1) * y ^ 4
      - (x ^ 3 + x ^ 2 + x + 1) * y ^ 3
      - x * (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 4 + 4 * x ^ 3 + 8 * x ^ 2 + 9 * x + 5) * y
      - x ^ 2 * (x ^ 2 + 3 * x + 2)

/-- Horizontal coordinate on the genus-one diamond quotient. -/
def diamondU (x y : ℚ) : ℚ :=
  diamondUNumerator x y / x ^ 3

/-- Vertical coordinate on the genus-one diamond quotient. -/
def diamondV (x y : ℚ) : ℚ :=
  diamondVNumerator x y / x ^ 3

/-- Residual of the elliptic equation `V²+V=U³+U²+U`. -/
def diamondResidual (u v : ℚ) : ℚ :=
  v ^ 2 + v - u ^ 3 - u ^ 2 - u

/-- Polynomial certificate for the quotient residual identity. -/
def diamondCertificate (x y : ℚ) : ℚ :=
    y ^ 7
      - (2 * x ^ 2 + 1) * y ^ 6
      + (x ^ 4 - 4 * x ^ 3 - 6 * x ^ 2 - x) * y ^ 5
      + (6 * x ^ 5 + 13 * x ^ 4 + 11 * x ^ 3 + 9 * x ^ 2) * y ^ 4
      + (-2 * x ^ 7 - 2 * x ^ 6 + 5 * x ^ 5 + 6 * x ^ 4 -
          2 * x ^ 2) * y ^ 3
      + (-4 * x ^ 8 - 19 * x ^ 7 - 38 * x ^ 6 - 41 * x ^ 5 -
          21 * x ^ 4 - x ^ 3) * y ^ 2
      + (x ^ 10 + 6 * x ^ 9 + 17 * x ^ 8 + 29 * x ^ 7 +
          32 * x ^ 6 + 23 * x ^ 5 + 9 * x ^ 4) * y
      - x ^ 8 - 4 * x ^ 7 - 7 * x ^ 6 - 5 * x ^ 5 - x ^ 4

set_option maxHeartbeats 0 in
/-- The explicit quotient coordinates satisfy the genus-one equation on the
optimized order-nineteen locus. -/
theorem diamond_residual_identity {x y : ℚ} (hx : x ≠ 0) :
    diamondResidual (diamondU x y) (diamondV x y) =
      -diamondCertificate x y * optF19 x y / x ^ 9 := by
  simp only [diamondResidual, diamondU, diamondV, diamondUNumerator,
    diamondVNumerator, diamondCertificate, optF19]
  field_simp [hx]
  ring

/-! ## The zero horizontal fibre -/

/-- First coefficient in the Bézout certificate for the zero horizontal
fibre of the diamond quotient. -/
def zeroFiberBezoutA (x y : ℚ) : ℚ :=
    (x ^ 2 - x - 1) * y ^ 3
      + (-x ^ 4 + x ^ 3 - x) * y ^ 2
      + (-2 * x ^ 5 - x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 7 + 2 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2

/-- Second coefficient in the Bézout certificate for the zero horizontal
fibre of the diamond quotient. -/
def zeroFiberBezoutB (x y : ℚ) : ℚ :=
    (-x ^ 2 + x + 1) * y ^ 4
      + (x ^ 4 - x ^ 3 + x ^ 2 - 1) * y ^ 3
      + (2 * x ^ 5 - 3 * x ^ 3 - 4 * x ^ 2 - 2 * x) * y ^ 2
      + (-x ^ 7 - 2 * x ^ 6 - 4 * x ^ 5 - x ^ 4 +
          4 * x ^ 3 + 2 * x ^ 2) * y
      + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2

/-- The optimized equation and the zero horizontal numerator force
`x⁷(x+1)²=0`. -/
theorem zero_fiber_bezout (x y : ℚ) :
    zeroFiberBezoutA x y * optF19 x y +
        zeroFiberBezoutB x y * diamondUNumerator x y =
      x ^ 7 * (x + 1) ^ 2 := by
  simp only [zeroFiberBezoutA, zeroFiberBezoutB, optF19,
    diamondUNumerator]
  ring

/-- A nonzero optimized point in the zero horizontal fibre has `x=-1`. -/
theorem x_eq_neg_one_of_diamondU_eq_zero {x y : ℚ}
    (hx : x ≠ 0) (hopt : optF19 x y = 0)
    (hU : diamondU x y = 0) :
    x = -1 := by
  have hUN : diamondUNumerator x y = 0 := by
    simp only [diamondU] at hU
    exact (div_eq_zero_iff).mp hU |>.resolve_right (pow_ne_zero 3 hx)
  have hprod : x ^ 7 * (x + 1) ^ 2 = 0 := by
    rw [← zero_fiber_bezout x y, hopt, hUN]
    ring
  have hplus : (x + 1) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 7 hx)
  linarith [eq_zero_of_pow_eq_zero hplus]

/-- The equation `rawToOptX r s = -1` forces a boundary point of the raw
order-nineteen equation. -/
theorem rawToOptX_ne_neg_one {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0)
    (hdelta : rawDelta r s ≠ 0) :
    rawToOptX r s ≠ -1 := by
  intro hx
  have hboundary : s ^ 2 - r - s + 1 = 0 := by
    simp only [rawToOptX] at hx
    field_simp [hdelta] at hx
    simp only [rawXFactor, rawDelta] at hx
    linear_combination hx
  have hr : r = s ^ 2 - s + 1 := by
    linarith
  rw [hr] at hraw hr1
  have hspecial : rawF19 (s ^ 2 - s + 1) s =
      -s * (s - 1) ^ 16 := by
    simp only [rawF19]
    ring
  rw [hspecial] at hraw
  have hs1 : s - 1 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp hraw).resolve_left (neg_ne_zero.mpr hs))
  apply hr1
  rw [sub_eq_zero.mp hs1]
  norm_num

end

end MazurProof.N19SutherlandModels
