import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# The Sutherland source model for the order-25 Tate locus

Andrew Sutherland's explicit models of `X₁(N)` use the raw coordinates

```
r = b / c,        s = c² / (b - c),
```

and then the birational optimization

```
x = (s - r) / (r*s - 2*r + 1),
y = (r*s - 2*r + 1) / (s² - s - r + 1).
```

This file verifies that comparison for `N = 25` directly against the primitive
Tate division polynomial `F25`.  After simplifying the composite map, it proves
an unconditional denominator-cleared polynomial identity and proves that both
remaining denominators are nonzero on the exact-order locus.  The endpoint is
therefore an explicit rational map from every primitive Tate solution to
Sutherland's bidegree-`(8,8)` plane model.

The formulas are kept as literal polynomials, and every model comparison below
is certified by `ring`; no modular-curve identification is introduced as an
assumption.  This closes the Tate-to-optimized-source part of the N25 comparison.
-/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option maxRecDepth 20000
set_option linter.style.longLine false

/-! ## The simplified Tate-to-Sutherland coordinates -/

/-- Numerator `X = c³ - b(b-c)` of the optimized coordinate
`x = (s-r)/(r*s-2*r+1)` after substituting `r=b/c` and `s=c²/(b-c)`. -/
def tateToSutherlandXNum25 (b c : ℚ) : ℚ := -b ^ 2 + b * c + c ^ 3

/-- Common numerator `K` of `r*s-2*r+1`.  On the Tate chart,
`r*s-2*r+1 = K / (c(b-c))`; it is also the denominator of optimized `x`
and a numerator factor of optimized `y`. -/
def tateToSutherlandCommon25 (b c : ℚ) : ℚ := -2 * b ^ 2 + b * c ^ 2 + 3 * b * c - c ^ 2

/-- Numerator `B` of `s²-s-r+1` after the Tate substitution:
`s²-s-r+1 = B / (c(b-c)²)`.  Hence the optimized second coordinate is
`y = K(b-c)/B`. -/
def tateToSutherlandYDen25 (b c : ℚ) : ℚ :=
  -b ^ 3 + 3 * b ^ 2 * c - b * c ^ 3 - 3 * b * c ^ 2 + c ^ 5 + c ^ 4 + c ^ 3

/-- Numerator `c²-b+c` of `s-1 = (c²-b+c)/(b-c)`.  It appears as the
third exceptional factor in the denominator-cleared model identity. -/
def tateToSutherlandSMinusOneNum25 (b c : ℚ) : ℚ := c ^ 2 - b + c

/-! ## Sutherland's optimized and raw equations -/

/-- Sutherland's bidegree-`(8,8)` affine equation for `X₁(25)`.  The source
publishes this polynomial as `X1/FFFc25.txt`; the coordinate convention is the
optimized `(x,y)` convention stated in the module documentation. -/
def sutherlandX1Plane25 (x y : ℚ) : ℚ :=
  x ^ 8 * y ^ 2 + x ^ 7 * y ^ 5 - 4 * x ^ 7 * y ^ 4 - x ^ 7 * y ^ 2 -
  3 * x ^ 6 * y ^ 6 + 11 * x ^ 6 * y ^ 5 - 2 * x ^ 6 * y ^ 4 +
  2 * x ^ 6 * y ^ 2 - 2 * x ^ 6 * y + 3 * x ^ 5 * y ^ 7 -
  9 * x ^ 5 * y ^ 6 - 4 * x ^ 5 * y ^ 5 + 4 * x ^ 5 * y ^ 4 -
  2 * x ^ 5 * y ^ 3 + 4 * x ^ 5 * y ^ 2 - x ^ 4 * y ^ 8 +
  x ^ 4 * y ^ 7 + 9 * x ^ 4 * y ^ 6 - 5 * x ^ 4 * y ^ 5 +
  6 * x ^ 4 * y ^ 4 - 15 * x ^ 4 * y ^ 3 + 7 * x ^ 4 * y ^ 2 -
  2 * x ^ 4 * y + x ^ 4 + x ^ 3 * y ^ 8 - 4 * x ^ 3 * y ^ 7 +
  3 * x ^ 3 * y ^ 6 - 14 * x ^ 3 * y ^ 5 + 26 * x ^ 3 * y ^ 4 -
  15 * x ^ 3 * y ^ 3 + 7 * x ^ 3 * y ^ 2 - 5 * x ^ 3 * y + x ^ 3 -
  x ^ 2 * y ^ 7 + 8 * x ^ 2 * y ^ 6 - 13 * x ^ 2 * y ^ 5 +
  12 * x ^ 2 * y ^ 4 - 18 * x ^ 2 * y ^ 3 + 19 * x ^ 2 * y ^ 2 -
  8 * x ^ 2 * y + x ^ 2 - 4 * x * y ^ 5 + 13 * x * y ^ 4 -
  16 * x * y ^ 3 + 10 * x * y ^ 2 - 4 * x * y + x + y ^ 4 -
  4 * y ^ 3 + 6 * y ^ 2 - 4 * y + 1

set_option maxHeartbeats 1000000 in
/-- Sutherland's raw equation `F(r,s)=0` for `X₁(25)`, before the universal
birational optimization.  Its bidegrees are `10` in `r` and `15` in `s`.
This is deliberately distinct from the repository's Tate polynomial `F25`. -/
def sutherlandRawX1Plane25 (r s : ℚ) : ℚ :=
  r ^ 10 - r ^ 9 * s ^ 10 + 17 * r ^ 9 * s ^ 9 - 123 * r ^ 9 * s ^ 8 +
  494 * r ^ 9 * s ^ 7 - 1205 * r ^ 9 * s ^ 6 + 1836 * r ^ 9 * s ^ 5 -
  1732 * r ^ 9 * s ^ 4 + 968 * r ^ 9 * s ^ 3 - 294 * r ^ 9 * s ^ 2 +
  35 * r ^ 9 * s - 5 * r ^ 9 - 6 * r ^ 8 * s ^ 10 + 74 * r ^ 8 * s ^ 9 -
  345 * r ^ 8 * s ^ 8 + 690 * r ^ 8 * s ^ 7 - 185 * r ^ 8 * s ^ 6 -
  1659 * r ^ 8 * s ^ 5 + 3051 * r ^ 8 * s ^ 4 - 2320 * r ^ 8 * s ^ 3 +
  840 * r ^ 8 * s ^ 2 - 105 * r ^ 8 * s + 10 * r ^ 8 -
  21 * r ^ 7 * s ^ 10 + 161 * r ^ 7 * s ^ 9 - 351 * r ^ 7 * s ^ 8 -
  144 * r ^ 7 * s ^ 7 + 1289 * r ^ 7 * s ^ 6 - 789 * r ^ 7 * s ^ 5 -
  1551 * r ^ 7 * s ^ 4 + 2166 * r ^ 7 * s ^ 3 - 996 * r ^ 7 * s ^ 2 +
  126 * r ^ 7 * s - 10 * r ^ 7 + r ^ 6 * s ^ 15 - 18 * r ^ 6 * s ^ 14 +
  151 * r ^ 6 * s ^ 13 - 770 * r ^ 6 * s ^ 12 + 2655 * r ^ 6 * s ^ 11 -
  6558 * r ^ 6 * s ^ 10 + 11834 * r ^ 6 * s ^ 9 - 15408 * r ^ 6 * s ^ 8 +
  14630 * r ^ 6 * s ^ 7 - 11195 * r ^ 6 * s ^ 6 + 7227 * r ^ 6 * s ^ 5 -
  2441 * r ^ 6 * s ^ 4 - 388 * r ^ 6 * s ^ 3 + 555 * r ^ 6 * s ^ 2 -
  70 * r ^ 6 * s + 5 * r ^ 6 + r ^ 5 * s ^ 15 - 15 * r ^ 5 * s ^ 14 +
  90 * r ^ 5 * s ^ 13 - 245 * r ^ 5 * s ^ 12 + 90 * r ^ 5 * s ^ 11 +
  1587 * r ^ 5 * s ^ 10 - 6145 * r ^ 5 * s ^ 9 + 12270 * r ^ 5 * s ^ 8 -
  15060 * r ^ 5 * s ^ 7 + 12520 * r ^ 5 * s ^ 6 - 8214 * r ^ 5 * s ^ 5 +
  3660 * r ^ 5 * s ^ 4 - 685 * r ^ 5 * s ^ 3 - 120 * r ^ 5 * s ^ 2 +
  15 * r ^ 5 * s - r ^ 5 + r ^ 4 * s ^ 15 - 12 * r ^ 4 * s ^ 14 +
  48 * r ^ 4 * s ^ 13 - 49 * r ^ 4 * s ^ 12 - 165 * r ^ 4 * s ^ 11 +
  609 * r ^ 4 * s ^ 10 - 433 * r ^ 4 * s ^ 9 - 1623 * r ^ 4 * s ^ 8 +
  4299 * r ^ 4 * s ^ 7 - 4615 * r ^ 4 * s ^ 6 + 3435 * r ^ 4 * s ^ 5 -
  1740 * r ^ 4 * s ^ 4 + 455 * r ^ 4 * s ^ 3 + r ^ 3 * s ^ 15 -
  9 * r ^ 3 * s ^ 14 + 25 * r ^ 3 * s ^ 13 - 35 * r ^ 3 * s ^ 12 +
  45 * r ^ 3 * s ^ 11 - 181 * r ^ 3 * s ^ 10 + 569 * r ^ 3 * s ^ 9 -
  705 * r ^ 3 * s ^ 8 + 5 * r ^ 3 * s ^ 7 + 470 * r ^ 3 * s ^ 6 -
  540 * r ^ 3 * s ^ 5 + 340 * r ^ 3 * s ^ 4 - 105 * r ^ 3 * s ^ 3 +
  r ^ 2 * s ^ 15 - 6 * r ^ 2 * s ^ 14 + 21 * r ^ 2 * s ^ 13 -
  56 * r ^ 2 * s ^ 12 + 126 * r ^ 2 * s ^ 11 - 231 * r ^ 2 * s ^ 10 +
  266 * r ^ 2 * s ^ 9 - 126 * r ^ 2 * s ^ 8 + 96 * r ^ 2 * s ^ 7 -
  91 * r ^ 2 * s ^ 6 + 75 * r ^ 2 * s ^ 5 - 45 * r ^ 2 * s ^ 4 +
  15 * r ^ 2 * s ^ 3 + 6 * r * s ^ 10 - 28 * r * s ^ 9 +
  21 * r * s ^ 8 - 15 * r * s ^ 7 + 10 * r * s ^ 6 - 6 * r * s ^ 5 +
  3 * r * s ^ 4 - r * s ^ 3 + s ^ 10

set_option maxHeartbeats 1000000 in
/-- Exact pullback of Sutherland's raw equation to the Tate chart.  The factors
`c¹⁰(b-c)¹⁵` account for clearing `r=b/c` and `s=c²/(b-c)`; no further
polynomial cofactor is present. -/
theorem tateF25_eq_raw_pullback (b c : ℚ) (hc : c ≠ 0) (hd : b - c ≠ 0) :
    F25 b c = c ^ 10 * (b - c) ^ 15 * sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) := by
  simp only [sutherlandRawX1Plane25, F25]
  field_simp
  ring

/-- The boundary specialization `s=1` of the raw model is the single cusp
factor `(r-1)¹⁰`. -/
theorem sutherlandRawX1Plane25_at_s_one (r : ℚ) : sutherlandRawX1Plane25 r 1 = (r - 1) ^ 10 := by
  simp [sutherlandRawX1Plane25]
  ring

set_option maxHeartbeats 1000000 in
/-- On the divisor `r*s-2*r+1=0`, parametrized by `r=1/(2-s)`, the raw
equation reduces to `(s-1)²³` after clearing the tenth power denominator. -/
theorem sutherlandRawX1Plane25_at_common_zero (s : ℚ) (hs : 2 - s ≠ 0) :
    (2 - s) ^ 10 * sutherlandRawX1Plane25 (1 / (2 - s)) s = (s - 1) ^ 23 := by
  simp only [sutherlandRawX1Plane25]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- On the divisor `s²-s-r+1=0`, parametrized by `r=s²-s+1`, the raw
equation reduces to `-s(s-1)²⁷`. -/
theorem sutherlandRawX1Plane25_at_yDen_zero (s : ℚ) :
    sutherlandRawX1Plane25 (s ^ 2 - s + 1) s = -(s * (s - 1) ^ 27) := by
  simp only [sutherlandRawX1Plane25]
  ring

/-- The first denominator of the raw-to-optimized map cannot vanish at a raw
point away from `r=1`.  The preceding specialization forces `s=1`, after
which the denominator equation itself forces `r=1`. -/
theorem sutherlandCommon_ne_zero_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) :
    r * s - 2 * r + 1 ≠ 0 := by
  intro hA
  have hs2 : 2 - s ≠ 0 := by
    intro hs2
    have hs : s = 2 := by linarith
    rw [hs] at hA
    linarith
  have hr : r = 1 / (2 - s) := by
    field_simp
    linarith
  have hid := sutherlandRawX1Plane25_at_common_zero s hs2
  rw [← hr, hraw, mul_zero] at hid
  have hs1 : s = 1 :=
    sub_eq_zero.mp
      ((pow_eq_zero_iff (by norm_num : (23 : ℕ) ≠ 0)).mp hid.symm)
  rw [hs1] at hA
  exact hr1 (by linarith)

/-- A raw point with `r≠1` cannot lie on `s=1`, because the raw equation then
equals `(r-1)¹⁰`. -/
theorem sutherlandS_ne_one_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) : s ≠ 1 := by
  intro hs
  subst s
  rw [sutherlandRawX1Plane25_at_s_one] at hraw
  exact hr1 (sub_eq_zero.mp
    ((pow_eq_zero_iff (by norm_num : (10 : ℕ) ≠ 0)).mp hraw))

/-- The second denominator `s²-s-r+1` is nonzero at a raw point with
`s≠0,1`.  Its vanishing specialization is exactly `-s(s-1)²⁷`. -/
theorem sutherlandYDen_ne_zero_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : s ^ 2 - s - r + 1 ≠ 0 := by
  intro hB
  have hr : r = s ^ 2 - s + 1 := by linarith
  have hid := sutherlandRawX1Plane25_at_yDen_zero s
  rw [← hr, hraw] at hid
  have hz : s * (s - 1) ^ 27 = 0 := by linarith
  rcases mul_eq_zero.mp hz with hs | hs
  · exact hs0 hs
  · exact hs1 (sub_eq_zero.mp
      ((pow_eq_zero_iff (by norm_num : (27 : ℕ) ≠ 0)).mp hs))

/-- A primitive Tate zero maps to a zero of Sutherland's raw equation whenever
the two Tate-chart denominators `c` and `b-c` are nonzero. -/
theorem sutherlandRawX1Plane25_zero_of_tate {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) = 0 := by
  have hpull := tateF25_eq_raw_pullback b c hc hd
  rw [hF] at hpull
  have hp : c ^ 10 * (b - c) ^ 15 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 10 hc) (pow_ne_zero 15 hd)
  exact (mul_eq_zero.mp hpull.symm).resolve_left hp

/-- The raw coordinate `r=b/c` is not `1` when `c≠0` and the proper-order-five
factor `b-c` is nonzero. -/
theorem tateR_ne_one {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0) : b / c ≠ 1 := by
  intro h
  apply hd
  field_simp at h
  linarith

/-- The simplified common factor `K` is nonzero on the primitive Tate locus.
After removing the nonzero scalar `c(b-c)`, this is the raw-model denominator
`r*s-2*r+1`, whose vanishing was excluded above. -/
theorem tateToSutherlandCommon_ne_zero {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandCommon25 b c ≠ 0 := by
  have hraw := sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hA := sutherlandCommon_ne_zero_on_raw hraw (tateR_ne_one hc hd)
  intro hK
  apply hA
  have hnum :
      c * (b - c) * ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) = tateToSutherlandCommon25 b c := by
    field_simp
    simp [tateToSutherlandCommon25]
    ring
  rw [hK] at hnum
  exact (mul_eq_zero.mp hnum).resolve_left (mul_ne_zero hc hd)

/-- The simplified denominator `B` of the optimized `y` coordinate is nonzero
on the primitive Tate locus.  Removing `c(b-c)²` reduces the claim to the
raw-model denominator `s²-s-r+1`. -/
theorem tateToSutherlandYDen_ne_zero {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandYDen25 b c ≠ 0 := by
  have hraw := sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hs0 : c ^ 2 / (b - c) ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 := sutherlandS_ne_one_on_raw hraw (tateR_ne_one hc hd)
  have hBraw := sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  intro hB
  apply hBraw
  have hnum :
      c * (b - c) ^ 2 *
          ((c ^ 2 / (b - c)) ^ 2 - c ^ 2 / (b - c) - b / c + 1) = tateToSutherlandYDen25 b c := by
    field_simp
    simp [tateToSutherlandYDen25]
    ring
  rw [hB] at hnum
  exact (mul_eq_zero.mp hnum).resolve_left
    (mul_ne_zero hc (pow_ne_zero 2 hd))

set_option maxHeartbeats 1000000 in
/-- The `(8,8)` bihomogenization of `sutherlandX1Plane25` evaluated at
projective pairs `[X:K]` and `[K*D:B]`.  It is polynomial even on the boundary
where either affine denominator vanishes. -/
def sutherlandBihomogenized25 (X K D B : ℚ) : ℚ :=
  X ^ 8 * K ^ 2 * D ^ 2 * B ^ 6 +
  X ^ 7 * K ^ 6 * D ^ 5 * B ^ 3 -
  4 * X ^ 7 * K ^ 5 * D ^ 4 * B ^ 4 -
  X ^ 7 * K ^ 3 * D ^ 2 * B ^ 6 -
  3 * X ^ 6 * K ^ 8 * D ^ 6 * B ^ 2 +
  11 * X ^ 6 * K ^ 7 * D ^ 5 * B ^ 3 -
  2 * X ^ 6 * K ^ 6 * D ^ 4 * B ^ 4 +
  2 * X ^ 6 * K ^ 4 * D ^ 2 * B ^ 6 -
  2 * X ^ 6 * K ^ 3 * D * B ^ 7 +
  3 * X ^ 5 * K ^ 10 * D ^ 7 * B -
  9 * X ^ 5 * K ^ 9 * D ^ 6 * B ^ 2 -
  4 * X ^ 5 * K ^ 8 * D ^ 5 * B ^ 3 +
  4 * X ^ 5 * K ^ 7 * D ^ 4 * B ^ 4 -
  2 * X ^ 5 * K ^ 6 * D ^ 3 * B ^ 5 +
  4 * X ^ 5 * K ^ 5 * D ^ 2 * B ^ 6 -
  X ^ 4 * K ^ 12 * D ^ 8 +
  X ^ 4 * K ^ 11 * D ^ 7 * B +
  9 * X ^ 4 * K ^ 10 * D ^ 6 * B ^ 2 -
  5 * X ^ 4 * K ^ 9 * D ^ 5 * B ^ 3 +
  6 * X ^ 4 * K ^ 8 * D ^ 4 * B ^ 4 -
  15 * X ^ 4 * K ^ 7 * D ^ 3 * B ^ 5 +
  7 * X ^ 4 * K ^ 6 * D ^ 2 * B ^ 6 -
  2 * X ^ 4 * K ^ 5 * D * B ^ 7 +
  X ^ 4 * K ^ 4 * B ^ 8 +
  X ^ 3 * K ^ 13 * D ^ 8 -
  4 * X ^ 3 * K ^ 12 * D ^ 7 * B +
  3 * X ^ 3 * K ^ 11 * D ^ 6 * B ^ 2 -
  14 * X ^ 3 * K ^ 10 * D ^ 5 * B ^ 3 +
  26 * X ^ 3 * K ^ 9 * D ^ 4 * B ^ 4 -
  15 * X ^ 3 * K ^ 8 * D ^ 3 * B ^ 5 +
  7 * X ^ 3 * K ^ 7 * D ^ 2 * B ^ 6 -
  5 * X ^ 3 * K ^ 6 * D * B ^ 7 +
  X ^ 3 * K ^ 5 * B ^ 8 -
  X ^ 2 * K ^ 13 * D ^ 7 * B +
  8 * X ^ 2 * K ^ 12 * D ^ 6 * B ^ 2 -
  13 * X ^ 2 * K ^ 11 * D ^ 5 * B ^ 3 +
  12 * X ^ 2 * K ^ 10 * D ^ 4 * B ^ 4 -
  18 * X ^ 2 * K ^ 9 * D ^ 3 * B ^ 5 +
  19 * X ^ 2 * K ^ 8 * D ^ 2 * B ^ 6 -
  8 * X ^ 2 * K ^ 7 * D * B ^ 7 +
  X ^ 2 * K ^ 6 * B ^ 8 -
  4 * X * K ^ 12 * D ^ 5 * B ^ 3 +
  13 * X * K ^ 11 * D ^ 4 * B ^ 4 -
  16 * X * K ^ 10 * D ^ 3 * B ^ 5 +
  10 * X * K ^ 9 * D ^ 2 * B ^ 6 -
  4 * X * K ^ 8 * D * B ^ 7 +
  X * K ^ 7 * B ^ 8 +
  K ^ 12 * D ^ 4 * B ^ 4 -
  4 * K ^ 11 * D ^ 3 * B ^ 5 +
  6 * K ^ 10 * D ^ 2 * B ^ 6 -
  4 * K ^ 9 * D * B ^ 7 +
  K ^ 8 * B ^ 8

set_option maxHeartbeats 1000000 in
/-- On the affine chart `K*B≠0`, the bihomogeneous expression equals
`K⁸B⁸ f(X/K,KD/B)`.  This records exactly which denominators were cleared. -/
theorem sutherlandBihomogenized25_eq_affine (X K D B : ℚ) (hK : K ≠ 0) (hB : B ≠ 0) :
    sutherlandBihomogenized25 X K D B = K ^ 8 * B ^ 8 * sutherlandX1Plane25 (X / K) (K * D / B) := by
  simp only [sutherlandBihomogenized25, sutherlandX1Plane25]
  field_simp

set_option maxHeartbeats 2000000 in
/-- The raw-to-optimized comparison as a polynomial identity.  With
`X=s-r`, `K=r*s-2*r+1`, and `B=s²-s-r+1`, the bihomogenized optimized equation
is `(r-s)⁴(s-1)³K²` times the raw equation. -/
theorem sutherlandRawToOptimized_bihomogeneous_identity (r s : ℚ) :
    sutherlandBihomogenized25
        (s - r) (r * s - 2 * r + 1) 1 (s ^ 2 - s - r + 1) =
      (r - s) ^ 4 * (s - 1) ^ 3 * (r * s - 2 * r + 1) ^ 2 *
        sutherlandRawX1Plane25 r s := by
  simp only [sutherlandBihomogenized25, sutherlandRawX1Plane25]
  ring

/-- Every raw point on the chart where the two universal denominators are
nonzero maps to Sutherland's optimized affine model. -/
theorem sutherlandRawToOptimized_on_plane
    {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0)
    (hK : r * s - 2 * r + 1 ≠ 0) (hB : s ^ 2 - s - r + 1 ≠ 0) :
    sutherlandX1Plane25
        ((s - r) / (r * s - 2 * r + 1))
        ((r * s - 2 * r + 1) / (s ^ 2 - s - r + 1)) = 0 := by
  have hidentity := sutherlandRawToOptimized_bihomogeneous_identity r s
  rw [sutherlandBihomogenized25_eq_affine _ _ _ _ hK hB, hraw,
    mul_zero] at hidentity
  simpa using (mul_eq_zero.mp hidentity).resolve_left
    (mul_ne_zero (pow_ne_zero 8 hK) (pow_ne_zero 8 hB))

/-- The raw formula `(s-r)/(r*s-2*r+1)` simplifies to `X/K` in Tate
coordinates. -/
theorem tateToSutherlandX_eq_raw
    {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0)
    (hK : tateToSutherlandCommon25 b c ≠ 0) :
    (c ^ 2 / (b - c) - b / c) /
        ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) =
      tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c := by
  have hK' : -2 * b ^ 2 + b * c ^ 2 + 3 * b * c - c ^ 2 ≠ 0 := by
    simpa [tateToSutherlandCommon25] using hK
  simp only [tateToSutherlandXNum25, tateToSutherlandCommon25]
  field_simp [hc, hd, hK']
  ring

/-- The raw formula `(r*s-2*r+1)/(s²-s-r+1)` simplifies to `K(b-c)/B` in
Tate coordinates. -/
theorem tateToSutherlandY_eq_raw
    {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0)
    (hB : tateToSutherlandYDen25 b c ≠ 0) :
    ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) /
        ((c ^ 2 / (b - c)) ^ 2 - c ^ 2 / (b - c) - b / c + 1) =
      tateToSutherlandCommon25 b c * (b - c) /
        tateToSutherlandYDen25 b c := by
  have hB' :
      -b ^ 3 + 3 * b ^ 2 * c - b * c ^ 3 - 3 * b * c ^ 2 +
          c ^ 5 + c ^ 4 + c ^ 3 ≠ 0 := by
    simpa [tateToSutherlandYDen25] using hB
  simp only [tateToSutherlandCommon25, tateToSutherlandYDen25]
  field_simp [hc, hd, hB']
  ring

/-- On a nonzero Tate parameter `b`, a zero of `F25` necessarily has `c≠0`:
the specialization `F25(b,0)` is `b²⁵`. -/
theorem tateC_ne_zero_of_F25 {b c : ℚ} (hb : b ≠ 0) (hF : F25 b c = 0) : c ≠ 0 := by
  intro hc
  subst c
  simp [F25] at hF
  exact hb hF

/-- Every primitive Tate solution maps to Sutherland's optimized affine
`X₁(25)` model by the explicit formulas
`x=X/K` and `y=K(b-c)/B`.  The assumptions are exactly the nonzero Tate
parameter, the proper-order-five exclusion, and the primitive equation. -/
theorem tateToSutherland_on_plane
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    sutherlandX1Plane25
        (tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c)
        (tateToSutherlandCommon25 b c * (b - c) /
          tateToSutherlandYDen25 b c) = 0 := by
  have hc := tateC_ne_zero_of_F25 hb hF
  have hd : b - c ≠ 0 := by
    simpa [TateNFDivision.F5] using h5
  let r := b / c
  let s := c ^ 2 / (b - c)
  have hraw : sutherlandRawX1Plane25 r s = 0 :=
    sutherlandRawX1Plane25_zero_of_tate hF hc hd
  have hr1 : r ≠ 1 := tateR_ne_one hc hd
  have hKraw : r * s - 2 * r + 1 ≠ 0 :=
    sutherlandCommon_ne_zero_on_raw hraw hr1
  have hs0 : s ≠ 0 := div_ne_zero (pow_ne_zero 2 hc) hd
  have hs1 : s ≠ 1 := sutherlandS_ne_one_on_raw hraw hr1
  have hBraw : s ^ 2 - s - r + 1 ≠ 0 :=
    sutherlandYDen_ne_zero_on_raw hraw hs0 hs1
  have hplane := sutherlandRawToOptimized_on_plane hraw hKraw hBraw
  have hK := tateToSutherlandCommon_ne_zero hF hc hd
  have hB := tateToSutherlandYDen_ne_zero hF hc hd
  rw [tateToSutherlandX_eq_raw hc hd hK,
    tateToSutherlandY_eq_raw hc hd hB] at hplane
  exact hplane

end MazurProof.RationalPointsN25SutherlandBridge
