import FLT.Assumptions.MazurProof.CyclicExclusion49Polynomial
import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# Rational infrastructure for the order-49 Vélu map

This file records the square-root-free part of the degree-seven quotient used
in the order-49 argument.  The three kernel coordinates are kept in the compact
straight-line-program form supplied by the origin evaluations of `preΨ'`.
-/

namespace MazurProof.N49VeluMap

open TateNFDivision
open TateOrder25Factor
open CyclicExclusion49Polynomial

noncomputable section

/-! ## Kernel coordinates and symmetric functions -/

/-- The SLP expression for `x([7]P)`. -/
def x1 (b c : ℚ) : ℚ :=
  b * c * F6 b c * F8 b c / F7 b c ^ 2

/-- The SLP expression for `y([7]P)`.
Sage: `y7_num = b² · F6² · (-F9)`, `y7_den = F7³`. -/
def y1 (b c : ℚ) : ℚ :=
  -(b ^ 2 * F6 b c ^ 2 * F9 b c) / F7 b c ^ 3

/-- The SLP expression for `x([14]P)`. -/
def x2 (b c : ℚ) : ℚ :=
  b * G13 b c * F15 b c / G14 b c ^ 2

/-- The SLP expression for `x([21]P)`. -/
def x3 (b c : ℚ) : ℚ :=
  -(G20 b c * G22 b c) / G21 b c ^ 2

/-- First elementary symmetric function of the nonzero kernel coordinates. -/
def e1 (b c : ℚ) : ℚ :=
  x1 b c + x2 b c + x3 b c

/-- Second elementary symmetric function of the nonzero kernel coordinates. -/
def e2 (b c : ℚ) : ℚ :=
  x1 b c * x2 b c + x1 b c * x3 b c + x2 b c * x3 b c

/-- Third elementary symmetric function of the nonzero kernel coordinates. -/
def e3 (b c : ℚ) : ℚ :=
  x1 b c * x2 b c * x3 b c

/-! ## Tate invariants and the quotient abscissa -/

/-- The Tate-normal-form invariant `b₂`. -/
def b2 (b c : ℚ) : ℚ :=
  (1 - c) ^ 2 - 4 * b

/-- The Tate-normal-form invariant `b₄`. -/
def b4 (b c : ℚ) : ℚ :=
  b * (c - 1)

/-- The Tate-normal-form invariant `b₆`. -/
def b6 (b _c : ℚ) : ℚ :=
  b ^ 2

/-- Kohel's numerator at the Tate origin for the kernel polynomial
`(X-x1)(X-x2)(X-x3)`. -/
def phi0 (b c : ℚ) : ℚ :=
  b6 b c * (e2 b c ^ 2 + 2 * e1 b c * e3 b c) -
    b4 b c * e2 b c * e3 b c + 2 * e1 b c * e3 b c ^ 2

/-- The abscissa of the image of `P=(0,0)` under the Vélu quotient. -/
def xR (b c : ℚ) : ℚ :=
  phi0 b c / e3 b c ^ 2

/-! The following two expressions substitute the compact `preΨ'` kernel
coordinates directly, before naming their elementary symmetric functions. -/

/-- Kohel's origin numerator written directly in the three `preΨ'` kernel
coordinates. -/
def phi0PrePsi (b c : ℚ) : ℚ :=
  let q1 := b * c * F6 b c * F8 b c / F7 b c ^ 2
  let q2 := b * G13 b c * F15 b c / G14 b c ^ 2
  let q3 := -(G20 b c * G22 b c) / G21 b c ^ 2
  b6 b c * ((q1 * q2 + q1 * q3 + q2 * q3) ^ 2 +
      2 * (q1 + q2 + q3) * (q1 * q2 * q3)) -
    b4 b c * (q1 * q2 + q1 * q3 + q2 * q3) * (q1 * q2 * q3) +
    2 * (q1 + q2 + q3) * (q1 * q2 * q3) ^ 2

/-- The squared Kohel denominator written directly in the three `preΨ'`
kernel coordinates. -/
def e3SqPrePsi (b c : ℚ) : ℚ :=
  ((b * c * F6 b c * F8 b c / F7 b c ^ 2) *
      (b * G13 b c * F15 b c / G14 b c ^ 2) *
      (-(G20 b c * G22 b c) / G21 b c ^ 2)) ^ 2

/-- The symmetric-function and direct `preΨ'` forms of Kohel's numerator
agree. -/
theorem phi0_eq_phi0PrePsi (b c : ℚ) :
    phi0 b c = phi0PrePsi b c := by
  unfold phi0 phi0PrePsi e1 e2 e3 x1 x2 x3
  ring

/-- The squared constant term of the kernel polynomial agrees with the direct
`preΨ'` product. -/
theorem e3_sq_eq_e3SqPrePsi (b c : ℚ) :
    e3 b c ^ 2 = e3SqPrePsi b c := by
  unfold e3 e3SqPrePsi x1 x2 x3
  ring

/-! ## Coefficients of the image curve -/

/-- Vélu's kernel sum `v`. -/
def v (b c : ℚ) : ℚ :=
  6 * (e1 b c ^ 2 - 2 * e2 b c) + b2 b c * e1 b c + 3 * b4 b c

/-- Vélu's kernel sum `w`. -/
def w (b c : ℚ) : ℚ :=
  10 * (e1 b c ^ 3 - 3 * e1 b c * e2 b c + 3 * e3 b c) +
    2 * b2 b c * (e1 b c ^ 2 - 2 * e2 b c) +
    3 * b4 b c * e1 b c + 3 * b6 b c

/-- The `a₄` coefficient of the quotient curve. -/
def a4' (b c : ℚ) : ℚ :=
  -5 * v b c

/-- The `a₆` coefficient of the quotient curve. -/
def a6' (b c : ℚ) : ℚ :=
  -b2 b c * v b c - 7 * w b c

/-- The completed-square cubic of the quotient curve, evaluated at `xR`.
It is the square of `2*yR + (1-c)*xR - b` once the ordinate is introduced. -/
def HxR (b c : ℚ) : ℚ :=
  4 * xR b c ^ 3 + b2 b c * xR b c ^ 2 +
    2 * (b4 b c + 2 * a4' b c) * xR b c + b6 b c + 4 * a6' b c

/-! ## T₇ invariant V = T₇(d([7]P))

The d-invariant of [7]P on the Tate curve uses `x1`, `y1` and the curve
coefficients `a₁ = 1-c, a₂ = -b, a₃ = -b, a₄ = 0`.  Since `y1` factors
through `F6²·F9`, the intermediate expressions stay in the SLP ring. -/

/-- λ = (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃), numerator. -/
def lam_num (b c : ℚ) : ℚ :=
  3 * x1 b c ^ 2 + 2 * (-b) * x1 b c - (1 - c) * y1 b c

/-- λ denominator: 2y₁ + a₁x₁ + a₃ = 2y₁ + (1-c)x₁ - b. -/
def lam_den (b c : ℚ) : ℚ :=
  2 * y1 b c + (1 - c) * x1 b c - b

/-- A₂' = a₂ - λa₁ - λ² + 3x₁, times lam_den². -/
def A2_num (b c : ℚ) : ℚ :=
  (-b) * lam_den b c ^ 2 - lam_num b c * (1 - c) * lam_den b c -
    lam_num b c ^ 2 + 3 * x1 b c * lam_den b c ^ 2

/-- A₃' = a₃ + a₁x₁ + 2y₁ = lam_den. -/
def A3_val (b c : ℚ) : ℚ :=
  lam_den b c

/-- A₁' = a₁ + 2λ, times lam_den. -/
def A1_num (b c : ℚ) : ℚ :=
  (1 - c) * lam_den b c + 2 * lam_num b c

/-- d([7]P) = -A₂³/(A₃(A₃ - A₁A₂)), all multiplied by lam_den⁶ to clear.
Numerator of d: -A2_num³. Denominator: A3_val·lam_den²·(A3_val·lam_den² - A1_num·A2_num). -/
def d7_num (b c : ℚ) : ℚ :=
  -(A2_num b c) ^ 3

def d7_den (b c : ℚ) : ℚ :=
  A3_val b c * lam_den b c ^ 2 *
    (A3_val b c * lam_den b c ^ 2 - A1_num b c * A2_num b c)

/-- V = T₇(d) = (d³-8d²+5d+1)/(d(d-1)), numerator times d7_den³. -/
def V_num (b c : ℚ) : ℚ :=
  d7_num b c ^ 3 - 8 * d7_num b c ^ 2 * d7_den b c +
    5 * d7_num b c * d7_den b c ^ 2 + d7_den b c ^ 3

def V_den (b c : ℚ) : ℚ :=
  d7_num b c * (d7_num b c - d7_den b c)

end

end MazurProof.N49VeluMap
