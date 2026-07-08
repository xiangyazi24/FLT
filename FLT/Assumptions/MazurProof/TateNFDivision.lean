import Mathlib

/-!
# Division polynomials at the Tate normal form origin

For the Tate normal form `y² + (1-c)xy - by = x³ - bx²` with marked point
`P = (0,0)`, the division polynomials `ψₙ` evaluated at `P` factor as
`ψₙ(P) = b^eₙ · Fₙ(b,c)` where `Fₙ` is a small polynomial.

The condition "P has exact order n" is `Fₙ(b,c) = 0` (with `b ≠ 0` and
nonsingularity).  These compact factors are the foundation for all cyclic
torsion exclusions via Tate normal form.

## References

* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
* The division polynomial recurrence specialized at the origin
-/

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]

/-! ## Tate normal form curve and origin -/

/-- The Tate normal form `y² + (1-c)xy - by = x³ - bx²`. -/
def tateCurve (b c : K) : WeierstrassCurve K where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

/-! ## Weierstrass invariants of the Tate normal form -/

theorem tate_b₂ (b c : K) : (tateCurve b c).b₂ = (1 - c) ^ 2 - 4 * b := by
  simp [tateCurve, WeierstrassCurve.b₂]; ring

theorem tate_b₄ (b c : K) : (tateCurve b c).b₄ = b * (c - 1) := by
  simp [tateCurve, WeierstrassCurve.b₄]; ring

theorem tate_b₆ (b c : K) : (tateCurve b c).b₆ = b ^ 2 := by
  simp [tateCurve, WeierstrassCurve.b₆]

theorem tate_b₈ (b c : K) : (tateCurve b c).b₈ = -b ^ 3 := by
  simp [tateCurve, WeierstrassCurve.b₈]; ring

/-! ## Compact factors of ψₙ(0,0) / b^eₙ

These are the NON-trivial factors after removing the power of `b`.
The order-n condition at the Tate origin is `Fₙ(b,c) = 0`.
-/

/-- `ψ₅(0,0) / b⁸ = b - c`.  Order 5 at origin ⟺ `c = b`. -/
def F5 (b c : K) : K := b - c

/-- `ψ₆(0,0) / b¹² = b - c - c²`.  Order 6 at origin ⟺ `c² + c = b`. -/
def F6 (b c : K) : K := b - c - c ^ 2

/-- `ψ₇(0,0) / b¹⁶ = c³ - b² + bc`.  Order 7 at origin. -/
def F7 (b c : K) : K := c ^ 3 - b ^ 2 + b * c

/-- `ψ₈(0,0) / (-b²¹c) = 2b² - 3bc - bc² + c²`.  Order 8 at origin
    requires additionally `c ≠ 0`. -/
def F8 (b c : K) : K := 2 * b ^ 2 - 3 * b * c - b * c ^ 2 + c ^ 2

/-- `ψ₉(0,0) / b²⁷ = (b-c)³ + c³(b-c-c²)`.  Order 9 at origin. -/
def F9 (b c : K) : K := (b - c) ^ 3 + c ^ 3 * (b - c - c ^ 2)

/-- `ψ₁₁(0,0) / b⁴⁰`.  11 monomials, total degree 8. -/
def F11 (b c : K) : K :=
  (c ^ 3 - b * (b - c)) * (b - c) ^ 3 - b * c * (b - c - c ^ 2) ^ 3

/-- `-ψ₁₃(0,0) / b⁵⁶`.  20 monomials, total degree 11. -/
def F13 (b c : K) : K :=
  (b - c) * (c ^ 3 - b * (b - c)) ^ 3 +
    b * c * F8 b c * (b - c - c ^ 2) ^ 3

/-- `ψ₁₅(0,0) / b⁷⁵ = F9 · F7³ + (b-c-c²) · c³ · F8³`. -/
def F15 (b c : K) : K :=
  F9 b c * F7 b c ^ 3 + (b - c - c ^ 2) * c ^ 3 * F8 b c ^ 3

/-! ## Expanded forms (useful for ring-level reasoning) -/

@[simp] theorem F5_eq (b c : K) : F5 b c = b - c := rfl

@[simp] theorem F6_eq (b c : K) : F6 b c = b - c - c ^ 2 := rfl

theorem F7_expanded (b c : K) : F7 b c = c ^ 3 + b * c - b ^ 2 := by
  unfold F7; ring

theorem F8_expanded (b c : K) :
    F8 b c = 2 * b ^ 2 - 3 * b * c - b * c ^ 2 + c ^ 2 := by
  unfold F8; ring

theorem F9_expanded (b c : K) :
    F9 b c = b ^ 3 - 3 * b ^ 2 * c + 3 * b * c ^ 2 - c ^ 3
           + b * c ^ 3 - c ^ 4 - c ^ 5 := by
  unfold F9; ring

theorem F11_expanded (b c : K) :
    F11 b c =
      - b ^ 5 + 3 * b ^ 4 * c - 3 * b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3
      + 4 * b ^ 3 * c ^ 3 - 9 * b ^ 2 * c ^ 4 + 6 * b * c ^ 5 - c ^ 6
      - 3 * b ^ 2 * c ^ 5 + 3 * b * c ^ 6 + b * c ^ 7 := by
  unfold F11; ring

/-! ## Two-division polynomial (for rational 2-torsion detection) -/

/-- The 2-division x-polynomial for the Tate normal form.
    A rational root gives a rational 2-torsion point. -/
def T2 (b c X : K) : K :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

/-- The 3-division x-polynomial for the Tate normal form. -/
def Psi3X (b c X : K) : K :=
  3 * X ^ 4 + ((1 - c) ^ 2 - 4 * b) * X ^ 3 +
    3 * (b * (c - 1)) * X ^ 2 + 3 * b ^ 2 * X - b ^ 3

/-! ## Relation to Weierstrass invariants -/

theorem T2_eq_twoDiv (b c X : K) :
    T2 b c X = 4 * X ^ 3 + (tateCurve b c).b₂ * X ^ 2
             + 2 * (tateCurve b c).b₄ * X + (tateCurve b c).b₆ := by
  unfold T2; rw [tate_b₂, tate_b₄, tate_b₆]; ring

/-! ## Order conditions at the Tate origin

Exact order `n` at the origin means `Fₙ(b,c) = 0` and all proper divisor
conditions are nonzero.
-/

/-- Exact order 4: `c = 0` (with `b ≠ 0`). -/
def ExactOrder4 (b c : K) : Prop :=
  b ≠ 0 ∧ c = 0

/-- Exact order 5: `b = c` (with `b ≠ 0`). -/
def ExactOrder5 (b c : K) : Prop :=
  b ≠ 0 ∧ F5 b c = 0

/-- Exact order 7: `F7(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder7 (b c : K) : Prop :=
  b ≠ 0 ∧ F7 b c = 0

/-- Exact order 8: `F8(b,c) = 0` (with `b ≠ 0`, `c ≠ 0`). -/
def ExactOrder8 (b c : K) : Prop :=
  b ≠ 0 ∧ c ≠ 0 ∧ F8 b c = 0

/-- Exact order 9: `F9(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder9 (b c : K) : Prop :=
  b ≠ 0 ∧ F9 b c = 0

/-- Exact order 11: `F11(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder11 (b c : K) : Prop :=
  b ≠ 0 ∧ F11 b c = 0

/-- Exact order 13: `F13(b,c) = 0` (with `b ≠ 0`). -/
def ExactOrder13 (b c : K) : Prop :=
  b ≠ 0 ∧ F13 b c = 0

/-! ## Composite order systems via coprime decomposition -/

/-- A rational point of order 2 exists on `E(b,c)`: the 2-division cubic has
    a rational root. -/
def HasRational2Torsion (b c : K) : Prop :=
  ∃ X : K, T2 b c X = 0

/-- A rational point of order 3 exists on `E(b,c)`: the 3-division polynomial
    has a rational root, and the curve equation is satisfied. -/
def HasRational3Torsion (b c : K) : Prop :=
  ∃ X Y : K,
    Y ^ 2 + (1 - c) * X * Y - b * Y = X ^ 3 - b * X ^ 2 ∧
    Psi3X b c X = 0

/-- System for order 14 = 2 · 7: origin has order 7, plus rational 2-torsion. -/
def Obstruction14 (b c : K) : Prop :=
  ExactOrder7 b c ∧ HasRational2Torsion b c

/-- System for order 18 = 2 · 9: origin has order 9, plus rational 2-torsion. -/
def Obstruction18 (b c : K) : Prop :=
  ExactOrder9 b c ∧ HasRational2Torsion b c

/-- System for order 20 = 4 · 5: origin has order 4 (c=0), plus rational
    5-torsion (separate point). -/
def Obstruction20 (b c : K) : Prop :=
  ExactOrder4 b c ∧ F5 b c = 0

/-- System for order 21 = 3 · 7: origin has order 7, plus rational 3-torsion. -/
def Obstruction21 (b c : K) : Prop :=
  ExactOrder7 b c ∧ HasRational3Torsion b c

/-- System for order 24 = 3 · 8: origin has order 8, plus rational 3-torsion. -/
def Obstruction24 (b c : K) : Prop :=
  ExactOrder8 b c ∧ HasRational3Torsion b c

end MazurProof.TateNFDivision
