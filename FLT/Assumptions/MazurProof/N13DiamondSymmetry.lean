import FLT.Assumptions.MazurProof.N13CurveModel

/-!
# The rational diamond symmetry of the `X₁(13)` sextic

The order-six diamond action is already visible on the sextic chart.  Its
order-three subgroup has a genus-zero quotient, with the displayed invariant
as a rational parameter.  These identities are small rational-function
calculations, not an elimination certificate.
-/

namespace MazurProof.N13DiamondSymmetry

open N13CurveModel

def diamondX (x : ℚ) : ℚ := -1 / (x + 1)

def diamondY (x y : ℚ) : ℚ := y / (x + 1) ^ 3

def orderThreeY (x y : ℚ) : ℚ := -y / (x + 1) ^ 3

def quotientParameter (x : ℚ) : ℚ :=
  (x ^ 3 - 3 * x - 1) / (x * (x + 1))

theorem sextic_diamond_identity (x : ℚ) (hx : x + 1 ≠ 0) :
    sexticF13 (diamondX x) = sexticF13 x / (x + 1) ^ 6 := by
  unfold diamondX sexticF13
  field_simp [hx]
  ring

theorem diamond_mem {x y : ℚ} (hx : x + 1 ≠ 0)
    (h : C13SexticEq x y) :
    C13SexticEq (diamondX x) (diamondY x y) := by
  rw [C13SexticEq, diamondY, sextic_diamond_identity x hx]
  field_simp [hx]
  simpa only [C13SexticEq] using h

theorem orderThree_mem {x y : ℚ} (hx : x + 1 ≠ 0)
    (h : C13SexticEq x y) :
    C13SexticEq (diamondX x) (orderThreeY x y) := by
  rw [C13SexticEq, orderThreeY, sextic_diamond_identity x hx]
  field_simp [hx]
  simpa only [C13SexticEq] using h

theorem diamondX_sq (x : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    diamondX (diamondX x) = -(x + 1) / x := by
  unfold diamondX
  rw [show -1 / (x + 1) + 1 = x / (x + 1) by
    field_simp [hx, hx1]
    ring]
  field_simp [hx, hx1]

theorem diamondX_cube (x : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    diamondX (diamondX (diamondX x)) = x := by
  rw [diamondX_sq x hx hx1]
  unfold diamondX
  field_simp [hx, hx1]
  ring

theorem diamondY_cube (x y : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    diamondY (diamondX (diamondX x))
      (diamondY (diamondX x) (diamondY x y)) = -y := by
  rw [diamondX_sq x hx hx1]
  unfold diamondY diamondX
  field_simp [hx, hx1]
  ring

theorem orderThreeY_cube (x y : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    orderThreeY (diamondX (diamondX x))
      (orderThreeY (diamondX x) (orderThreeY x y)) = y := by
  rw [diamondX_sq x hx hx1]
  unfold orderThreeY diamondX
  field_simp [hx, hx1]
  ring

theorem quotientParameter_invariant (x : ℚ) (hx : x ≠ 0)
    (hx1 : x + 1 ≠ 0) :
    quotientParameter (diamondX x) = quotientParameter x := by
  unfold quotientParameter diamondX
  field_simp [hx, hx1]
  ring

end MazurProof.N13DiamondSymmetry
