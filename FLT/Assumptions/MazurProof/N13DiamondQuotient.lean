import FLT.Assumptions.MazurProof.N13DiamondSymmetry

/-!
# The order-three diamond quotient of the `X₁(13)` sextic

On the affine chart away from `x=0,-1`, the invariant functions
`u = (x³-3x-1)/(x(x+1))` and `z = y/(x(x+1))` satisfy a conic equation.
The quotient is therefore rational, but its cubic fibers remain nontrivial.
-/

namespace MazurProof.N13DiamondQuotient

open N13CurveModel N13DiamondSymmetry

def quotientZ (x y : ℚ) : ℚ := y / (x * (x + 1))

theorem quotient_equation {x y : ℚ} (hx : x ≠ 0) (hx1 : x + 1 ≠ 0)
    (h : C13SexticEq x y) :
    quotientZ x y ^ 2 = quotientParameter x ^ 2 +
      4 * quotientParameter x + 8 := by
  unfold quotientZ quotientParameter
  field_simp [hx, hx1]
  simp only [C13SexticEq, sexticF13] at h
  linear_combination h

theorem quotient_fiber_cubic (x : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    x ^ 3 - quotientParameter x * x ^ 2 -
        (quotientParameter x + 3) * x - 1 = 0 := by
  unfold quotientParameter
  field_simp [hx, hx1]
  ring

theorem quotientZ_orderThree_invariant (x y : ℚ) (hx : x ≠ 0)
    (hx1 : x + 1 ≠ 0) :
    quotientZ (diamondX x) (orderThreeY x y) = quotientZ x y := by
  unfold quotientZ diamondX orderThreeY
  field_simp [hx, hx1]
  ring

def conicU (t : ℚ) : ℚ := t⁻¹ - t - 2

def conicZ (t : ℚ) : ℚ := t + t⁻¹

theorem conic_parametrization (t : ℚ) (ht : t ≠ 0) :
    conicZ t ^ 2 = conicU t ^ 2 + 4 * conicU t + 8 := by
  unfold conicU conicZ
  field_simp [ht]
  ring

def conicParameter (u z : ℚ) : ℚ := (z - u - 2) / 2

theorem conic_factor {u z : ℚ} (h : z ^ 2 = u ^ 2 + 4 * u + 8) :
    (z - u - 2) * (z + u + 2) = 4 := by
  nlinarith

theorem conicParameter_ne_zero {u z : ℚ}
    (h : z ^ 2 = u ^ 2 + 4 * u + 8) :
    conicParameter u z ≠ 0 := by
  intro hz
  have hz' : z - u - 2 = 0 := by
    unfold conicParameter at hz
    linarith
  have hfac := conic_factor h
  rw [hz'] at hfac
  norm_num at hfac

theorem conicU_conicParameter {u z : ℚ}
    (h : z ^ 2 = u ^ 2 + 4 * u + 8) :
    conicU (conicParameter u z) = u := by
  have ht := conicParameter_ne_zero h
  have hfac := conic_factor h
  have hden : z - u - 2 ≠ 0 := by
    intro hzero
    apply ht
    simp [conicParameter, hzero]
  unfold conicU conicParameter
  field_simp [hden]
  nlinarith [hfac]

theorem conicZ_conicParameter {u z : ℚ}
    (h : z ^ 2 = u ^ 2 + 4 * u + 8) :
    conicZ (conicParameter u z) = z := by
  have ht := conicParameter_ne_zero h
  have hfac := conic_factor h
  have hden : z - u - 2 ≠ 0 := by
    intro hzero
    apply ht
    simp [conicParameter, hzero]
  unfold conicZ conicParameter
  field_simp [hden]
  nlinarith [hfac]

end MazurProof.N13DiamondQuotient
