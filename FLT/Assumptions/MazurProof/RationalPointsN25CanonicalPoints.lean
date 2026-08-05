import Mathlib

/-!
# Coordinate-boundary rational points on the level-25 canonical curve

The genus-four quotient used at level `25` has canonical model in `ℙ³`

```
-x*z - x*w + y^2 + y*z + z*w = 0,
x^2*w + x*y*z - x*y*w - x*z*w + y*z*w + z^2*w - z*w^2 = 0.
```

This file proves an unconditional boundary classification: if any one of the
four homogeneous coordinates of a rational point is zero, then the point is
projectively equal to one of the five rational cusps.  Consequently every
hypothetical noncuspidal rational point lies in the dense torus where all four
coordinates are nonzero.

The only number-theoretic input needed for the `y = 0` chart is the rational
root theorem for the monic irreducible cubic `T^3 - T - 1`.
-/

namespace MazurProof.RationalPointsN25CanonicalPoints

open Polynomial

/-- The quadratic equation of the canonical model. -/
def canonicalQuadric25 (x y z w : ℚ) : ℚ :=
  -x * z - x * w + y ^ 2 + y * z + z * w

/-- The cubic equation of the canonical model. -/
def canonicalCubic25 (x y z w : ℚ) : ℚ :=
  x ^ 2 * w + x * y * z - x * y * w - x * z * w +
    y * z * w + z ^ 2 * w - z * w ^ 2

/-- The coefficient of `y` when the canonical cubic is viewed as a linear
equation in `y`. -/
def projectionDenominator25 (x z w : ℚ) : ℚ :=
  x * z - x * w + z * w

/-- The `y`-independent term of the canonical cubic. -/
def projectionNumerator25 (x z w : ℚ) : ℚ :=
  w * (x ^ 2 - x * z + z ^ 2 - z * w)

/-- The plane sextic obtained by eliminating `y` from the canonical model. -/
def canonicalPlaneSextic25 (x z w : ℚ) : ℚ :=
  x ^ 4 * w ^ 2 - x ^ 3 * z ^ 3 - x ^ 3 * w ^ 3 -
    x ^ 2 * z ^ 2 * w ^ 2 + x ^ 2 * z * w ^ 3 -
    x * z ^ 4 * w + 2 * x * z ^ 3 * w ^ 2 -
    2 * x * z ^ 2 * w ^ 3 + z ^ 2 * w ^ 4

/-- On the open set where the cubic is genuinely linear in `y`, this is its
unique solution. -/
def recoveredY25 (x z w : ℚ) : ℚ :=
  -projectionNumerator25 x z w / projectionDenominator25 x z w

/-- The canonical cubic is linear in `y` with the displayed coefficient and
constant term. -/
theorem canonicalCubic25_eq_linear (x y z w : ℚ) :
    canonicalCubic25 x y z w =
      y * projectionDenominator25 x z w + projectionNumerator25 x z w := by
  simp only [canonicalCubic25, projectionDenominator25, projectionNumerator25]
  ring

/-- Exact elimination identity behind the plane sextic projection. -/
theorem canonical_elimination_identity25 (x y z w : ℚ) :
    canonicalPlaneSextic25 x z w =
      projectionDenominator25 x z w ^ 2 * canonicalQuadric25 x y z w +
      (projectionNumerator25 x z w -
          projectionDenominator25 x z w * y -
          z * projectionDenominator25 x z w) *
        canonicalCubic25 x y z w := by
  simp only [canonicalPlaneSextic25, projectionDenominator25,
    projectionNumerator25, canonicalQuadric25, canonicalCubic25]
  ring

/-- Every point on the canonical complete intersection projects to the plane
sextic. -/
theorem canonical_point_projects_to_plane_sextic {x y z w : ℚ}
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0) :
    canonicalPlaneSextic25 x z w = 0 := by
  rw [canonical_elimination_identity25, hQ, hC]
  ring

/-- Conversely, away from the linear-projection denominator, every rational
point on the plane sextic lifts to the canonical complete intersection. -/
theorem plane_sextic_lifts_to_canonical {x z w : ℚ}
    (hD : projectionDenominator25 x z w ≠ 0)
    (hF : canonicalPlaneSextic25 x z w = 0) :
    canonicalQuadric25 x (recoveredY25 x z w) z w = 0 ∧
      canonicalCubic25 x (recoveredY25 x z w) z w = 0 := by
  have hC : canonicalCubic25 x (recoveredY25 x z w) z w = 0 := by
    rw [canonicalCubic25_eq_linear]
    unfold recoveredY25
    field_simp [hD]
    ring
  refine ⟨?_, hC⟩
  have hid := canonical_elimination_identity25 x (recoveredY25 x z w) z w
  rw [hF, hC, mul_zero, add_zero] at hid
  exact (mul_eq_zero.mp hid.symm).resolve_left (pow_ne_zero 2 hD)

/-- The eliminated coordinate is uniquely recovered from any canonical point
on the nonexceptional projection locus. -/
theorem recoveredY25_eq_of_canonical {x y z w : ℚ}
    (hD : projectionDenominator25 x z w ≠ 0)
    (hC : canonicalCubic25 x y z w = 0) :
    y = recoveredY25 x z w := by
  rw [canonicalCubic25_eq_linear] at hC
  unfold recoveredY25
  field_simp [hD]
  linarith

/-- A homogeneous quadruple is nonzero. -/
def NonzeroQuadruple (x y z w : ℚ) : Prop :=
  x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0

/-- Equality of two rational homogeneous quadruples in projective space. -/
def ProjectivelyEqual4
    (x y z w X Y Z W : ℚ) : Prop :=
  ∃ a : ℚ, a ≠ 0 ∧
    x = a * X ∧ y = a * Y ∧ z = a * Z ∧ w = a * W

/-- The five rational cusp classes on the level-25 canonical model. -/
def IsCanonicalCusp25 (x y z w : ℚ) : Prop :=
  ProjectivelyEqual4 x y z w 0 0 0 1 ∨
  ProjectivelyEqual4 x y z w 0 (-1) 1 0 ∨
  ProjectivelyEqual4 x y z w 1 1 0 1 ∨
  ProjectivelyEqual4 x y z w 0 0 1 0 ∨
  ProjectivelyEqual4 x y z w 1 0 0 0

/-! ## Elementary projective-coordinate helpers -/

private theorem cusp0001_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hy : y = 0) (hz : z = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst z
  have hw : w ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inl ⟨w, hw, by norm_num, by norm_num, by norm_num, by ring⟩

private theorem cusp0m110_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hyz : y = -z) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst w
  have hz : z ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inl ⟨z, hz, by norm_num, by ring, by ring, by norm_num⟩

private theorem cusp1101_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hy : y = x) (hz : z = 0) (hw : w = x) :
    IsCanonicalCusp25 x y z w := by
  subst y
  subst z
  subst w
  have hx : x ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inl
    ⟨x, hx, by ring, by ring, by norm_num, by ring⟩

private theorem cusp0010_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hx : x = 0) (hy : y = 0) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  subst y
  subst w
  have hz : z ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨z, hz, by norm_num, by norm_num, by ring, by norm_num⟩

private theorem cusp1000_of_coordinates {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hy : y = 0) (hz : z = 0) (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst y
  subst z
  subst w
  have hx : x ≠ 0 := by simpa [NonzeroQuadruple] using hnz
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr
    ⟨x, hx, by ring, by norm_num, by norm_num, by norm_num⟩

/-! ## The cubic obstruction in the `y = 0` chart -/

/-- The monic cubic `T^3 - T - 1` has no rational root. -/
theorem plastic_cubic_ne_zero (t : ℚ) : t ^ 3 - t - 1 ≠ 0 := by
  intro ht
  let p : ℤ[X] := X ^ 3 - X - 1
  have hp : p.Monic := by
    dsimp [p]
    monicity
    all_goals norm_num
  have heval : Polynomial.aeval t p = 0 := by
    norm_num [p, Polynomial.aeval_def]
    exact ht
  obtain ⟨n, hn, hndvd⟩ :=
    exists_integer_of_is_root_of_monic hp heval
  have hunit : IsUnit n := by
    apply isUnit_of_dvd_one
    have hneg : n ∣ (-1 : ℤ) := by simpa [p] using hndvd
    simpa using hneg.neg_right
  rcases Int.isUnit_iff.mp hunit with hnone | hnneg
  · have htone : t = 1 := by simpa [hnone] using hn
    rw [htone] at ht
    norm_num at ht
  · have htneg : t = -1 := by simpa [hnneg] using hn
    rw [htneg] at ht
    norm_num at ht

/-- A second monic cubic occurring in the exceptional projection locus has no
rational root. -/
theorem projection_cubic_ne_zero (t : ℚ) :
    t ^ 3 - 2 * t ^ 2 + 3 * t - 1 ≠ 0 := by
  intro ht
  let p : ℤ[X] := X ^ 3 - 2 * X ^ 2 + 3 * X - 1
  have hp : p.Monic := by
    dsimp [p]
    monicity
    all_goals norm_num
  have heval : Polynomial.aeval t p = 0 := by
    norm_num [p, Polynomial.aeval_def]
    exact ht
  obtain ⟨n, hn, hndvd⟩ :=
    exists_integer_of_is_root_of_monic hp heval
  have hunit : IsUnit n := by
    apply isUnit_of_dvd_one
    have hneg : n ∣ (-1 : ℤ) := by simpa [p] using hndvd
    simpa using hneg.neg_right
  rcases Int.isUnit_iff.mp hunit with hnone | hnneg
  · have htone : t = 1 := by simpa [hnone] using hn
    rw [htone] at ht
    norm_num at ht
  · have htneg : t = -1 := by simpa [hnneg] using hn
    rw [htneg] at ht
    norm_num at ht

/-! ## Classification on the four coordinate hyperplanes -/

/-- Every rational canonical point on the hyperplane `w = 0` is a cusp. -/
theorem canonical_point_w_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hw : w = 0) :
    IsCanonicalCusp25 x y z w := by
  subst w
  have hxyz : x * y * z = 0 := by
    simpa [canonicalCubic25] using hC
  rcases mul_eq_zero.mp hxyz with hxy | hz
  · rcases mul_eq_zero.mp hxy with hx | hy
    · have hyfac : y * (y + z) = 0 := by
        simp only [canonicalQuadric25, hx, zero_mul, neg_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hyfac with hy | hyz
      · exact cusp0010_of_coordinates hnz hx hy rfl
      · have hyneg : y = -z := by linarith
        exact cusp0m110_of_coordinates hnz hx hyneg rfl
    · have hxz : x * z = 0 := by
        simp only [canonicalQuadric25, hy, zero_mul, add_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hxz with hx | hz
      · exact cusp0010_of_coordinates hnz hx hy rfl
      · exact cusp1000_of_coordinates hnz hy hz rfl
  · have hy : y = 0 := by
      simp only [canonicalQuadric25, hz, mul_zero, add_zero] at hQ
      nlinarith [sq_nonneg y]
    exact cusp1000_of_coordinates hnz hy hz rfl

/-- Every rational canonical point on the hyperplane `z = 0` is a cusp. -/
theorem canonical_point_z_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hz : z = 0) :
    IsCanonicalCusp25 x y z w := by
  subst z
  have hC' : x ^ 2 * w - x * y * w = 0 := by
    simpa [canonicalCubic25] using hC
  have hprod : x * w * (x - y) = 0 := by
    linear_combination hC'
  rcases mul_eq_zero.mp hprod with hxw | hxy
  · rcases mul_eq_zero.mp hxw with hx | hw
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hx, zero_mul, neg_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp0001_of_coordinates hnz hx hy rfl
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hw, mul_zero, add_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp1000_of_coordinates hnz hy rfl hw
  · have hy : y = x := by linarith
    have hxw : x * (x - w) = 0 := by
      simp only [canonicalQuadric25, hy] at hQ
      nlinarith
    rcases mul_eq_zero.mp hxw with hx | hxw
    · have hy0 : y = 0 := by rw [hy, hx]
      exact cusp0001_of_coordinates hnz hx hy0 rfl
    · have hw : w = x := by linarith
      exact cusp1101_of_coordinates hnz hy rfl hw

/-- Every rational canonical point on the hyperplane `x = 0` is a cusp. -/
theorem canonical_point_x_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hx : x = 0) :
    IsCanonicalCusp25 x y z w := by
  subst x
  have hC' : y * z * w + z ^ 2 * w - z * w ^ 2 = 0 := by
    simpa [canonicalCubic25] using hC
  have hprod : z * w * (y + z - w) = 0 := by
    linear_combination hC'
  rcases mul_eq_zero.mp hprod with hzw | hyzw
  · rcases mul_eq_zero.mp hzw with hz | hw
    · have hy : y = 0 := by
        simp only [canonicalQuadric25, hz, mul_zero, add_zero] at hQ
        nlinarith [sq_nonneg y]
      exact cusp0001_of_coordinates hnz rfl hy hz
    · have hyfac : y * (y + z) = 0 := by
        simp only [canonicalQuadric25, hw, mul_zero, add_zero] at hQ
        nlinarith
      rcases mul_eq_zero.mp hyfac with hy | hyz
      · exact cusp0010_of_coordinates hnz rfl hy hw
      · have hyneg : y = -z := by linarith
        exact cusp0m110_of_coordinates hnz rfl hyneg hw
  · have hwzero : w = 0 := by
      have hyzw' : y + z = w := by linarith
      have hQ' : y ^ 2 + y * z + z * w = 0 := by
        simpa [canonicalQuadric25] using hQ
      rw [← hyzw'] at hQ'
      have hsum : y + z = 0 := by nlinarith [sq_nonneg (y + z)]
      linarith
    have hyfac : y * (y + z) = 0 := by
      simp only [canonicalQuadric25, hwzero, mul_zero, add_zero] at hQ
      nlinarith
    rcases mul_eq_zero.mp hyfac with hy | hyz
    · exact cusp0010_of_coordinates hnz rfl hy hwzero
    · have hyneg : y = -z := by linarith
      exact cusp0m110_of_coordinates hnz rfl hyneg hwzero

/-- Every rational canonical point on the hyperplane `y = 0` is a cusp.

After the easy component `w = 0`, elimination of `x` from the two equations
gives

`z * (z^3 - w^2*z - w^3) = 0`.

The second factor would make `z/w` a rational root of `T^3 - T - 1`. -/
theorem canonical_point_y_zero_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hy : y = 0) :
    IsCanonicalCusp25 x y z w := by
  subst y
  by_cases hw : w = 0
  · exact canonical_point_w_zero_is_cusp hnz hQ hC hw
  have hQ' : -x * z - x * w + z * w = 0 := by
    simpa [canonicalQuadric25] using hQ
  have hC' : x ^ 2 * w - x * z * w + z ^ 2 * w - z * w ^ 2 = 0 := by
    simpa [canonicalCubic25] using hC
  have hinner : x ^ 2 - x * z + z ^ 2 - z * w = 0 := by
    have hfactor : w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
      linear_combination hC'
    exact (mul_eq_zero.mp hfactor).resolve_left hw
  have hres : z * (z ^ 3 - w ^ 2 * z - w ^ 3) = 0 := by
    linear_combination
      ((w + z) * x - z ^ 2) * hQ' + (w + z) ^ 2 * hinner
  rcases mul_eq_zero.mp hres with hz | hhom
  · have hx : x = 0 := by
      rw [hz] at hQ'
      norm_num at hQ'
      exact hQ'.resolve_right hw
    exact cusp0001_of_coordinates hnz hx rfl hz
  · have hroot : (z / w) ^ 3 - z / w - 1 = 0 := by
      field_simp [hw]
      nlinarith
    exact False.elim ((plastic_cubic_ne_zero (z / w)) hroot)

/-- A rational point on the canonical model with a zero homogeneous
coordinate is one of the five rational cusps. -/
theorem canonical_point_with_zero_coordinate_is_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hzero : x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0) :
    IsCanonicalCusp25 x y z w := by
  rcases hzero with hx | hy | hz | hw
  · exact canonical_point_x_zero_is_cusp hnz hQ hC hx
  · exact canonical_point_y_zero_is_cusp hnz hQ hC hy
  · exact canonical_point_z_zero_is_cusp hnz hQ hC hz
  · exact canonical_point_w_zero_is_cusp hnz hQ hC hw

/-- Contrapositive form used by later affine/descent reductions: every
noncuspidal rational point has all four coordinates nonzero. -/
theorem all_coordinates_ne_zero_of_not_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w ≠ 0 := by
  constructor
  · intro hx
    exact hncusp (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inl hx))
  constructor
  · intro hy
    exact hncusp (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inl hy)))
  constructor
  · intro hz
    exact hncusp
      (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inr (Or.inl hz))))
  · intro hw
    exact hncusp
      (canonical_point_with_zero_coordinate_is_cusp hnz hQ hC (Or.inr (Or.inr (Or.inr hw))))

/-- The plane-sextic projection denominator cannot vanish at a noncuspidal
rational point.  Indeed, simultaneous vanishing of the denominator and the
canonical cubic eliminates `x` to

`z * (z^3 - 2*w*z^2 + 3*w^2*z - w^3) = 0`.

On the dense torus the first factor is nonzero, while the second factor would
give a rational root of `T^3 - 2*T^2 + 3*T - 1`. -/
theorem projectionDenominator25_ne_zero_of_not_cusp {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    projectionDenominator25 x z w ≠ 0 := by
  obtain ⟨_hx, _hy, hz, hw⟩ :=
    all_coordinates_ne_zero_of_not_cusp hnz hQ hC hncusp
  intro hD
  have hD' : x * z - x * w + z * w = 0 := by
    simpa [projectionDenominator25] using hD
  have hdecomp :
      y * projectionDenominator25 x z w +
        w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
    change y * projectionDenominator25 x z w +
      projectionNumerator25 x z w = 0
    rw [← canonicalCubic25_eq_linear]
    exact hC
  have hwi : w * (x ^ 2 - x * z + z ^ 2 - z * w) = 0 := by
    simpa only [hD, mul_zero, zero_add] using hdecomp
  have hinner : x ^ 2 - x * z + z ^ 2 - z * w = 0 :=
    (mul_eq_zero.mp hwi).resolve_left hw
  have hres :
      z * (z ^ 3 - 2 * w * z ^ 2 + 3 * w ^ 2 * z - w ^ 3) = 0 := by
    linear_combination
      ((w - z) * x + z ^ 2) * hD' + (w - z) ^ 2 * hinner
  have hhom : z ^ 3 - 2 * w * z ^ 2 + 3 * w ^ 2 * z - w ^ 3 = 0 :=
    (mul_eq_zero.mp hres).resolve_left hz
  have hroot :
      (z / w) ^ 3 - 2 * (z / w) ^ 2 + 3 * (z / w) - 1 = 0 := by
    field_simp [hw]
    nlinarith
  exact (projection_cubic_ne_zero (z / w)) hroot

/-- Dense-open birational reduction: every hypothetical noncuspidal canonical
point projects to the plane sextic on its nonexceptional locus, and its fourth
coordinate `y` is recovered by the explicit rational formula. -/
theorem noncuspidal_point_to_plane_sextic {x y z w : ℚ}
    (hnz : NonzeroQuadruple x y z w)
    (hQ : canonicalQuadric25 x y z w = 0)
    (hC : canonicalCubic25 x y z w = 0)
    (hncusp : ¬ IsCanonicalCusp25 x y z w) :
    canonicalPlaneSextic25 x z w = 0 ∧
      projectionDenominator25 x z w ≠ 0 ∧
      y = recoveredY25 x z w := by
  have hD := projectionDenominator25_ne_zero_of_not_cusp hnz hQ hC hncusp
  exact ⟨canonical_point_projects_to_plane_sextic hQ hC, hD,
    recoveredY25_eq_of_canonical hD hC⟩

end MazurProof.RationalPointsN25CanonicalPoints
