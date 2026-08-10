import FLT.Assumptions.MazurProof.RationalPointsN25QuotientSmallThreeSemantic

/-!
# Geometric Jacobian certificate in characteristic three

The canonical level-25 quotient is the complete intersection of a quadric
and a cubic in projective three-space.  This file proves that their two
gradient rows have rank two at every geometric point in characteristic three.

The proof follows the linear-elimination geometry rather than enumerating a
finite field.  On the regular `x`-chart `z≠1`, the quadric solves uniquely for
`w`; differentiating the cleared elimination identity turns two Jacobian
minors into the two partial derivatives of the residual plane equation.  A
single Bézout identity shows that the residual and both partial derivatives
can vanish only on `z=1`.  That exceptional divisor has a separate quadratic
certificate.  The remaining normalized charts reduce to two elementary
factor branches and two minors that are identically one.

The final theorem is valid over every field of characteristic three, hence in
particular over an algebraic closure.  It supplies the geometric Jacobian
criterion certificate; packaging the complete intersection as a smooth
proper genus-four scheme remains a separate algebraic-geometric interface.
-/

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientWeilThreeLinear
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic

/-! ## Characteristic-three gradients and singularity predicate -/

/-- The gradient of the canonical quadric after reducing its coefficients
modulo three.  The coordinate order is `(x,y,z,w)`. -/
def canonicalQuadricGradient25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨-P.z - P.w,
    -P.y + P.z,
    -P.x + P.y + P.w,
    -P.x + P.z⟩

/-- The gradient of the canonical cubic after reducing its coefficients
modulo three, again in coordinate order `(x,y,z,w)`. -/
def canonicalCubicGradient25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨-P.x * P.w + P.y * P.z - P.y * P.w - P.z * P.w,
    P.x * P.z - P.x * P.w + P.z * P.w,
    -P.w ^ 2 - P.x * P.w + P.y * P.w - P.z * P.w + P.x * P.y,
    P.x ^ 2 - P.x * P.y - P.x * P.z + P.y * P.z + P.z ^ 2 + P.z * P.w⟩

/-- The six two-by-two minors of the quadric and cubic gradient rows.  Their
simultaneous vanishing is exactly failure of rank two for this `2 × 4`
Jacobian matrix. -/
structure CanonicalJacobianMinors25Three (K : Type*) where
  xy : K
  xz : K
  xw : K
  yz : K
  yw : K
  zw : K

/-- Evaluate the six characteristic-three Jacobian minors at homogeneous
coordinates. -/
def canonicalJacobianMinors25Three {K : Type*} [CommRing K]
    (P : Coordinates4 K) : CanonicalJacobianMinors25Three K :=
  let q := canonicalQuadricGradient25Three P
  let c := canonicalCubicGradient25Three P
  ⟨q.x * c.y - q.y * c.x,
    q.x * c.z - q.z * c.x,
    q.x * c.w - q.w * c.x,
    q.y * c.z - q.z * c.y,
    q.y * c.w - q.w * c.y,
    q.z * c.w - q.w * c.z⟩

/-- A homogeneous point is singular for the characteristic-three complete
intersection when it lies on both equations and all six Jacobian minors
vanish. -/
def IsCanonicalSingular25Three {K : Type*} [Field K]
    (P : Coordinates4 K) : Prop :=
  let M := canonicalJacobianMinors25Three P
  canonicalQuadric25Three P = 0 ∧
    canonicalCubic25Three P = 0 ∧
    M.xy = 0 ∧ M.xz = 0 ∧ M.xw = 0 ∧
    M.yz = 0 ∧ M.yw = 0 ∧ M.zw = 0

/-! ## The regular residual and its Jacobian identities -/

/-- The `y`-partial derivative of the eliminated residual in characteristic
three.  Terms with coefficient three disappear and `4=1`, `-2=1`. -/
def canonicalResidualYDerivative25Three {K : Type*} [CommRing K]
    (y z : K) : K :=
  y ^ 3 * z + z ^ 4 + y

/-- The `z`-partial derivative of the eliminated residual in characteristic
three. -/
def canonicalResidualZDerivative25Three {K : Type*} [CommRing K]
    (y z : K) : K :=
  y ^ 4 + y ^ 3 + y * z ^ 3 - z ^ 3 - z + 1

/-- Small numeral reductions reused when ring normalization exposes integer
coefficients in the differentiated elimination identities. -/
private theorem characteristicThree_small_casts
    (K : Type*) [Field K] [CharP K 3] :
    (2 : K) = -1 ∧ (4 : K) = 1 ∧ (5 : K) = 2 ∧
      (6 : K) = 0 ∧ (7 : K) = 1 ∧ (8 : K) = 2 ∧
      (9 : K) = 0 ∧ (10 : K) = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) = -1 := by linear_combination h3
  have h4 : (4 : K) = 1 := by
    calc
      (4 : K) = (3 : K) + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add]
  have h5 : (5 : K) = 2 := by
    calc
      (5 : K) = (3 : K) + 2 := by norm_num
      _ = 2 := by rw [h3, zero_add]
  have h6 : (6 : K) = 0 := by
    calc
      (6 : K) = (3 : K) + 3 := by norm_num
      _ = 0 := by rw [h3, add_zero]
  have h7 : (7 : K) = 1 := by
    calc
      (7 : K) = (3 : K) + 3 + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add, zero_add]
  have h8 : (8 : K) = 2 := by
    calc
      (8 : K) = (3 : K) + 3 + 2 := by norm_num
      _ = 2 := by rw [h3, zero_add, zero_add]
  have h9 : (9 : K) = 0 := by
    calc
      (9 : K) = (3 : K) + 3 + 3 := by norm_num
      _ = 0 := by rw [h3, zero_add, add_zero]
  have h10 : (10 : K) = 1 := by
    calc
      (10 : K) = (3 : K) + 3 + 3 + 1 := by norm_num
      _ = 1 := by rw [h3, zero_add, zero_add, zero_add]
  exact ⟨h2, h4, h5, h6, h7, h8, h9, h10⟩

/-- The residual and its two partial derivatives generate `z-1`.  Therefore
a critical point of the residual plane curve must lie on the exceptional
divisor `z=1`.  The displayed identity was discovered by Gröbner reduction;
Lean verifies the complete polynomial certificate independently. -/
theorem residual_regular_bezout25Three
    {K : Type*} [Field K] [CharP K 3] (y z : K) :
    (-y ^ 2 * z ^ 2 - y ^ 2 * z - y ^ 2 - y * z ^ 3 + y * z ^ 2 +
        y + z ^ 4 - z ^ 3 - z ^ 2 - 1) *
        canonicalResidualX25Three y z +
      (y ^ 3 * z + y ^ 3 + y ^ 2 * z ^ 2 + y ^ 2 * z - y * z ^ 3 +
        y * z ^ 2 + y * z - y + z ^ 3 - z ^ 2 - z - 1) *
        canonicalResidualYDerivative25Three y z +
      (y ^ 2 * z ^ 3 + y * z ^ 4 + y * z ^ 3 + y * z ^ 2 + y * z + y -
        z ^ 5 - z ^ 4 - z ^ 3 - z ^ 2 + z - 1) *
        canonicalResidualZDerivative25Three y z = z - 1 := by
  dsimp [canonicalResidualX25Three, canonicalResidualYDerivative25Three,
    canonicalResidualZDerivative25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  ring_nf
  simp [h3]

/-- Differentiating the cleared elimination identity in `y` and `w` shows
that the `yw` Jacobian minor controls the `y`-partial of the residual.  Terms
proportional to the quadric are retained explicitly, so the identity is
valid before restricting to the curve. -/
theorem regular_yw_minor_identity25Three
    {K : Type*} [Field K] [CharP K 3] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let M := canonicalJacobianMinors25Three P
    (z - 1) ^ 2 * M.yw =
      canonicalQuadricX25Three y z w *
        ((-y + z) * (-z ^ 2 + z) -
          (z - 1) * (2 * y * z + 2 * z ^ 2 - 2 * z + 1)) +
      (z - 1) * canonicalResidualYDerivative25Three y z := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three, canonicalQuadricX25Three,
    canonicalResidualYDerivative25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  obtain ⟨h2, h4, h5, h6, h7, h8, _, _⟩ :=
    characteristicThree_small_casts K
  ring_nf
  simp [h2, h3, h4, h5, h6, h7, h8]
  ring

/-- Differentiating in `z` and `w` gives the companion identity for the
`zw` minor.  The extra cubic term comes from differentiating `(z-1)²`. -/
theorem regular_zw_minor_identity25Three
    {K : Type*} [Field K] [CharP K 3] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let M := canonicalJacobianMinors25Three P
    (z - 1) ^ 2 * M.zw =
      canonicalQuadricX25Three y z w *
        ((y + w - 1) * (-z ^ 2 + z) -
          (z - 1) * (y ^ 2 + y * z + z * w + y + w - 1)) +
      (z - 1) * canonicalResidualZDerivative25Three y z +
      2 * (z - 1) ^ 2 * canonicalCubicX25Three y z w := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three, canonicalQuadricX25Three,
    canonicalCubicX25Three, canonicalResidualZDerivative25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  obtain ⟨h2, h4, h5, h6, h7, h8, h9, h10⟩ :=
    characteristicThree_small_casts K
  ring_nf
  simp [h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

/-! ## Exceptional divisor and boundary charts -/

/-- On the exceptional `x`-chart divisor `z=1`, the two curve equations and
the `yw` minor generate one.  This is the terminal two-variable certificate
for the only locus not covered by regular elimination. -/
theorem exceptional_xChart_jacobian_certificate25Three
    {K : Type*} [Field K] [CharP K 3] (y w : K) :
    (w ^ 2 - w) * (y ^ 2 + y - 1) +
      (-w * y + w + 1) * (y + w - w ^ 2) +
      (w ^ 2 + w * y + 1) * ((1 - y) * (1 + w)) = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  ring_nf
  simp [h3]

/-- The quadric on the normalized `y`-chart factors as the displayed affine
equation. -/
theorem yChart_quadric25Three {K : Type*} [Field K] (z w : K) :
    canonicalQuadric25Three (⟨0, 1, z, w⟩ : Coordinates4 K) =
      1 + z + z * w := by
  unfold canonicalQuadric25Three
  ring

/-- The cubic on the normalized `y`-chart is the product
`zw(1+z-w)`, giving the two boundary branches used below. -/
theorem yChart_cubic25Three {K : Type*} [Field K] (z w : K) :
    canonicalCubic25Three (⟨0, 1, z, w⟩ : Coordinates4 K) =
      z * w * (1 + z - w) := by
  unfold canonicalCubic25Three
  ring

/-- On the `y`-chart branch `w=0`, the quadric forces `z=-1`, where the
`xy` minor equals one. -/
theorem yChart_xy_minor_zero_branch25Three
    {K : Type*} [Field K] [CharP K 3] :
    (canonicalJacobianMinors25Three
      (⟨0, 1, -1, 0⟩ : Coordinates4 K)).xy = 1 := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination -h3

/-- On the second `y`-chart branch `w=1+z`, the `xw` minor is `z²-z`.
Together with the quadric relation `z²-z+1=0`, it cannot vanish. -/
theorem yChart_xw_minor_second_branch25Three
    {K : Type*} [Field K] [CharP K 3] (z : K) :
    (canonicalJacobianMinors25Three
      (⟨0, 1, z, 1 + z⟩ : Coordinates4 K)).xw = z ^ 2 - z := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  linear_combination (-2 * z ^ 2 - z ^ 3) * h3

/-- The `yw` minor is identically one on the normalized `z`-chart. -/
theorem zChart_yw_minor_eq_one25Three
    {K : Type*} [Field K] (w : K) :
    (canonicalJacobianMinors25Three
      (⟨0, 0, 1, w⟩ : Coordinates4 K)).yw = 1 := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  ring

/-- The `xz` minor is identically one at the final normalized `w`-chart
point. -/
theorem wChart_xz_minor_eq_one25Three
    {K : Type*} [Field K] :
    (canonicalJacobianMinors25Three
      (⟨0, 0, 0, 1⟩ : Coordinates4 K)).xz = 1 := by
  dsimp [canonicalJacobianMinors25Three, canonicalQuadricGradient25Three,
    canonicalCubicGradient25Three]
  ring

/-! ## Algebraic-closure-valid projective consequence -/

/-- No normalized projective point over any characteristic-three field is
singular for the canonical quadric-cubic complete intersection.  Since the
field is arbitrary, applying the theorem over an algebraic closure proves
geometric Jacobian nonsingularity rather than only absence of rational
singular points. -/
theorem normalized_projective_point_not_singular
    {K : Type*} [Field K] [CharP K 3] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25Three (normalizedCoordinatesThree P) := by
  intro hs
  cases P with
  | xChart y z w =>
      change IsCanonicalSingular25Three
        (⟨1, y, z, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      by_cases hz : z = 1
      · subst z
        have hq' : y ^ 2 + y - 1 = 0 := by
          dsimp [canonicalQuadric25Three] at hq
          linear_combination hq
        have hc' : y + w - w ^ 2 = 0 := by
          dsimp [canonicalCubic25Three] at hc
          linear_combination hc
        have hm' : (1 - y) * (1 + w) = 0 := by
          dsimp [canonicalJacobianMinors25Three,
            canonicalQuadricGradient25Three,
            canonicalCubicGradient25Three] at hyw
          linear_combination hyw
        have hcert := exceptional_xChart_jacobian_certificate25Three y w
        rw [hq', hc', hm'] at hcert
        norm_num at hcert
      · have hcurve : IsCanonicalNormalizedThree (.xChart y z w) := ⟨hq, hc⟩
        have hQC := (isCanonicalNormalizedThree_xChart_iff y z w).1 hcurve
        have hB :=
          (canonicalCubicX25Three_eq_zero_iff_residual hz hQC.1).1 hQC.2
        have hByProd :
            (z - 1) * canonicalResidualYDerivative25Three y z = 0 := by
          have hid := regular_yw_minor_identity25Three y z w
          dsimp only at hid
          rw [hQC.1, hyw] at hid
          simp only [zero_mul, mul_zero, zero_add] at hid
          exact hid.symm
        have hBzProd :
            (z - 1) * canonicalResidualZDerivative25Three y z = 0 := by
          have hid := regular_zw_minor_identity25Three y z w
          dsimp only at hid
          rw [hQC.1, hQC.2, hzw] at hid
          simp only [zero_mul, mul_zero, zero_add, add_zero] at hid
          exact hid.symm
        have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
        have hBy : canonicalResidualYDerivative25Three y z = 0 :=
          (mul_eq_zero.mp hByProd).resolve_left hD
        have hBz : canonicalResidualZDerivative25Three y z = 0 :=
          (mul_eq_zero.mp hBzProd).resolve_left hD
        have hcert := residual_regular_bezout25Three y z
        rw [hB, hBy, hBz] at hcert
        simp only [mul_zero, zero_add] at hcert
        exact hz (sub_eq_zero.mp hcert.symm)
  | yChart z w =>
      change IsCanonicalSingular25Three
        (⟨0, 1, z, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [yChart_quadric25Three] at hq
      rw [yChart_cubic25Three] at hc
      have hz : z ≠ 0 := by
        intro hz
        subst z
        norm_num at hq
      rcases mul_eq_zero.mp hc with hzw' | hfactor
      · have hw : w = 0 := (mul_eq_zero.mp hzw').resolve_left hz
        have hzval : z = -1 := by
          rw [hw] at hq
          linear_combination hq
        rw [hw, hzval] at hxy
        rw [yChart_xy_minor_zero_branch25Three] at hxy
        exact one_ne_zero hxy
      · have hwval : w = 1 + z := by linear_combination -hfactor
        rw [hwval] at hq hxw
        have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
        have hrel : z ^ 2 - z + 1 = 0 := by
          linear_combination hq - z * h3
        rw [yChart_xw_minor_second_branch25Three] at hxw
        have : (1 : K) = 0 := by linear_combination hrel - hxw
        exact one_ne_zero this
  | zChart w =>
      change IsCanonicalSingular25Three
        (⟨0, 0, 1, w⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [zChart_yw_minor_eq_one25Three] at hyw
      exact one_ne_zero hyw
  | wChart =>
      change IsCanonicalSingular25Three
        (⟨0, 0, 0, 1⟩ : Coordinates4 K) at hs
      rcases hs with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
      rw [wChart_xz_minor_eq_one25Three] at hxz
      exact one_ne_zero hxz

end MazurProof.RationalPointsN25QuotientSmoothF3
