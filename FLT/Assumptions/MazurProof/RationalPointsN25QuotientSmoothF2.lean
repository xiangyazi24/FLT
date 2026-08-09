import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil

/-!
# Geometric smoothness certificate for the level-25 special fibre

The canonical quotient is a quadric-cubic complete intersection in projective
three-space.  In characteristic two, a singular point would make the two
gradient rows linearly dependent, so all six two-by-two Jacobian minors would
vanish together with the two defining equations.

This file records four exact Bézout certificates, one on each normalized
projective chart.  Each certificate expresses one as a polynomial linear
combination of the quadric, cubic, and six minors.  Because the coefficient
field is arbitrary of characteristic two, the certificates exclude singular
geometric points, not merely `F_2`-rational singular points.  The identities
were discovered with a Gröbner-basis computation and are independently
verified by Lean's `ring_nf` tactic.
-/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil

/-- The canonical quadric after reduction to characteristic two. -/
def canonicalQuadric25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x * P.z + P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

/-- The canonical cubic after reduction to characteristic two. -/
def canonicalCubic25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : K :=
  P.x ^ 2 * P.w + P.x * P.y * P.z + P.x * P.y * P.w +
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w +
    P.z * P.w ^ 2

/-- The gradient row of the reduced canonical quadric. -/
def canonicalQuadricGradient25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨P.z + P.w, P.z, P.x + P.y + P.w, P.x + P.z⟩

/-- The gradient row of the reduced canonical cubic. -/
def canonicalCubicGradient25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨P.y * P.z + P.y * P.w + P.z * P.w,
    P.x * P.z + P.x * P.w + P.z * P.w,
    P.x * P.y + P.x * P.w + P.y * P.w + P.w ^ 2,
    P.x ^ 2 + P.x * P.y + P.x * P.z + P.y * P.z + P.z ^ 2⟩

/-- The six two-by-two minors of the quadric and cubic gradient rows. -/
structure CanonicalJacobianMinors25 (K : Type*) where
  xy : K
  xz : K
  xw : K
  yz : K
  yw : K
  zw : K

/-- Evaluate the six Jacobian minors at a homogeneous coordinate vector. -/
def canonicalJacobianMinors25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : CanonicalJacobianMinors25 K :=
  let q := canonicalQuadricGradient25CharTwo P
  let k := canonicalCubicGradient25CharTwo P
  ⟨q.x * k.y - q.y * k.x,
    q.x * k.z - q.z * k.x,
    q.x * k.w - q.w * k.x,
    q.y * k.z - q.z * k.y,
    q.y * k.w - q.w * k.y,
    q.z * k.w - q.w * k.z⟩

/-- Simultaneous vanishing condition defining a singular point of the
codimension-two complete intersection. -/
def IsCanonicalSingular25CharTwo {K : Type*} [CommRing K]
    (P : Coordinates4 K) : Prop :=
  let M := canonicalJacobianMinors25CharTwo P
  canonicalQuadric25CharTwo P = 0 ∧
    canonicalCubic25CharTwo P = 0 ∧
    M.xy = 0 ∧ M.xz = 0 ∧ M.xw = 0 ∧
    M.yz = 0 ∧ M.yw = 0 ∧ M.zw = 0

/-! ## Four chartwise Bézout identities -/

/-- Bézout certificate excluding a singular point on the chart `x=1`. -/
theorem xChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (y z w : K) :
    let P : Coordinates4 K := ⟨1, y, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (y*z*w + z^2 + z*w + w^2 + y + w) * q +
      (y*z*w + z^2 + y*w + z*w + w^2 + z + w) * k +
      (y*w + y + z + w + 1) * M.xz +
      (y*w + y + z + w + 1) * M.xw +
      (y*z^2*w + z^3 + y^2*w + z^2*w + y*w^2 + z*w^2 +
        y^2 + y*z + y*w + w^2 + y + z + w) * M.yz +
      (y + 1) * M.yw + (y + 1) * M.zw = 1 := by
  dsimp [canonicalQuadric25CharTwo, canonicalCubic25CharTwo,
    canonicalJacobianMinors25CharTwo, canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, add_zero]
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have height : (8 : K) = 0 := by
    calc
      (8 : K) = 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have hten : (10 : K) = 0 := by
    calc
      (10 : K) = 2 + 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  ring_nf
  simp [htwo, hfour]

/-- Bézout certificate excluding a singular point on the chart `y=1`. -/
theorem yChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x z w : K) :
    let P : Coordinates4 K := ⟨x, 1, z, w⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^2*w + z^3*w + x*z*w^2 + z^2*w^2 + z*w^3 +
        x*z^2 + z^3 + x*z*w + z^2*w + x*w + z + 1) * q +
      (x*z*w + z^2*w + z*w^2 + x*w) * k +
      (x*z*w + z^2*w + z*w^2 + z^2 + x*w) * M.xy +
      (x^2*z + x*z^2 + x*z*w + z^2*w + x^2 + z^2 + x + z) * M.xz +
      (z*w^2 + z^2 + z + w + 1) * M.yz +
      (z*w) * M.yw = 1 := by
  dsimp [canonicalQuadric25CharTwo, canonicalCubic25CharTwo,
    canonicalJacobianMinors25CharTwo, canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, add_zero]
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have height : (8 : K) = 0 := by
    calc
      (8 : K) = 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have hten : (10 : K) = 0 := by
    calc
      (10 : K) = 2 + 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  ring_nf
  simp [htwo, hfour, hsix, height, hten]

/-- Bézout certificate excluding a singular point on the chart `z=1`. -/
theorem zChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x y w : K) :
    let P : Coordinates4 K := ⟨x, y, 1, w⟩
    let q := canonicalQuadric25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x^2 + x*y + x*w + y) * q +
      (x*w + w^2 + w + 1) * M.xy +
      (x^2 + x*w + x + w) * M.xz +
      (x^2*w + w^3 + x*y + y*w + w^2 + w) * M.xw +
      (x*w + w^2 + y + w + 1) * M.yz +
      (x^2*w + w^3 + x*y + x*w + y*w + y + w + 1) * M.yw +
      (x*w + w^2 + y + 1) * M.zw = 1 := by
  dsimp [canonicalQuadric25CharTwo, canonicalCubic25CharTwo,
    canonicalJacobianMinors25CharTwo, canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, add_zero]
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  ring_nf
  simp [htwo, hfour, hsix]

/-- Bézout certificate excluding a singular point on the chart `w=1`. -/
theorem wChart_jacobian_certificate
    {K : Type*} [CommRing K] [CharP K 2] (x y z : K) :
    let P : Coordinates4 K := ⟨x, y, z, 1⟩
    let q := canonicalQuadric25CharTwo P
    let k := canonicalCubic25CharTwo P
    let M := canonicalJacobianMinors25CharTwo P
    (x*z^4 + z^4 + x*y*z + y^2*z + z^3 + x*y + y^2 + x*z + y*z) * q +
      (x*z^2 + x*z + y + z + 1) * k +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + 1) * M.xy +
      (x*z^3 + x*z^2 + z^3 + x*y + y^2 + z^2 + x + z + 1) * M.xz +
      (x*z + x + z) * M.yz +
      (x*z^2 + x*z + z^2) * M.yw +
      (z^2 + 1) * M.zw = 1 := by
  dsimp [canonicalQuadric25CharTwo, canonicalCubic25CharTwo,
    canonicalJacobianMinors25CharTwo, canonicalQuadricGradient25CharTwo,
    canonicalCubicGradient25CharTwo]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, add_zero]
  have hsix : (6 : K) = 0 := by
    calc
      (6 : K) = 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  have height : (8 : K) = 0 := by
    calc
      (8 : K) = 2 + 2 + 2 + 2 := by norm_num
      _ = 0 := by simp [htwo]
  ring_nf
  simp [htwo, hfour, hsix, height]

/-! ## Algebraic-closure-valid projective consequence -/

/-- The standard ring operations used to turn a normalized projective chart
into homogeneous coordinates over a characteristic-two field. -/
def fieldBinaryOperations (K : Type*) [Field K] : BinaryRingOperations K where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

/-- Homogeneous coordinates of a normalized projective point over a field. -/
def normalizedCoordinates25 {K : Type*} [Field K]
    (P : NormalizedProjective4 K) : Coordinates4 K :=
  P.coordinates (fieldBinaryOperations K)

/-- No normalized projective point over any characteristic-two field is a
singular point of the canonical complete intersection.  Applying this theorem
to an algebraic closure supplies the geometric Jacobian-criterion
certificate needed for good reduction at two. -/
theorem normalized_projective_point_not_singular
    {K : Type*} [Field K] [CharP K 2] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25CharTwo (normalizedCoordinates25 P) := by
  intro hsing
  cases P with
  | xChart y z w =>
      change IsCanonicalSingular25CharTwo
        (⟨1, y, z, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := xChart_jacobian_certificate y z w
      simp [hq, hk, hxz, hxw, hyz, hyw, hzw] at hcert
  | yChart z w =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 1, z, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := yChart_jacobian_certificate (0 : K) z w
      simp [hq, hk, hxy, hxz, hyz, hyw] at hcert
  | zChart w =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 0, 1, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := zChart_jacobian_certificate (0 : K) 0 w
      simp [hq, hxy, hxz, hxw, hyz, hyw, hzw] at hcert
  | wChart =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 0, 0, 1⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := wChart_jacobian_certificate (K := K) 0 0 0
      simp [hq, hk, hxy, hxz, hyz, hyw, hzw] at hcert

end MazurProof.RationalPointsN25QuotientSmoothF2
