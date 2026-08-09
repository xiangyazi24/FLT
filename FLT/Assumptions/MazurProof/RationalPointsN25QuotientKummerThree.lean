import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeilThreeDefs

/-!
# The order-five Kummer model in characteristic three

The canonical level-25 curve carries a proved automorphism of order five.
Over a characteristic-three field containing a fifth root of unity `e`, its
four-dimensional representation diagonalizes.  In the eigenbasis the
canonical quadric is the Segre quadric, so the substitution

```
(u₁,u₂,u₃,u₄) = (ac,ad,bc,bd)
```

solves the quadric identically.  The cubic then becomes a four-term
bidegree-`(3,3)` equation.  On the dense chart `a=c=1`, the invariant
parameter `t=r²s` converts that equation to a cyclic Kummer equation of
degree five.

This file proves those reductions symbolically over every field of
characteristic three.  Finite computation is deliberately postponed until
the final one-dimensional quotient fibres.
-/

namespace MazurProof.RationalPointsN25QuotientKummerThree

open RationalPointsN25CanonicalPoints
open RationalPointsN25QuotientF2

section StructuralModel

variable {K : Type*} [Field K] [CharP K 3]

/-- The fifth-cyclotomic relation imposed on the eigenvalue `e` of the
order-five automorphism. -/
def IsCyclotomicFive25Three (e : K) : Prop :=
  e ^ 4 + e ^ 3 + e ^ 2 + e + 1 = 0

/-- The canonical quadric over an arbitrary coefficient field.  This is the
base change of the stored rational equation. -/
def canonicalQuadric25Three (P : Coordinates4 K) : K :=
  -P.x * P.z - P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

/-- The canonical cubic over an arbitrary coefficient field.  This is the
base change of the stored rational equation. -/
def canonicalCubic25Three (P : Coordinates4 K) : K :=
  P.x ^ 2 * P.w + P.x * P.y * P.z - P.x * P.y * P.w -
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w -
    P.z * P.w ^ 2

/-- The first nontrivial coefficient in the four-term Segre cubic. -/
def segreCoefficientA25Three (e : K) : K :=
  2 * e ^ 3 + e + 1

/-- The second nontrivial coefficient in the four-term Segre cubic. -/
def segreCoefficientB25Three (e : K) : K :=
  e ^ 3 + 2 * e ^ 2 + 2 * e + 1

/-- The cubic left after diagonalizing the order-five action and solving the
canonical quadric by the Segre parametrization.  Its four monomials all have
weight zero for `(r,s) ↦ (e²r,es)`. -/
def canonicalSegreCubic25Three (e a b c d : K) : K :=
  a ^ 2 * b * c ^ 3 +
    segreCoefficientA25Three e * b ^ 3 * c ^ 2 * d +
    segreCoefficientB25Three e * a ^ 3 * c * d ^ 2 +
    e ^ 2 * a * b ^ 2 * d ^ 3

/-- The inverse eigenbasis matrix, already reduced modulo the fifth
cyclotomic polynomial in characteristic three.

The inputs are the four eigen-coordinates and the outputs are the original
canonical coordinates `(x,y,z,w)`.  Keeping this linear map separate from
the Segre parametrization makes its inverse available for the projective
chart comparison. -/
def canonicalCoordinatesFromEigen25Three
    (e u₁ u₂ u₃ u₄ : K) : Coordinates4 K :=
  ⟨
    (e ^ 2 + 2) * u₁ +
      (2 * e ^ 3 + 2 * e ^ 2 + 2 * e + 1) * u₂ +
      (e + 2) * u₃ + (e ^ 3 + 2) * u₄,
    (2 * e ^ 3 + e ^ 2) * u₁ +
      (2 * e ^ 3 + 2 * e ^ 2 + e + 2) * u₂ +
      (e ^ 3 + e ^ 2 + 2 * e + 1) * u₃ +
      (e ^ 3 + 2 * e ^ 2) * u₄,
    (e ^ 3 + 2 * e) * u₁ + (2 * e ^ 2 + e) * u₂ +
      (e ^ 3 + 2 * e ^ 2 + 2 * e + 2) * u₃ +
      (e ^ 3 + 2 * e ^ 2 + e + 1) * u₄,
    (e ^ 3 + 2 * e ^ 2 + e + 1) * u₁ +
      (e ^ 3 + 2 * e ^ 2 + 2 * e + 2) * u₂ +
      (2 * e ^ 2 + e) * u₃ + (e ^ 3 + 2 * e) * u₄
  ⟩

/-- The explicit forward eigenbasis matrix taking canonical coordinates
`(x,y,z,w)` back to the four order-five eigencoordinates.

These coefficients are the inverse of
`canonicalCoordinatesFromEigen25Three` over the fifth-cyclotomic locus. -/
def canonicalEigenCoordinates25Three (e : K)
    (P : Coordinates4 K) : Coordinates4 K :=
  ⟨
    P.x + (2 + 2 * e + 2 * e ^ 3) * P.y +
      (2 + 2 * e + 2 * e ^ 2 + 2 * e ^ 3) * P.z + e * P.w,
    P.x + (2 + 2 * e + 2 * e ^ 2) * P.y + e ^ 3 * P.z + e ^ 2 * P.w,
    P.x + (e + e ^ 2) * P.y + e ^ 2 * P.z + e ^ 3 * P.w,
    P.x + (e + e ^ 3) * P.y + e * P.z +
      (2 + 2 * e + 2 * e ^ 2 + 2 * e ^ 3) * P.w
  ⟩

/-- Apply the inverse eigenbasis after the Segre map
`(u₁,u₂,u₃,u₄)=(ac,ad,bc,bd)`.

Avoiding projective normalization here keeps the algebraic change of
variables homogeneous and denominator-free. -/
def canonicalSegreCoordinates25Three (e a b c d : K) : Coordinates4 K :=
  canonicalCoordinatesFromEigen25Three e (a * c) (a * d) (b * c) (b * d)

/-- The forward and inverse eigenbasis matrices compose to the identity on
eigen-coordinates.

The proof reduces powers of `e` with the fifth-cyclotomic relation.  Every
remaining coefficient is a multiple of three, so characteristic three
finishes the four coordinate identities. -/
theorem canonicalEigenCoordinates_fromEigen {e u₁ u₂ u₃ u₄ : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalEigenCoordinates25Three e
      (canonicalCoordinatesFromEigen25Three e u₁ u₂ u₃ u₄) =
        ⟨u₁, u₂, u₃, u₄⟩ := by
  unfold IsCyclotomicFive25Three at he
  have he₄ : e ^ 4 = -e ^ 3 - e ^ 2 - e - 1 := by
    linear_combination he
  have he₅ : e ^ 5 = 1 := by
    apply sub_eq_zero.mp
    calc
      e ^ 5 - 1 = (e - 1) * (e ^ 4 + e ^ 3 + e ^ 2 + e + 1) := by ring
      _ = 0 := by rw [he]; ring
  have he₆ : e ^ 6 = e := by
    rw [show e ^ 6 = e ^ 5 * e by ring, he₅, one_mul]
  simp only [canonicalEigenCoordinates25Three,
    canonicalCoordinatesFromEigen25Three, Coordinates4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf
  all_goals simp only [he₆, he₅, he₄]
  all_goals ring_nf
  · linear_combination
      (e * u₂ + e * u₃ - e * u₄ - e ^ 2 * u₁ + e ^ 2 * u₂ +
        e ^ 2 * u₃ + e ^ 2 * u₄ + e ^ 3 * u₁ + 3 * e ^ 3 * u₂ +
        2 * e ^ 3 * u₃ + 2 * e ^ 3 * u₄ - 2 * u₁ + u₄) *
        CharP.cast_eq_zero K 3
  · linear_combination
      (-e * u₂ - 3 * e * u₁ - 2 * e * u₄ + e ^ 2 * u₂ -
        2 * e ^ 2 * u₁ - e ^ 2 * u₄ + e ^ 3 * u₂ + e ^ 3 * u₃ -
        e ^ 3 * u₁ + e ^ 3 * u₄ - u₁) * CharP.cast_eq_zero K 3
  · linear_combination
      (-e * u₂ - e * u₃ - e * u₁ - 2 * e * u₄ - e ^ 2 * u₂ -
        e ^ 2 * u₁ - 2 * e ^ 2 * u₄ - e ^ 3 * u₄ - u₂ + u₁ - u₄) *
        CharP.cast_eq_zero K 3
  · linear_combination
      (-e * u₁ + e * u₂ - e * u₃ + e ^ 2 * u₂ - e ^ 2 * u₄ +
        3 * e ^ 3 * u₂ + e ^ 3 * u₄ - u₃ - u₄) * CharP.cast_eq_zero K 3

/-- The inverse and forward eigenbasis matrices compose to the identity on
canonical coordinates. -/
theorem canonicalCoordinatesFromEigen_eigen {e : K} {P : Coordinates4 K}
    (he : IsCyclotomicFive25Three e) :
    canonicalCoordinatesFromEigen25Three e
      (canonicalEigenCoordinates25Three e P).x
      (canonicalEigenCoordinates25Three e P).y
      (canonicalEigenCoordinates25Three e P).z
      (canonicalEigenCoordinates25Three e P).w = P := by
  rcases P with ⟨x, y, z, w⟩
  unfold IsCyclotomicFive25Three at he
  have he₄ : e ^ 4 = -e ^ 3 - e ^ 2 - e - 1 := by
    linear_combination he
  have he₅ : e ^ 5 = 1 := by
    apply sub_eq_zero.mp
    calc
      e ^ 5 - 1 = (e - 1) * (e ^ 4 + e ^ 3 + e ^ 2 + e + 1) := by ring
      _ = 0 := by rw [he]; ring
  have he₆ : e ^ 6 = e := by
    rw [show e ^ 6 = e ^ 5 * e by ring, he₅, one_mul]
  simp only [canonicalEigenCoordinates25Three,
    canonicalCoordinatesFromEigen25Three, Coordinates4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf
  all_goals simp only [he₆, he₅, he₄]
  all_goals ring_nf
  · linear_combination
      (e * x + 2 * e * y + e * z + e * w + e ^ 2 * x + 2 * e ^ 2 * y +
        e ^ 2 * z + e ^ 3 * x + 4 * e ^ 3 * y + e ^ 3 * z + 2 * e ^ 3 * w +
        2 * x + y + z + w) * CharP.cast_eq_zero K 3
  · linear_combination
      (e * x - e * y - e * z - 3 * e * w + 2 * e ^ 2 * x - 2 * e ^ 2 * z -
        2 * e ^ 2 * w + 2 * e ^ 3 * x + 2 * e ^ 3 * y + e ^ 3 * z -
        e ^ 3 * w + x - y - w) * CharP.cast_eq_zero K 3
  · linear_combination
      (2 * e * x - e * y - e * z - 2 * e * w + 2 * e ^ 2 * x - e ^ 2 * z -
        e ^ 2 * w + e ^ 3 * x + x - 4 * y - 2 * z - w) *
        CharP.cast_eq_zero K 3
  · linear_combination
      (2 * e * x - 2 * e * z - e * w + 2 * e ^ 2 * x + 2 * e ^ 2 * y -
        e ^ 2 * z - e ^ 2 * w + e ^ 3 * x + 2 * e ^ 3 * y + x - y - z - 2 * w) *
        CharP.cast_eq_zero K 3

/-- The two explicit matrices define a genuine linear coordinate
equivalence on the fifth-cyclotomic locus. -/
def canonicalEigenCoordinateEquiv25Three (e : K)
    (he : IsCyclotomicFive25Three e) : Coordinates4 K ≃ Coordinates4 K where
  toFun := canonicalEigenCoordinates25Three e
  invFun U := canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w
  left_inv P := canonicalCoordinatesFromEigen_eigen he
  right_inv U := by
    rcases U with ⟨u₁, u₂, u₃, u₄⟩
    exact canonicalEigenCoordinates_fromEigen he

/-- Applying the forward eigenbasis to a Segre point recovers the four
products `(ac,ad,bc,bd)` exactly. -/
theorem canonicalEigenCoordinates_segre {e a b c d : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalEigenCoordinates25Three e
      (canonicalSegreCoordinates25Three e a b c d) =
        ⟨a * c, a * d, b * c, b * d⟩ := by
  exact canonicalEigenCoordinates_fromEigen he

/-- The nonzero scalar relating the canonical quadric to the determinant
quadric in eigen-coordinates. -/
def canonicalSegreQuadricScalar25Three (e : K) : K :=
  1 + 2 * e ^ 2 + 2 * e ^ 3

/-- The quadric scalar cannot vanish at a fifth-cyclotomic eigenvalue.

The displayed Bézout identity combines the fifth-cyclotomic polynomial with
the scalar to obtain one; the remaining coefficient is a multiple of three. -/
theorem canonicalSegreQuadricScalar25Three_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalSegreQuadricScalar25Three e ≠ 0 := by
  intro hs
  unfold IsCyclotomicFive25Three at he
  unfold canonicalSegreQuadricScalar25Three at hs
  have hone : (1 : K) = 0 := by
    linear_combination
      (e ^ 2 + e - 1) * he + (e ^ 3 + e ^ 2 - 1) * hs -
      (e ^ 6 + 2 * e ^ 5 + e ^ 4 - 1) * CharP.cast_eq_zero K 3
  exact one_ne_zero hone

/-- In eigen-coordinates, the canonical quadric is a nonzero scalar times
the determinant `u₂u₃-u₁u₄`.

This single matrix identity is the structural content behind the Segre
parametrization.  The proof is polynomial reduction modulo the
fifth-cyclotomic relation and characteristic three, not a point table. -/
theorem canonicalQuadric25_fromEigen {e u₁ u₂ u₃ u₄ : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalQuadric25Three
      (canonicalCoordinatesFromEigen25Three e u₁ u₂ u₃ u₄) =
      canonicalSegreQuadricScalar25Three e * (u₂ * u₃ - u₁ * u₄) := by
  unfold IsCyclotomicFive25Three at he
  unfold canonicalQuadric25Three canonicalCoordinatesFromEigen25Three
    canonicalSegreQuadricScalar25Three
  linear_combination
    (7 * e ^ 2 * u₁ ^ 2 + 7 * e ^ 2 * u₁ * u₂ +
      8 * e ^ 2 * u₁ * u₃ + 7 * e ^ 2 * u₁ * u₄ +
      2 * e ^ 2 * u₂ ^ 2 + 5 * e ^ 2 * u₂ * u₃ +
      2 * e ^ 2 * u₂ * u₄ + 2 * e ^ 2 * u₃ ^ 2 +
      4 * e ^ 2 * u₃ * u₄ + e ^ 2 * u₄ ^ 2 -
      2 * e * u₁ ^ 2 + 6 * e * u₁ * u₂ + 9 * e * u₁ * u₃ +
      10 * e * u₁ * u₄ + 2 * e * u₂ ^ 2 + 5 * e * u₂ * u₃ +
      12 * e * u₂ * u₄ + 5 * e * u₃ ^ 2 + 9 * e * u₃ * u₄ +
      7 * e * u₄ ^ 2 + u₁ ^ 2 - 5 * u₁ * u₂ + 5 * u₁ * u₃ -
      2 * u₁ * u₄ - u₂ ^ 2 + 11 * u₂ * u₃ - u₂ * u₄ +
      8 * u₃ ^ 2 + 10 * u₃ * u₄ + u₄ ^ 2) * he +
    (-2 * e ^ 3 * u₁ ^ 2 - e ^ 3 * u₁ * u₃ -
      4 * e ^ 3 * u₁ * u₄ + e ^ 3 * u₂ * u₃ -
      2 * e ^ 3 * u₄ ^ 2 - 3 * e ^ 2 * u₁ ^ 2 -
      5 * e ^ 2 * u₁ * u₂ - 7 * e ^ 2 * u₁ * u₃ -
      4 * e ^ 2 * u₁ * u₄ + e ^ 2 * u₂ ^ 2 -
      3 * e ^ 2 * u₂ * u₃ - 2 * e ^ 2 * u₂ * u₄ -
      2 * e ^ 2 * u₃ ^ 2 - 6 * e ^ 2 * u₃ * u₄ -
      3 * e ^ 2 * u₄ ^ 2 - e * u₁ ^ 2 - e * u₁ * u₂ -
      7 * e * u₁ * u₃ - 6 * e * u₁ * u₄ - 2 * e * u₂ * u₃ -
      5 * e * u₂ * u₄ - 3 * e * u₃ ^ 2 - 8 * e * u₃ * u₄ -
      4 * e * u₄ ^ 2 - u₁ ^ 2 - 3 * u₁ * u₃ + u₂ ^ 2 -
      2 * u₂ * u₃ - 3 * u₃ ^ 2 - 5 * u₃ * u₄ - u₄ ^ 2) *
      CharP.cast_eq_zero K 3

omit [CharP K 3] in
/-- Every point of the determinant quadric `u₂u₃=u₁u₄` factors as a
rank-one matrix `(u₁,u₂,u₃,u₄)=(ac,ad,bc,bd)`.

The proof uses the `u₁≠0` chart and the two boundary rulings `u₁=u₂=0`
and `u₁=u₃=0`.  These are exactly the three pieces later used by the
Kummer dense-chart and boundary count. -/
theorem exists_segre_factorization_of_det_eq_zero {u₁ u₂ u₃ u₄ : K}
    (hdet : u₂ * u₃ - u₁ * u₄ = 0) :
    ∃ a b c d : K,
      a * c = u₁ ∧ a * d = u₂ ∧ b * c = u₃ ∧ b * d = u₄ := by
  by_cases hu₁ : u₁ = 0
  · subst u₁
    have hprod : u₂ * u₃ = 0 := by simpa using hdet
    by_cases hu₂ : u₂ = 0
    · subst u₂
      exact ⟨0, 1, u₃, u₄, by simp⟩
    · have hu₃ : u₃ = 0 := (mul_eq_zero.mp hprod).resolve_left hu₂
      subst u₃
      refine ⟨1, u₄ / u₂, 0, u₂, ?_⟩
      simp only [one_mul, mul_zero, true_and]
      exact div_mul_cancel₀ u₄ hu₂
  · refine ⟨1, u₃ / u₁, u₁, u₂, ?_⟩
    simp only [one_mul, true_and]
    constructor
    · exact div_mul_cancel₀ u₃ hu₁
    · rw [div_mul_eq_mul_div, div_eq_iff hu₁]
      linear_combination hdet

/-- Every canonical-quadric point comes from the explicit Segre map.

Apply the forward eigenbasis, use the nonzero quadric scalar to obtain the
determinant equation, factor the resulting rank-one matrix, and finally use
the inverse eigenbasis identity.  This closes the coordinate-surjectivity
part of the projective Segre bridge without enumerating points. -/
theorem exists_canonicalSegreCoordinates_of_quadric_eq_zero
    {e : K} {P : Coordinates4 K}
    (he : IsCyclotomicFive25Three e)
    (hQ : canonicalQuadric25Three P = 0) :
    ∃ a b c d : K, canonicalSegreCoordinates25Three e a b c d = P := by
  let U := canonicalEigenCoordinates25Three e P
  have hback :
      canonicalCoordinatesFromEigen25Three e U.x U.y U.z U.w = P :=
    canonicalCoordinatesFromEigen_eigen he
  have hnormal := canonicalQuadric25_fromEigen
    (e := e) (u₁ := U.x) (u₂ := U.y) (u₃ := U.z) (u₄ := U.w) he
  rw [hback, hQ] at hnormal
  have hdet : U.y * U.z - U.x * U.w = 0 := by
    have hprod : canonicalSegreQuadricScalar25Three e *
        (U.y * U.z - U.x * U.w) = 0 := hnormal.symm
    exact (mul_eq_zero.mp hprod).resolve_left
      (canonicalSegreQuadricScalar25Three_ne_zero he)
  rcases exists_segre_factorization_of_det_eq_zero hdet with
    ⟨a, b, c, d, hac, had, hbc, hbd⟩
  refine ⟨a, b, c, d, ?_⟩
  unfold canonicalSegreCoordinates25Three
  rw [hac, had, hbc, hbd]
  exact hback

/-- The inverse eigenbasis sends every Segre point to the canonical quadric.
The proof is a polynomial consequence of the fifth-cyclotomic relation and
the characteristic-three identity `3=0`; no finite field is enumerated. -/
theorem canonicalQuadric25_segre_eq_zero {e a b c d : K}
    (he : IsCyclotomicFive25Three e) :
    let P := canonicalSegreCoordinates25Three e a b c d
    canonicalQuadric25Three P = 0 := by
  change canonicalQuadric25Three
    (canonicalCoordinatesFromEigen25Three e (a * c) (a * d) (b * c) (b * d)) = 0
  rw [canonicalQuadric25_fromEigen he]
  ring

/-- On the Segre quadric, the original canonical cubic is the four-term
Segre cubic multiplied by `e³+1`.  Thus the diagonal change of coordinates
identifies the two curve equations once that harmless scalar is shown
nonzero. -/
theorem canonicalCubic25_segre {e a b c d : K}
    (he : IsCyclotomicFive25Three e) :
    let P := canonicalSegreCoordinates25Three e a b c d
    canonicalCubic25Three P =
      (e ^ 3 + 1) * canonicalSegreCubic25Three e a b c d := by
  unfold IsCyclotomicFive25Three at he
  have he₄ : e ^ 4 = -e ^ 3 - e ^ 2 - e - 1 := by
    linear_combination he
  have he₅ : e ^ 5 = 1 := by
    apply sub_eq_zero.mp
    calc
      e ^ 5 - 1 = (e - 1) * (e ^ 4 + e ^ 3 + e ^ 2 + e + 1) := by ring
      _ = 0 := by rw [he]; ring
  have he₆ : e ^ 6 = e := by rw [show e ^ 6 = e ^ 5 * e by ring, he₅, one_mul]
  have he₇ : e ^ 7 = e ^ 2 := by
    rw [show e ^ 7 = e ^ 5 * e ^ 2 by ring, he₅, one_mul]
  have he₈ : e ^ 8 = e ^ 3 := by
    rw [show e ^ 8 = e ^ 5 * e ^ 3 by ring, he₅, one_mul]
  have he₉ : e ^ 9 = e ^ 4 := by
    rw [show e ^ 9 = e ^ 5 * e ^ 4 by ring, he₅, one_mul]
  simp only [canonicalSegreCoordinates25Three,
    canonicalCoordinatesFromEigen25Three, canonicalCubic25Three,
    canonicalSegreCubic25Three, segreCoefficientA25Three,
    segreCoefficientB25Three]
  ring_nf
  simp only [he₉, he₈, he₇, he₆, he₅, he₄]
  ring_nf
  linear_combination
    (-5 * e ^ 3 * a ^ 3 * c ^ 3 - 2 * e ^ 3 * a ^ 2 * b * c ^ 3 +
      6 * e ^ 3 * a * b ^ 2 * c ^ 3 + 2 * e ^ 3 * b ^ 3 * c ^ 3 -
      2 * e ^ 3 * a ^ 3 * c ^ 2 * d + 11 * e ^ 3 * a ^ 2 * b * c ^ 2 * d -
      3 * e ^ 3 * a * b ^ 2 * c ^ 2 * d - 5 * e ^ 3 * b ^ 3 * c ^ 2 * d +
      e ^ 3 * a ^ 3 * c * d ^ 2 - 4 * e ^ 3 * a ^ 2 * b * c * d ^ 2 -
      3 * e ^ 3 * a * b ^ 2 * c * d ^ 2 - e ^ 3 * b ^ 3 * c * d ^ 2 -
      3 * e ^ 3 * a ^ 3 * d ^ 3 - 5 * e ^ 3 * a ^ 2 * b * d ^ 3 -
      6 * e ^ 3 * a * b ^ 2 * d ^ 3 - 2 * e ^ 3 * b ^ 3 * d ^ 3 -
      e ^ 2 * a ^ 2 * b * c ^ 3 + 5 * e ^ 2 * a * b ^ 2 * c ^ 3 +
      3 * e ^ 2 * b ^ 3 * c ^ 3 + 3 * e ^ 2 * a ^ 3 * c ^ 2 * d +
      14 * e ^ 2 * a ^ 2 * b * c ^ 2 * d +
      8 * e ^ 2 * a * b ^ 2 * c ^ 2 * d + 2 * e ^ 2 * a ^ 3 * c * d ^ 2 -
      11 * e ^ 2 * a ^ 2 * b * c * d ^ 2 -
      13 * e ^ 2 * a * b ^ 2 * c * d ^ 2 - e ^ 2 * b ^ 3 * c * d ^ 2 +
      3 * e ^ 2 * a ^ 2 * b * d ^ 3 + 3 * e ^ 2 * a * b ^ 2 * d ^ 3 -
      e ^ 2 * b ^ 3 * d ^ 3 - e * a ^ 3 * c ^ 3 +
      6 * e * a ^ 2 * b * c ^ 3 + 6 * e * a * b ^ 2 * c ^ 3 +
      e * b ^ 3 * c ^ 3 + 2 * e * a ^ 3 * c ^ 2 * d +
      11 * e * a ^ 2 * b * c ^ 2 * d + 2 * e * a * b ^ 2 * c ^ 2 * d +
      3 * e * b ^ 3 * c ^ 2 * d + 5 * e * a ^ 3 * c * d ^ 2 +
      13 * e * a ^ 2 * b * c * d ^ 2 + 16 * e * a * b ^ 2 * c * d ^ 2 +
      9 * e * b ^ 3 * c * d ^ 2 + 2 * e * a ^ 3 * d ^ 3 +
      3 * e * a ^ 2 * b * d ^ 3 + e * b ^ 3 * d ^ 3 -
      5 * a ^ 3 * c ^ 3 - 8 * a ^ 2 * b * c ^ 3 + 2 * a * b ^ 2 * c ^ 3 +
      4 * a ^ 3 * c ^ 2 * d + 28 * a ^ 2 * b * c ^ 2 * d +
      12 * a * b ^ 2 * c ^ 2 * d + b ^ 3 * c ^ 2 * d +
      2 * a ^ 3 * c * d ^ 2 + 2 * a ^ 2 * b * c * d ^ 2 +
      11 * a * b ^ 2 * c * d ^ 2 + 7 * b ^ 3 * c * d ^ 2 +
      2 * a ^ 3 * d ^ 3 + 3 * a ^ 2 * b * d ^ 3 +
      9 * a * b ^ 2 * d ^ 3 + 2 * b ^ 3 * d ^ 3) *
        CharP.cast_eq_zero K 3

/-- A fifth-cyclotomic eigenvalue is nonzero. -/
theorem cyclotomicFive25Three_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) : e ≠ 0 := by
  intro h
  subst e
  norm_num [IsCyclotomicFive25Three] at he

/-- The scalar `e³+1` relating the two cubics cannot vanish for a
fifth-cyclotomic eigenvalue in characteristic three. -/
theorem cyclotomicFive25Three_cubicScalar_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) : e ^ 3 + 1 ≠ 0 := by
  have he_ne := cyclotomicFive25Three_ne_zero he
  intro hs
  unfold IsCyclotomicFive25Three at he
  have he₃ : e ^ 3 = -1 := by linear_combination hs
  have he₄ : e ^ 4 = -e := by rw [show e ^ 4 = e ^ 3 * e by ring, he₃]; ring
  rw [he₄, he₃] at he
  have he₂ : e ^ 2 = 0 := by
    linear_combination he
  have he_zero : e = 0 := by
    have hmul : e * e = 0 := by simpa [pow_two] using he₂
    exact (mul_eq_zero.mp hmul).elim id id
  exact he_ne he_zero

/-- A canonical affine-cone point lies on the quadric-cubic curve exactly
when it is the image of a Segre point satisfying the four-term cubic.

The reverse direction uses surjectivity of the Segre parametrization of the
quadric.  The cubic comparison is reversible because its scalar `e³+1` is
nonzero.  Thus no equation or point is lost in the characteristic-three
coordinate change. -/
theorem canonicalCurve_eq_zero_iff_exists_segre
    {e : K} {P : Coordinates4 K} (he : IsCyclotomicFive25Three e) :
    canonicalQuadric25Three P = 0 ∧ canonicalCubic25Three P = 0 ↔
      ∃ a b c d : K,
        P = canonicalSegreCoordinates25Three e a b c d ∧
          canonicalSegreCubic25Three e a b c d = 0 := by
  constructor
  · rintro ⟨hQ, hC⟩
    rcases exists_canonicalSegreCoordinates_of_quadric_eq_zero he hQ with
      ⟨a, b, c, d, hP⟩
    have hcubic := canonicalCubic25_segre
      (e := e) (a := a) (b := b) (c := c) (d := d) he
    change canonicalCubic25Three
        (canonicalSegreCoordinates25Three e a b c d) =
      (e ^ 3 + 1) * canonicalSegreCubic25Three e a b c d at hcubic
    rw [hP, hC] at hcubic
    have hsegre : canonicalSegreCubic25Three e a b c d = 0 := by
      have hprod : (e ^ 3 + 1) * canonicalSegreCubic25Three e a b c d = 0 :=
        hcubic.symm
      exact (mul_eq_zero.mp hprod).resolve_left
        (cyclotomicFive25Three_cubicScalar_ne_zero he)
    exact ⟨a, b, c, d, hP.symm, hsegre⟩
  · rintro ⟨a, b, c, d, rfl, hsegre⟩
    constructor
    · exact canonicalQuadric25_segre_eq_zero he
    · have hcubic := canonicalCubic25_segre
        (e := e) (a := a) (b := b) (c := c) (d := d) he
      change canonicalCubic25Three
          (canonicalSegreCoordinates25Three e a b c d) =
        (e ^ 3 + 1) * canonicalSegreCubic25Three e a b c d at hcubic
      simpa [hsegre] using hcubic

/-- The coefficient `A=2e³+e+1` is nonzero on the fifth-cyclotomic locus.
This prevents an entire boundary ruling of the Segre quadric from lying on
the cubic. -/
theorem segreCoefficientA25Three_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) : segreCoefficientA25Three e ≠ 0 := by
  intro hA
  unfold IsCyclotomicFive25Three at he
  unfold segreCoefficientA25Three at hA
  have hone : (1 : K) = 0 := by
    linear_combination
      (e ^ 2 + e + 1) * he +
      (e ^ 3 + 2 * e ^ 2 + e) * hA -
      (e ^ 6 + 2 * e ^ 5 + 2 * e ^ 4 + 2 * e ^ 3 + 2 * e ^ 2 + e) *
        CharP.cast_eq_zero K 3
  exact one_ne_zero hone

/-- The coefficient `B=e³+2e²+2e+1` is nonzero on the
fifth-cyclotomic locus.  It controls both the dense `r=0` fibre and the
single Kummer point introduced by clearing `r⁴`. -/
theorem segreCoefficientB25Three_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) : segreCoefficientB25Three e ≠ 0 := by
  intro hB
  unfold IsCyclotomicFive25Three at he
  unfold segreCoefficientB25Three at hB
  have hone : (1 : K) = 0 := by
    linear_combination
      (2 * e) * he + (e ^ 2 + 2 * e + 1) * hB -
      (e ^ 5 + 2 * e ^ 4 + 3 * e ^ 3 + 3 * e ^ 2 + 2 * e) *
        CharP.cast_eq_zero K 3
  exact one_ne_zero hone

/-! ## Boundary rulings and the dense Kummer chart -/

/-- On the boundary ruling `a=0`, the cubic has exactly the point `d=0`.
In projective coordinates this is one of the three points outside the dense
Segre chart. -/
theorem segre_boundary_a_zero {e d : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalSegreCubic25Three e 0 1 1 d = 0 ↔ d = 0 := by
  have hA := segreCoefficientA25Three_ne_zero he
  simp [canonicalSegreCubic25Three, hA]

/-- On the boundary ruling `c=0`, the cubic has exactly the point `b=0`.
This is the second point outside the dense Segre chart. -/
theorem segre_boundary_c_zero {e b : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalSegreCubic25Three e 1 b 0 1 = 0 ↔ b = 0 := by
  have he0 := cyclotomicFive25Three_ne_zero he
  simp [canonicalSegreCubic25Three, he0]

/-- The intersection of the two boundary rulings lies on the Segre cubic,
giving the third point outside the dense chart. -/
theorem segre_boundary_corner (e : K) :
    canonicalSegreCubic25Three e 0 1 0 1 = 0 := by
  simp [canonicalSegreCubic25Three]

/-- The dense Segre chart `a=c=1`, with affine coordinates `(r,s)`. -/
def canonicalDenseSegreCubic25Three (e r s : K) : K :=
  canonicalSegreCubic25Three e 1 r 1 s

/-- In the dense chart, setting `r=0` forces `s=0`.  Hence the genuine Segre
curve contributes only `(r,s)=(0,0)` above the zero value of `r`. -/
theorem denseSegre_at_zero {e s : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalDenseSegreCubic25Three e 0 s = 0 ↔ s = 0 := by
  have hB := segreCoefficientB25Three_ne_zero he
  simp [canonicalDenseSegreCubic25Three, canonicalSegreCubic25Three, hB]

/-- The denominator-cleared Kummer equation on the quotient coordinate
`t=r²s`.  For fixed `t` it is a degree-five equation in `r`. -/
def canonicalKummerPolynomial25Three (e r t : K) : K :=
  r ^ 5 * (1 + segreCoefficientA25Three e * t) +
    t ^ 2 * (segreCoefficientB25Three e + e ^ 2 * t)

/-- The coefficient of `r⁵` in the Kummer equation above the quotient
parameter `t`. -/
def canonicalKummerDenominator25Three (e t : K) : K :=
  1 + segreCoefficientA25Three e * t

/-- The constant term in the Kummer equation above the quotient parameter
`t`. -/
def canonicalKummerNumerator25Three (e t : K) : K :=
  t ^ 2 * (segreCoefficientB25Three e + e ^ 2 * t)

/-- When the coefficient of `r⁵` is nonzero, the Kummer equation is the
fifth-power equation `r⁵ = canonicalKummerTarget25Three e t`. -/
def canonicalKummerTarget25Three (e t : K) : K :=
  -canonicalKummerNumerator25Three e t /
    canonicalKummerDenominator25Three e t

omit [CharP K 3] in
/-- On a nondegenerate quotient fibre, the Kummer polynomial vanishes
exactly when `r⁵` equals the normalized target.

This is a field identity: move the constant term to the right and divide by
the nonzero coefficient of `r⁵`. -/
theorem canonicalKummer_eq_zero_iff_fifthPower_eq_target
    (e t : K) {r : K}
    (hden : canonicalKummerDenominator25Three e t ≠ 0) :
    canonicalKummerPolynomial25Three e r t = 0 ↔
      r ^ 5 = canonicalKummerTarget25Three e t := by
  unfold canonicalKummerTarget25Three
  rw [eq_div_iff hden]
  change r ^ 5 * canonicalKummerDenominator25Three e t +
      canonicalKummerNumerator25Three e t = 0 ↔
    r ^ 5 * canonicalKummerDenominator25Three e t =
      -canonicalKummerNumerator25Three e t
  constructor <;> intro h <;> linear_combination h

/-- Multiplying the dense Segre cubic by `r⁴` produces the Kummer equation
with invariant parameter `t=r²s`.  This exact identity is the second
dimension reduction in the characteristic-three point count. -/
theorem denseSegre_to_kummer_identity (e r s : K) :
    r ^ 4 * canonicalDenseSegreCubic25Three e r s =
      canonicalKummerPolynomial25Three e r (r ^ 2 * s) := by
  simp only [canonicalDenseSegreCubic25Three, canonicalSegreCubic25Three,
    canonicalKummerPolynomial25Three]
  ring

/-- Away from `r=0`, the substitution `s=t/r²` is an equivalence between
the dense Segre equation and the Kummer equation.  The excluded zero fibre is
handled separately because clearing `r⁴` creates one extraneous Kummer point. -/
theorem denseSegre_eq_zero_iff_kummer
    (e : K) {r t : K} (hr : r ≠ 0) :
    canonicalDenseSegreCubic25Three e r (t / r ^ 2) = 0 ↔
      canonicalKummerPolynomial25Three e r t = 0 := by
  have hrt : r ^ 2 * (t / r ^ 2) = t := by
    field_simp
  have hid := denseSegre_to_kummer_identity e r (t / r ^ 2)
  rw [hrt] at hid
  constructor
  · intro h
    rw [h, mul_zero] at hid
    exact hid.symm
  · intro h
    rw [h] at hid
    exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero 4 hr)

/-- At `r=0`, the Kummer equation factors into the two possible quotient
parameters.  Only `t=0` comes from `t=r²s`; the second factor records the
single point introduced by clearing the power of `r`. -/
theorem kummer_at_zero (e t : K) :
    canonicalKummerPolynomial25Three e 0 t =
      t ^ 2 * (segreCoefficientB25Three e + e ^ 2 * t) := by
  simp [canonicalKummerPolynomial25Three]

/-- The second zero-fibre parameter created by clearing `r⁴`. -/
def extraneousKummerParameter25Three (e : K) : K :=
  -segreCoefficientB25Three e / e ^ 2

/-- The cleared Kummer equation at `r=0` has exactly two quotient parameters:
the genuine value `t=0` and one nonzero extraneous value. -/
theorem kummer_zero_fibre_iff {e t : K}
    (he : IsCyclotomicFive25Three e) :
    canonicalKummerPolynomial25Three e 0 t = 0 ↔
      t = 0 ∨ t = extraneousKummerParameter25Three e := by
  have he0 := cyclotomicFive25Three_ne_zero he
  rw [kummer_at_zero, mul_eq_zero]
  constructor
  · rintro (ht | ht)
    · left
      have hmul : t * t = 0 := by simpa [pow_two] using ht
      exact (mul_eq_zero.mp hmul).elim id id
    · right
      unfold extraneousKummerParameter25Three
      apply (eq_div_iff (pow_ne_zero 2 he0)).2
      linear_combination ht
  · rintro (rfl | ht)
    · left
      simp
    · right
      unfold extraneousKummerParameter25Three at ht
      have hmul := (eq_div_iff (pow_ne_zero 2 he0)).1 ht
      linear_combination hmul

/-- The extraneous zero-fibre parameter is not zero because both `B` and the
cyclotomic eigenvalue are nonzero. -/
theorem extraneousKummerParameter25Three_ne_zero {e : K}
    (he : IsCyclotomicFive25Three e) :
    extraneousKummerParameter25Three e ≠ 0 := by
  have he0 := cyclotomicFive25Three_ne_zero he
  have hB := segreCoefficientB25Three_ne_zero he
  simp [extraneousKummerParameter25Three, he0, hB]

end StructuralModel

/-! ## Fifth-power fibres over fields with 81 elements

The Kummer equation has the form `r⁵ = c` whenever its linear
coefficient is nonzero.  The following lemmas justify the fibre classifier
structurally.  They use that the unit group of an 81-element field is cyclic
of order 80; no elements of the field are enumerated.
-/

section FifthPowerFibres

open scoped Pointwise

/-- In a cyclic group of order 80, the fifth powers are exactly the elements
whose sixteenth power is one.

Indeed, the fifth-power image is contained in the sixteenth-power kernel
because `(x⁵)¹⁶=x⁸⁰=1`.  Both subgroups have order 16, by the standard
image and kernel cardinality formulas for power maps on finite cyclic
groups. -/
theorem fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) :
    (powMonoidHom 5 : G →* G).range =
      (powMonoidHom 16 : G →* G).ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change (y ^ 5) ^ 16 = 1
    rw [← pow_mul]
    norm_num
    simpa [hcard] using (pow_card_eq_one' (x := y))
  · rw [IsCyclic.card_powMonoidHom_ker,
      IsCyclic.card_powMonoidHom_range, hcard]
    norm_num

/-- Every nonempty fibre of the fifth-power map on a cyclic group of order
80 has five elements.

A chosen point identifies its fibre with the kernel of the homomorphism;
that kernel has order `gcd(80,5)=5`. -/
theorem fifthPowerFiber_card_of_mem_range
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) {c : G}
    (hc : c ∈ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 5 := by
  rcases hc with ⟨a, rfl⟩
  calc
    Nat.card {u : G // u ^ 5 = a ^ 5} =
        Nat.card (powMonoidHom 5 : G →* G).ker := by
      change Nat.card ↑((powMonoidHom 5 : G →* G) ⁻¹' {
          (powMonoidHom 5 : G →* G) a}) = _
      exact Nat.card_congr
        ((powMonoidHom 5 : G →* G).fiberEquivKer a)
    _ = 5 := by
      rw [IsCyclic.card_powMonoidHom_ker, hcard]
      norm_num

/-- A point outside the image of the fifth-power map has an empty fibre. -/
theorem fifthPowerFiber_card_of_not_mem_range
    {G : Type*} [CommGroup G] [Finite G] {c : G}
    (hc : c ∉ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 0 := by
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun u => hc ⟨u, u.property⟩⟩

/-- For a nonzero target in a field, taking fifth roots in the field is
equivalent to taking fifth roots in its unit group.

The only point requiring attention is that a fifth root of a nonzero target
cannot itself be zero. -/
def nonzeroFifthPowerFiberEquivUnits
    {K : Type*} [Field K] {c : K} (hc : c ≠ 0) :
    {r : K // r ^ 5 = c} ≃
      {u : Kˣ // u ^ 5 = Units.mk0 c hc} where
  toFun r := by
    have hr : (r : K) ≠ 0 := by
      intro hr
      apply hc
      rw [← r.property, hr]
      norm_num
    refine ⟨Units.mk0 r hr, ?_⟩
    apply Units.ext
    exact r.property
  invFun u := by
    refine ⟨(u.1 : K), ?_⟩
    have hu := congrArg (↑· : Kˣ → K) u.property
    exact hu
  left_inv r := by
    ext
    rfl
  right_inv u := by
    ext
    rfl

/-- In any field with 81 elements, a nonzero element is a fifth power if
and only if its sixteenth power is one.

This is the semantic criterion implemented by the terminal `F_81` Kummer
fibre table. -/
theorem unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
    {K : Type*} [Field K] [Finite K]
    (hcard : Nat.card K = 81) {c : K} (hc : c ≠ 0) :
    Units.mk0 c hc ∈ (powMonoidHom 5 : Kˣ →* Kˣ).range ↔
      c ^ 16 = 1 := by
  have hcard_units : Nat.card Kˣ = 80 := by
    rw [Nat.card_units, hcard]
  rw [fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty hcard_units,
    MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg (↑· : Kˣ → K) h
  · intro h
    apply Units.ext
    exact h

/-- The complete fifth-power fibre classifier over an 81-element field.

The zero target has the single root zero.  A nonzero target has five roots
when its sixteenth power is one, and no roots otherwise.  This theorem is the
abstract mathematical justification for the executable values `1`, `5`, and
`0` used in the one-dimensional Kummer certificate. -/
theorem fifthPowerFiber_card_field81
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (c : K) :
    Nat.card {r : K // r ^ 5 = c} =
      if c = 0 then 1 else if c ^ 16 = 1 then 5 else 0 := by
  by_cases hc : c = 0
  · subst c
    simp
  · rw [if_neg hc]
    have hcard_units : Nat.card Kˣ = 80 := by
      rw [Nat.card_units, hcard]
    by_cases hpow : c ^ 16 = 1
    · rw [if_pos hpow]
      have hrange :
          Units.mk0 c hc ∈ (powMonoidHom 5 : Kˣ →* Kˣ).range :=
        (unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one hcard hc).2 hpow
      calc
        Nat.card {r : K // r ^ 5 = c} =
            Nat.card {u : Kˣ // u ^ 5 = Units.mk0 c hc} :=
          Nat.card_congr (nonzeroFifthPowerFiberEquivUnits hc)
        _ = 5 := fifthPowerFiber_card_of_mem_range hcard_units hrange
    · rw [if_neg hpow]
      have hrange :
          Units.mk0 c hc ∉ (powMonoidHom 5 : Kˣ →* Kˣ).range := by
        intro hrange
        exact hpow
          ((unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one hcard hc).1 hrange)
      calc
        Nat.card {r : K // r ^ 5 = c} =
            Nat.card {u : Kˣ // u ^ 5 = Units.mk0 c hc} :=
          Nat.card_congr (nonzeroFifthPowerFiberEquivUnits hc)
        _ = 0 := fifthPowerFiber_card_of_not_mem_range hrange

/-- The structural root-count classifier for one Kummer fibre over an
81-element field.

If the coefficient of `r⁵` vanishes, the equation is either inconsistent or
identically zero.  Otherwise the normalized fifth-power target is classified
by `fifthPowerFiber_card_field81`. -/
def canonicalKummerFiberSizeField81
    {K : Type*} [Field K] [DecidableEq K] (e t : K) : Nat :=
  let denominator := canonicalKummerDenominator25Three e t
  let numerator := canonicalKummerNumerator25Three e t
  if denominator = 0 then
    if numerator = 0 then 81 else 0
  else
    let target := -numerator / denominator
    if target = 0 then 1 else if target ^ 16 = 1 then 5 else 0

/-- The structural classifier gives the actual number of roots of the
Kummer polynomial over every 81-element field.

The proof separates the two degenerate constant fibres from the nonzero
coefficient case, where the Kummer equation is transported to `r⁵=c` and
the cyclic-group theorem applies.  No field elements are enumerated. -/
theorem canonicalKummerFiber_card_field81
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (e t : K) :
    Nat.card {r : K // canonicalKummerPolynomial25Three e r t = 0} =
      canonicalKummerFiberSizeField81 e t := by
  by_cases hden : canonicalKummerDenominator25Three e t = 0
  · by_cases hnum : canonicalKummerNumerator25Three e t = 0
    · change Nat.card
          {r : K // r ^ 5 * canonicalKummerDenominator25Three e t +
            canonicalKummerNumerator25Three e t = 0} =
            (if canonicalKummerDenominator25Three e t = 0 then
              if canonicalKummerNumerator25Three e t = 0 then 81 else 0
            else
              let target := -canonicalKummerNumerator25Three e t /
                canonicalKummerDenominator25Three e t
              if target = 0 then 1 else if target ^ 16 = 1 then 5 else 0)
      simpa [hden, hnum] using hcard
    · change Nat.card
          {r : K // r ^ 5 * canonicalKummerDenominator25Three e t +
            canonicalKummerNumerator25Three e t = 0} =
            (if canonicalKummerDenominator25Three e t = 0 then
              if canonicalKummerNumerator25Three e t = 0 then 81 else 0
            else
              let target := -canonicalKummerNumerator25Three e t /
                canonicalKummerDenominator25Three e t
              if target = 0 then 1 else if target ^ 16 = 1 then 5 else 0)
      simp [hden, hnum]
  · have hequiv :
        {r : K // canonicalKummerPolynomial25Three e r t = 0} ≃
          {r : K // r ^ 5 = canonicalKummerTarget25Three e t} :=
      (Equiv.refl K).subtypeEquiv fun r =>
        canonicalKummer_eq_zero_iff_fifthPower_eq_target e t hden
    calc
      Nat.card {r : K // canonicalKummerPolynomial25Three e r t = 0} =
          Nat.card {r : K // r ^ 5 = canonicalKummerTarget25Three e t} :=
        Nat.card_congr hequiv
      _ = if canonicalKummerTarget25Three e t = 0 then 1
          else if (canonicalKummerTarget25Three e t) ^ 16 = 1 then 5 else 0 :=
        fifthPowerFiber_card_field81 hcard (canonicalKummerTarget25Three e t)
      _ = canonicalKummerFiberSizeField81 e t := by
        unfold canonicalKummerTarget25Three canonicalKummerFiberSizeField81
        rw [if_neg hden]

end FifthPowerFibres

end MazurProof.RationalPointsN25QuotientKummerThree
