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
cyclotomic polynomial in characteristic three, applied after the Segre map.

The four returned entries are the original canonical coordinates
`(x,y,z,w)`.  Avoiding projective normalization here keeps the algebraic
change of variables homogeneous and denominator-free. -/
def canonicalSegreCoordinates25Three (e a b c d : K) : Coordinates4 K :=
  let u₁ := a * c
  let u₂ := a * d
  let u₃ := b * c
  let u₄ := b * d
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

/-- The inverse eigenbasis sends every Segre point to the canonical quadric.
The proof is a polynomial consequence of the fifth-cyclotomic relation and
the characteristic-three identity `3=0`; no finite field is enumerated. -/
theorem canonicalQuadric25_segre_eq_zero {e a b c d : K}
    (he : IsCyclotomicFive25Three e) :
    let P := canonicalSegreCoordinates25Three e a b c d
    canonicalQuadric25Three P = 0 := by
  unfold IsCyclotomicFive25Three at he
  have he₄ : e ^ 4 = -e ^ 3 - e ^ 2 - e - 1 := by
    linear_combination he
  have he₅ : e ^ 5 = 1 := by
    apply sub_eq_zero.mp
    calc
      e ^ 5 - 1 = (e - 1) * (e ^ 4 + e ^ 3 + e ^ 2 + e + 1) := by ring
      _ = 0 := by rw [he]; ring
  have he₆ : e ^ 6 = e := by rw [show e ^ 6 = e ^ 5 * e by ring, he₅, one_mul]
  simp only [canonicalSegreCoordinates25Three, canonicalQuadric25Three]
  ring_nf
  simp only [he₆, he₅, he₄]
  ring_nf
  linear_combination
    (-2 * e ^ 3 * a ^ 2 * c ^ 2 - e ^ 3 * a * b * c ^ 2 -
      3 * e ^ 3 * a * b * c * d - 2 * e ^ 3 * b ^ 2 * d ^ 2 -
      3 * e ^ 2 * a ^ 2 * c ^ 2 - 7 * e ^ 2 * a * b * c ^ 2 -
      2 * e ^ 2 * b ^ 2 * c ^ 2 - 5 * e ^ 2 * a ^ 2 * c * d -
      7 * e ^ 2 * a * b * c * d - 6 * e ^ 2 * b ^ 2 * c * d +
      e ^ 2 * a ^ 2 * d ^ 2 - 2 * e ^ 2 * a * b * d ^ 2 -
      3 * e ^ 2 * b ^ 2 * d ^ 2 - e * a ^ 2 * c ^ 2 -
      7 * e * a * b * c ^ 2 - 3 * e * b ^ 2 * c ^ 2 -
      e * a ^ 2 * c * d - 8 * e * a * b * c * d -
      8 * e * b ^ 2 * c * d - 5 * e * a * b * d ^ 2 -
      4 * e * b ^ 2 * d ^ 2 - a ^ 2 * c ^ 2 - 3 * a * b * c ^ 2 -
      3 * b ^ 2 * c ^ 2 - 2 * a * b * c * d - 5 * b ^ 2 * c * d +
      a ^ 2 * d ^ 2 - b ^ 2 * d ^ 2) * CharP.cast_eq_zero K 3

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
  simp only [canonicalSegreCoordinates25Three, canonicalCubic25Three,
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

end MazurProof.RationalPointsN25QuotientKummerThree
