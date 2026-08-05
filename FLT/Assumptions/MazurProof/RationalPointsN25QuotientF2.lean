import FLT.Assumptions.MazurProof.RationalPointsN25CanonicalPoints

/-!
# Finite-field points on the level-25 genus-four quotient

This file gives kernel-checked finite certificates for the canonical model of
the quotient labelled `25.150.4.f.1`.  Its equations are the quadric and cubic
used in `RationalPointsN25CanonicalPoints`.

Over `F_2`, the complete intersection has exactly five projective points, the
reductions of the five rational cusps.  Over `F_4 = F_2[alpha]/(alpha^2 +
alpha + 1)`, it has no new projective class: every `F_4` point is projectively
equal to one of those five `F_2` points.  The latter is the finite-field
certificate that there is no closed point of degree two on this model.

All finite checks below use ordinary kernel reduction through `by decide`.
There is no `native_decide` or external computation in the proof term.
-/

namespace MazurProof.RationalPointsN25QuotientF2

-- `Mathlib` disables the finite-universal decision instance in one imported
-- combinatorics module.  Re-enable both finite quantifier instances locally;
-- they are precisely the kernel enumeration mechanism used in this file.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- Four homogeneous coordinates over a coefficient type. -/
structure Coordinates4 (R : Type*) where
  x : R
  y : R
  z : R
  w : R
deriving DecidableEq, Fintype

/-- The canonical quadric over an arbitrary commutative ring.  This shared
formula is specialized below to the finite fields. -/
def canonicalQuadric25Over {R : Type*} [CommRing R] (P : Coordinates4 R) : R :=
  -P.x * P.z - P.x * P.w + P.y ^ 2 + P.y * P.z + P.z * P.w

/-- The canonical cubic over an arbitrary commutative ring. -/
def canonicalCubic25Over {R : Type*} [CommRing R] (P : Coordinates4 R) : R :=
  P.x ^ 2 * P.w + P.x * P.y * P.z - P.x * P.y * P.w -
    P.x * P.z * P.w + P.y * P.z * P.w + P.z ^ 2 * P.w -
    P.z * P.w ^ 2

/-- The generic quadric specializes definitionally to the imported rational
canonical model. -/
theorem canonicalQuadric25Over_rat_eq_source :
    ∀ P : Coordinates4 ℚ,
      canonicalQuadric25Over P =
        RationalPointsN25CanonicalPoints.canonicalQuadric25 P.x P.y P.z P.w := by
  intro P
  rfl

/-- The generic cubic specializes definitionally to the imported rational
canonical model. -/
theorem canonicalCubic25Over_rat_eq_source :
    ∀ P : Coordinates4 ℚ,
      canonicalCubic25Over P =
        RationalPointsN25CanonicalPoints.canonicalCubic25 P.x P.y P.z P.w := by
  intro P
  rfl

/-! ## The special fibre over `F_2` -/

/-- The prime field used for the special fibre. -/
abbrev F2 := ZMod 2

/-- The zero homogeneous vector over `F_2`. -/
def zeroCoordinatesF2 : Coordinates4 F2 :=
  ⟨0, 0, 0, 0⟩

/-- Scalar multiplication of homogeneous coordinates over `F_2`. -/
def scaleF2 (a : F2) (P : Coordinates4 F2) : Coordinates4 F2 :=
  ⟨a * P.x, a * P.y, a * P.z, a * P.w⟩

/-- Projective equivalence of nonzero coordinate vectors over `F_2`. -/
def ProjectivelyEqual4F2 (P Q : Coordinates4 F2) : Prop :=
  ∃ a : F2, a ≠ 0 ∧ P = scaleF2 a Q

private instance decidableProjectivelyEqual4F2 (P Q : Coordinates4 F2) :
    Decidable (ProjectivelyEqual4F2 P Q) := by
  unfold ProjectivelyEqual4F2
  infer_instance

/-- Reduction modulo two of the canonical quadric
`-xz - xw + y^2 + yz + zw`. -/
def canonicalQuadric25F2 (P : Coordinates4 F2) : F2 :=
  canonicalQuadric25Over P

/-- Reduction modulo two of the canonical cubic
`x^2w + xyz - xyw - xzw + yzw + z^2w - zw^2`. -/
def canonicalCubic25F2 (P : Coordinates4 F2) : F2 :=
  canonicalCubic25Over P

/-- A nonzero homogeneous vector satisfying the two canonical equations over
`F_2`. -/
def IsCanonicalPoint25F2 (P : Coordinates4 F2) : Prop :=
  P ≠ zeroCoordinatesF2 ∧
    canonicalQuadric25F2 P = 0 ∧ canonicalCubic25F2 P = 0

private instance decidableIsCanonicalPoint25F2 :
    DecidablePred IsCanonicalPoint25F2 := fun P => by
  unfold IsCanonicalPoint25F2
  infer_instance

/-- The five integral cusp vectors reduced modulo two. -/
def cusp0001F2 : Coordinates4 F2 := ⟨0, 0, 0, 1⟩
def cusp0m110F2 : Coordinates4 F2 := ⟨0, -1, 1, 0⟩
def cusp1101F2 : Coordinates4 F2 := ⟨1, 1, 0, 1⟩
def cusp0010F2 : Coordinates4 F2 := ⟨0, 0, 1, 0⟩
def cusp1000F2 : Coordinates4 F2 := ⟨1, 0, 0, 0⟩

/-- Projective membership in one of the five reduced cusp classes. -/
def IsCanonicalCusp25F2 (P : Coordinates4 F2) : Prop :=
  ProjectivelyEqual4F2 P cusp0001F2 ∨
  ProjectivelyEqual4F2 P cusp0m110F2 ∨
  ProjectivelyEqual4F2 P cusp1101F2 ∨
  ProjectivelyEqual4F2 P cusp0010F2 ∨
  ProjectivelyEqual4F2 P cusp1000F2

private instance decidableIsCanonicalCusp25F2 :
    DecidablePred IsCanonicalCusp25F2 := fun P => by
  unfold IsCanonicalCusp25F2 ProjectivelyEqual4F2
  infer_instance

/-- Over `F_2`, projective equivalence is just equality because the only
nonzero scalar is one. -/
theorem projectivelyEqual4F2_iff_eq :
    ∀ P Q : Coordinates4 F2, ProjectivelyEqual4F2 P Q ↔ P = Q := by
  decide

/-- Kernel-checked exhaustive classification of the special fibre: its
projective points are exactly the five reduced rational cusps. -/
theorem canonical_point25F2_iff_cusp :
    ∀ P : Coordinates4 F2, IsCanonicalPoint25F2 P ↔ IsCanonicalCusp25F2 P := by
  decide

/-- The finite set of nonzero coordinate representatives on the special
fibre.  Over `F_2` each projective class has a unique representative. -/
def canonicalPoints25F2 : Finset (Coordinates4 F2) :=
  Finset.univ.filter IsCanonicalPoint25F2

/-- There are exactly five `F_2`-projective points. -/
theorem canonicalPoints25F2_card : canonicalPoints25F2.card = 5 := by
  decide

/-! ## The quadratic extension `F_4` -/

/-- A computational presentation of
`F_4 = F_2[alpha]/(alpha^2 + alpha + 1)`.  The pair `(a,b)` represents
`a + b*alpha`. -/
abbrev F4 := F2 × F2

def f4Zero : F4 := (0, 0)
def f4One : F4 := (1, 0)

def f4Add (a b : F4) : F4 :=
  (a.1 + b.1, a.2 + b.2)

def f4Neg (a : F4) : F4 :=
  (-a.1, -a.2)

/-- Multiplication in the basis `1, alpha`, using `alpha^2 = alpha + 1` in
characteristic two. -/
def f4Mul (a b : F4) : F4 :=
  (a.1 * b.1 + a.2 * b.2,
    a.1 * b.2 + a.2 * b.1 + a.2 * b.2)

def f4Sub (a b : F4) : F4 :=
  f4Add a (f4Neg b)

def f4Sq (a : F4) : F4 :=
  f4Mul a a

/-- In the multiplicative group of order three, inversion is squaring. -/
def f4Inv (a : F4) : F4 :=
  f4Sq a

/-- The computational presentation has the required inverse law for every
nonzero element. -/
theorem f4_mul_inv_of_ne_zero :
    ∀ a : F4, a ≠ f4Zero → f4Mul a (f4Inv a) = f4One := by
  decide

/-- The natural embedding of the prime field into the quadratic extension. -/
def embedF2F4 (a : F2) : F4 :=
  (a, 0)

/-- Coordinatewise embedding of an `F_2` homogeneous vector. -/
def embedCoordinatesF2F4 (P : Coordinates4 F2) : Coordinates4 F4 :=
  ⟨embedF2F4 P.x, embedF2F4 P.y, embedF2F4 P.z, embedF2F4 P.w⟩

/-- Scalar multiplication of homogeneous coordinates over `F_4`. -/
def scaleF4 (a : F4) (P : Coordinates4 F4) : Coordinates4 F4 :=
  ⟨f4Mul a P.x, f4Mul a P.y, f4Mul a P.z, f4Mul a P.w⟩

/-- Projective equivalence over the computational presentation of `F_4`. -/
def ProjectivelyEqual4F4 (P Q : Coordinates4 F4) : Prop :=
  ∃ a : F4, a ≠ f4Zero ∧ P = scaleF4 a Q

private instance decidableProjectivelyEqual4F4 (P Q : Coordinates4 F4) :
    Decidable (ProjectivelyEqual4F4 P Q) := by
  unfold ProjectivelyEqual4F4
  infer_instance

/-- The canonical quadric over `F_4`. -/
def canonicalQuadric25F4 (P : Coordinates4 F4) : F4 :=
  f4Add
    (f4Add
      (f4Add (f4Sub f4Zero (f4Mul P.x P.z))
        (f4Sub f4Zero (f4Mul P.x P.w)))
      (f4Sq P.y))
    (f4Add (f4Mul P.y P.z) (f4Mul P.z P.w))

/-- The canonical cubic over `F_4`. -/
def canonicalCubic25F4 (P : Coordinates4 F4) : F4 :=
  f4Add
    (f4Add
      (f4Add
        (f4Add
          (f4Add
            (f4Add (f4Mul (f4Sq P.x) P.w)
              (f4Mul (f4Mul P.x P.y) P.z))
            (f4Neg (f4Mul (f4Mul P.x P.y) P.w)))
          (f4Neg (f4Mul (f4Mul P.x P.z) P.w)))
        (f4Mul (f4Mul P.y P.z) P.w))
      (f4Mul (f4Sq P.z) P.w))
    (f4Neg (f4Mul P.z (f4Sq P.w)))

/-- A nonzero homogeneous vector satisfying the canonical equations over
`F_4`. -/
def IsCanonicalPoint25F4 (P : Coordinates4 F4) : Prop :=
  P ≠ ⟨f4Zero, f4Zero, f4Zero, f4Zero⟩ ∧
    canonicalQuadric25F4 P = f4Zero ∧ canonicalCubic25F4 P = f4Zero

private instance decidableIsCanonicalPoint25F4 :
    DecidablePred IsCanonicalPoint25F4 := fun P => by
  unfold IsCanonicalPoint25F4
  infer_instance

/-- The five `F_2` cusp vectors viewed over `F_4`. -/
def IsCanonicalCusp25F4 (P : Coordinates4 F4) : Prop :=
  ProjectivelyEqual4F4 P (embedCoordinatesF2F4 cusp0001F2) ∨
  ProjectivelyEqual4F4 P (embedCoordinatesF2F4 cusp0m110F2) ∨
  ProjectivelyEqual4F4 P (embedCoordinatesF2F4 cusp1101F2) ∨
  ProjectivelyEqual4F4 P (embedCoordinatesF2F4 cusp0010F2) ∨
  ProjectivelyEqual4F4 P (embedCoordinatesF2F4 cusp1000F2)

private instance decidableIsCanonicalCusp25F4 :
    DecidablePred IsCanonicalCusp25F4 := fun P => by
  unfold IsCanonicalCusp25F4 ProjectivelyEqual4F4
  infer_instance

/-- The `F_4` equations restrict to the `F_2` equations under the natural
embedding. -/
theorem canonical_equations_embed_f2 :
    ∀ P : Coordinates4 F2,
      canonicalQuadric25F4 (embedCoordinatesF2F4 P) =
          embedF2F4 (canonicalQuadric25F2 P) ∧
        canonicalCubic25F4 (embedCoordinatesF2F4 P) =
          embedF2F4 (canonicalCubic25F2 P) := by
  decide

/-- Kernel-checked exhaustive classification over the quadratic extension:
there are no projective classes beyond the five classes already defined over
`F_2`. -/
theorem canonical_point25F4_iff_cusp :
    ∀ P : Coordinates4 F4, IsCanonicalPoint25F4 P ↔ IsCanonicalCusp25F4 P := by
  set_option maxRecDepth 100000 in
    decide

/-- Every point over `F_4` descends projectively to an `F_2` point on the same
canonical model. -/
theorem canonical_point25F4_descends_to_f2 :
    ∀ P : Coordinates4 F4, IsCanonicalPoint25F4 P →
      ∃ Q : Coordinates4 F2,
        IsCanonicalPoint25F2 Q ∧
          ProjectivelyEqual4F4 P (embedCoordinatesF2F4 Q) := by
  set_option maxRecDepth 100000 in
    decide

/-- Finite-field degree-two certificate: the canonical model has no
projective point over `F_4` whose class fails to descend to `F_2`. -/
theorem no_new_projective_class_over_f4 :
    ¬ ∃ P : Coordinates4 F4,
      IsCanonicalPoint25F4 P ∧
        ¬ ∃ Q : Coordinates4 F2,
          IsCanonicalPoint25F2 Q ∧
            ProjectivelyEqual4F4 P (embedCoordinatesF2F4 Q) := by
  intro h
  obtain ⟨P, hP, hnew⟩ := h
  exact hnew (canonical_point25F4_descends_to_f2 P hP)

end MazurProof.RationalPointsN25QuotientF2
