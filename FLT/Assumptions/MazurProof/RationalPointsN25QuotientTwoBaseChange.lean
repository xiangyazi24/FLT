import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBaseChange
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBinaryFieldSemantics
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius

/-!
# Base change for the characteristic-two canonical N25 model

The semantic characteristic-two equations use the actual field operations,
not the raw executable tables.  Since all their coefficients lie in the
prime field, a field homomorphism preserves and reflects both equations.
This supplies the curve-specific input needed by the generic Frobenius
descent module.
-/

namespace MazurProof.RationalPointsN25QuotientTwoBaseChange

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientBaseChange
open NormalizedProjectiveCurveFrobenius

/-- Normalized homogeneous coordinates commute with coefficient-field
homomorphisms. -/
theorem coordinates_map_two
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : NormalizedProjective4 K) :
    Coordinates4.map f (normalizedCoordinates25 P) =
      normalizedCoordinates25 (NormalizedProjective4.map f P) := by
  cases P <;>
    simp [Coordinates4.map, normalizedCoordinates25,
      NormalizedProjective4.coordinates, fieldBinaryOperations]

/-- The binary canonical quadric commutes with field homomorphisms. -/
theorem map_canonicalQuadric25Binary
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : Coordinates4 K) :
    f (canonicalQuadric25Binary (fieldBinaryOperations K) P) =
      canonicalQuadric25Binary (fieldBinaryOperations L)
        (Coordinates4.map f P) := by
  simp [canonicalQuadric25Binary, fieldBinaryOperations, Coordinates4.map]

/-- The binary canonical cubic commutes with field homomorphisms. -/
theorem map_canonicalCubic25Binary
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : Coordinates4 K) :
    f (canonicalCubic25Binary (fieldBinaryOperations K) P) =
      canonicalCubic25Binary (fieldBinaryOperations L)
        (Coordinates4.map f P) := by
  simp [canonicalCubic25Binary, fieldBinaryOperations, Coordinates4.map]

/-- A field homomorphism preserves and reflects the two semantic binary
canonical equations.  Reflection uses injectivity of field homomorphisms. -/
theorem isCanonicalNormalizedTwo_map_iff
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : NormalizedProjective4 K) :
    IsCanonicalNormalizedTwo (NormalizedProjective4.map f P) ↔
      IsCanonicalNormalizedTwo P := by
  unfold IsCanonicalNormalizedTwo
  dsimp only
  rw [← coordinates_map_two f P,
    ← map_canonicalQuadric25Binary f,
    ← map_canonicalCubic25Binary f]
  constructor
  · rintro ⟨hQ, hC⟩
    exact ⟨f.injective (hQ.trans (map_zero f).symm),
      f.injective (hC.trans (map_zero f).symm)⟩
  · rintro ⟨hQ, hC⟩
    constructor
    · rw [hQ]
      simp [fieldBinaryOperations]
    · rw [hC]
      simp [fieldBinaryOperations]

/-- A coefficient-field homomorphism embeds semantic binary curve points. -/
def canonicalPointEmbeddingTwo
    {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedTwo P} ↪
      {P : NormalizedProjective4 L // IsCanonicalNormalizedTwo P} where
  toFun P := ⟨NormalizedProjective4.map f P.1,
    (isCanonicalNormalizedTwo_map_iff f P.1).2 P.2⟩
  inj' := fun _ _ hPQ => Subtype.ext <|
    NormalizedProjective4.map_injective f f.injective <|
      congrArg Subtype.val hPQ

/-- A coefficient-field equivalence induces an equivalence of semantic
binary curve-point types. -/
noncomputable def canonicalPointEquivTwo
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedTwo P} ≃
      {P : NormalizedProjective4 L // IsCanonicalNormalizedTwo P} where
  toFun := canonicalPointEmbeddingTwo e.toRingHom
  invFun := canonicalPointEmbeddingTwo e.symm.toRingHom
  left_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;>
        simp [canonicalPointEmbeddingTwo, NormalizedProjective4.map]
  right_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;>
        simp [canonicalPointEmbeddingTwo, NormalizedProjective4.map]

/-- The characteristic-two canonical equations, packaged only with their
coefficient-base-change law for generic Frobenius descent. -/
def canonicalTwoModel : CurveModel where
  IsPoint := fun K _ P => IsCanonicalNormalizedTwo P
  map_iff := by
    intro K L _ _ f P
    exact isCanonicalNormalizedTwo_map_iff f P

end MazurProof.RationalPointsN25QuotientTwoBaseChange
