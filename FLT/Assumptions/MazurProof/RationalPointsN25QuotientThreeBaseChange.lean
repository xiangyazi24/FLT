import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBaseChange
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThreeProjective
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius

/-!
# Base change for the characteristic-three canonical model

The normalized projective charts used by the N25 point count are functorial
under field homomorphisms: apply the homomorphism to every free chart
coordinate and leave the leading zeroes and one unchanged.  Because the
canonical quadric and cubic have integral coefficients, this coordinate map
preserves both equations.

This file records that structural fact independently of any finite-field
enumeration.  In particular, later Frobenius arguments can transport actual
curve points between finite fields without replacing geometry by a
cardinality coincidence.
-/

namespace MazurProof.RationalPointsN25QuotientThreeBaseChange

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientKummerThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientBaseChange
open NormalizedProjectiveCurveFrobenius

/-! ## Preservation of the canonical equations -/

/-- Homogeneous coordinates commute with coordinatewise base change. -/
theorem coordinates_map
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : NormalizedProjective4 K) :
    Coordinates4.map f (normalizedCoordinatesThree P) =
      normalizedCoordinatesThree (NormalizedProjective4.map f P) := by
  cases P <;> simp [Coordinates4.map, normalizedCoordinatesThree]

/-- The canonical quadric is defined over the prime ring and hence commutes
with every field homomorphism. -/
theorem map_canonicalQuadric25Three
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : Coordinates4 K) :
    f (canonicalQuadric25Three P) =
      canonicalQuadric25Three (Coordinates4.map f P) := by
  simp [canonicalQuadric25Three, Coordinates4.map]

/-- The canonical cubic is defined over the prime ring and hence commutes
with every field homomorphism. -/
theorem map_canonicalCubic25Three
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : Coordinates4 K) :
    f (canonicalCubic25Three P) =
      canonicalCubic25Three (Coordinates4.map f P) := by
  simp [canonicalCubic25Three, Coordinates4.map]

/-- A field homomorphism preserves and reflects the two canonical equations.
Reflection uses injectivity of a homomorphism between fields, rather than a
finite-cardinality argument. -/
theorem isCanonicalNormalizedThree_map_iff
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P : NormalizedProjective4 K) :
    IsCanonicalNormalizedThree (NormalizedProjective4.map f P) ↔
      IsCanonicalNormalizedThree P := by
  unfold IsCanonicalNormalizedThree
  rw [← coordinates_map f P, ← map_canonicalQuadric25Three,
    ← map_canonicalCubic25Three]
  constructor
  · rintro ⟨hQ, hC⟩
    exact ⟨f.injective (hQ.trans (map_zero f).symm),
      f.injective (hC.trans (map_zero f).symm)⟩
  · rintro ⟨hQ, hC⟩
    simp [hQ, hC]

/-- A coefficient-field homomorphism embeds the corresponding semantic
curve-point type. -/
def canonicalPointEmbedding
    {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} ↪
      {P : NormalizedProjective4 L // IsCanonicalNormalizedThree P} where
  toFun P :=
    ⟨NormalizedProjective4.map f P.1,
      (isCanonicalNormalizedThree_map_iff f P.1).2 P.2⟩
  inj' := fun _ _ hPQ => Subtype.ext <|
    NormalizedProjective4.map_injective f f.injective <| congrArg Subtype.val hPQ

/-- A coefficient-field equivalence induces an equivalence of the semantic
curve-point types. -/
noncomputable def canonicalPointEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} ≃
      {P : NormalizedProjective4 L // IsCanonicalNormalizedThree P} where
  toFun := canonicalPointEmbedding e.toRingHom
  invFun := canonicalPointEmbedding e.symm.toRingHom
  left_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;> simp [canonicalPointEmbedding, NormalizedProjective4.map]
  right_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;> simp [canonicalPointEmbedding, NormalizedProjective4.map]

/-- The characteristic-three canonical equations, packaged only with their
coefficient-base-change law for generic Frobenius descent. -/
def canonicalThreeModel : CurveModel where
  IsPoint := fun K _ P => IsCanonicalNormalizedThree P
  map_iff := by
    intro K L _ _ f P
    exact isCanonicalNormalizedThree_map_iff f P

end MazurProof.RationalPointsN25QuotientThreeBaseChange
