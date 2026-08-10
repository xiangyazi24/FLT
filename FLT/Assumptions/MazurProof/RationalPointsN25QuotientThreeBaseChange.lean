import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThreeProjective

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

/-! ## Coordinatewise maps -/

/-- Apply a ring homomorphism to four homogeneous coordinates. -/
def Coordinates4.map {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (P : Coordinates4 K) : Coordinates4 L :=
  ⟨f P.x, f P.y, f P.z, f P.w⟩

/-- Apply a ring homomorphism to the free coordinates in a normalized
projective chart.  Its leading zeroes and leading one are preserved by the
homomorphism, so the result is already normalized. -/
def NormalizedProjective4.map {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) : NormalizedProjective4 K → NormalizedProjective4 L
  | .xChart y z w => .xChart (f y) (f z) (f w)
  | .yChart z w => .yChart (f z) (f w)
  | .zChart w => .zChart (f w)
  | .wChart => .wChart

@[simp]
theorem NormalizedProjective4.map_xChart
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (y z w : K) :
    NormalizedProjective4.map f (.xChart y z w) =
      .xChart (f y) (f z) (f w) := rfl

@[simp]
theorem NormalizedProjective4.map_yChart
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (z w : K) :
    NormalizedProjective4.map f (.yChart z w) = .yChart (f z) (f w) := rfl

@[simp]
theorem NormalizedProjective4.map_zChart
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (w : K) :
    NormalizedProjective4.map f (.zChart w) = .zChart (f w) := rfl

@[simp]
theorem NormalizedProjective4.map_wChart
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) :
    NormalizedProjective4.map f (.wChart : NormalizedProjective4 K) =
      (.wChart : NormalizedProjective4 L) := rfl

/-- Mapping by the identity homomorphism does not change a normalized
projective point. -/
@[simp]
theorem NormalizedProjective4.map_id
    {K : Type*} [Semiring K] (P : NormalizedProjective4 K) :
    NormalizedProjective4.map (RingHom.id K) P = P := by
  cases P <;> rfl

/-- Coordinatewise maps compose exactly as the underlying ring
homomorphisms compose. -/
theorem NormalizedProjective4.map_comp
    {K L M : Type*} [Semiring K] [Semiring L] [Semiring M]
    (g : L →+* M) (f : K →+* L) (P : NormalizedProjective4 K) :
    NormalizedProjective4.map g (NormalizedProjective4.map f P) =
      NormalizedProjective4.map (g.comp f) P := by
  cases P <;> rfl

/-- An injective coefficient map remains injective on normalized projective
charts because the chart constructor is part of the canonical
representative. -/
theorem NormalizedProjective4.map_injective
    {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (NormalizedProjective4.map f) := by
  intro P Q hPQ
  cases P <;> cases Q <;>
    simp_all only [NormalizedProjective4.map,
      NormalizedProjective4.xChart.injEq,
      NormalizedProjective4.yChart.injEq,
      NormalizedProjective4.zChart.injEq,
      hf.eq_iff, reduceCtorEq]

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

end MazurProof.RationalPointsN25QuotientThreeBaseChange
