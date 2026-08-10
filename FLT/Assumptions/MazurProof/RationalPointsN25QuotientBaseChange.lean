import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeil

/-!
# Coordinatewise base change for normalized projective space

The four normalized charts used in the N25 point counts are functorial under
ring homomorphisms.  This file contains only that characteristic-independent
coordinate layer; preservation of the characteristic-two and
characteristic-three curve equations is proved in their respective modules.
-/

namespace MazurProof.RationalPointsN25QuotientBaseChange

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil

/-- Apply a ring homomorphism to four homogeneous coordinates. -/
def Coordinates4.map {K L : Type*} [Semiring K] [Semiring L]
    (f : K →+* L) (P : Coordinates4 K) : Coordinates4 L :=
  ⟨f P.x, f P.y, f P.z, f P.w⟩

/-- Apply a ring homomorphism to the free coordinates in a normalized
projective chart.  Leading zeroes and the leading one remain normalized. -/
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

/-- Coordinatewise maps compose as the underlying ring homomorphisms do. -/
theorem NormalizedProjective4.map_comp
    {K L M : Type*} [Semiring K] [Semiring L] [Semiring M]
    (g : L →+* M) (f : K →+* L) (P : NormalizedProjective4 K) :
    NormalizedProjective4.map g (NormalizedProjective4.map f P) =
      NormalizedProjective4.map (g.comp f) P := by
  cases P <;> rfl

/-- An injective coefficient map is injective on normalized projective
charts because the chart constructor is part of the representative. -/
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

end MazurProof.RationalPointsN25QuotientBaseChange
