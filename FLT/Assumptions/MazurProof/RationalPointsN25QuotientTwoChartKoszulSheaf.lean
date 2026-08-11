import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoChartKoszul
import FLT.Mathlib.AlgebraicGeometry.Modules.TildeExact

/-!
# Sheafified Koszul exactness on the standard charts of the N25 curve

The affine calculation in `RationalPointsN25QuotientTwoChartKoszul` gives the
four-term Koszul resolution on each ambient chart `D₊(X i)`.  This file
packages its two overlapping three-term pieces as short complexes of modules
and applies exactness of affine tilde.  The result is exactness of the actual
module-sheaf morphisms on the affine spectrum of every ambient chart ring.

This is the local categorical input for gluing the global ambient projective
Koszul resolution.  It does not identify the affine tilde sheaves with the
already constructed projective twists; that comparison belongs to the next
gluing layer.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoChartKoszulSheaf

open CategoryTheory
open RationalPointsN25QuotientTwoChartKoszul

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ambient standard chart regarded as a bundled commutative ring. -/
abbrev AmbientChartRingCat (i : Fin 4) : CommRingCat :=
  .of (AmbientChartRing i)

set_option synthInstance.maxHeartbeats 100000 in
-- The chart ring is a reducible homogeneous localization, so resolving the
-- inherited additive tilde instance needs a larger synthesis budget.
noncomputable local instance chartTildePreservesZeroMorphisms (i : Fin 4) :
    (AlgebraicGeometry.tilde.functor
      (AmbientChartRingCat i)).PreservesZeroMorphisms :=
  letI : (AlgebraicGeometry.tilde.functor
      (AmbientChartRingCat i)).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive _

/-! ## Module-level short complexes -/

/-- The left three terms of the affine Koszul resolution
`A → A² → A` on `D₊(X i)`. -/
def chartKoszulLeftComplex (i : Fin 4) :
    ShortComplex (ModuleCat (AmbientChartRingCat i)) :=
  ModuleCat.shortComplexOfCompEqZero
    (chartKoszulTop i) (chartKoszulMiddle i) (chartKoszulMiddle_comp_top i)

/-- The quotient projection kills the image of the middle Koszul map. -/
theorem chartQuotientProjection_comp_middle (i : Fin 4) :
    (chartQuotientProjection i).comp (chartKoszulMiddle i) = 0 := by
  apply LinearMap.ext
  intro p
  exact (chartKoszul_exact_middle_projection i (chartKoszulMiddle i p)).2 ⟨p, rfl⟩

/-- The right three terms of the affine Koszul resolution
`A² → A → A/(Q/X_i²,C/X_i³)` on `D₊(X i)`. -/
def chartKoszulRightComplex (i : Fin 4) :
    ShortComplex (ModuleCat (AmbientChartRingCat i)) :=
  ModuleCat.shortComplexOfCompEqZero
    (chartKoszulMiddle i) (chartQuotientProjection i)
      (chartQuotientProjection_comp_middle i)

/-- Exactness of the left module complex is the homogeneous-denominator
Koszul theorem proved uniformly for all four charts. -/
theorem chartKoszulLeftComplex_exact (i : Fin 4) :
    (chartKoszulLeftComplex i).Exact :=
  ModuleCat.shortComplex_exact _ (chartKoszul_exact_top_middle i)

/-- Exactness of the right module complex identifies its cokernel with the
explicit affine curve chart. -/
theorem chartKoszulRightComplex_exact (i : Fin 4) :
    (chartKoszulRightComplex i).Exact :=
  ModuleCat.shortComplex_exact _ (chartKoszul_exact_middle_projection i)

/-! ## Affine module-sheaf complexes -/

/-- The left Koszul short complex after applying affine tilde on the spectrum
of the ambient chart ring.  Its arrows are the sheaf morphisms induced by
multiplication by `(C/X_i³,-Q/X_i²)` and `(Q/X_i²,C/X_i³)`. -/
abbrev chartKoszulLeftSheafComplex (i : Fin 4) :=
  (chartKoszulLeftComplex i).map
    (AlgebraicGeometry.tilde.functor (AmbientChartRingCat i))

/-- The right Koszul short complex after applying affine tilde.  Its last
arrow is the sheaf morphism induced by the explicit quotient projection. -/
abbrev chartKoszulRightSheafComplex (i : Fin 4) :=
  (chartKoszulRightComplex i).map
    (AlgebraicGeometry.tilde.functor (AmbientChartRingCat i))

/-- The sheafified left Koszul complex is exact on every ambient standard
chart because stalks of affine tilde are module localizations. -/
theorem chartKoszulLeftSheafComplex_exact (i : Fin 4) :
    (chartKoszulLeftSheafComplex i).Exact :=
  AlgebraicGeometry.tilde_map_exact _ _ (chartKoszulLeftComplex_exact i)

/-- The sheafified right Koszul complex is exact on every ambient standard
chart, including exactness at the structure sheaf immediately before the
curve-chart quotient sheaf. -/
theorem chartKoszulRightSheafComplex_exact (i : Fin 4) :
    (chartKoszulRightSheafComplex i).Exact :=
  AlgebraicGeometry.tilde_map_exact _ _ (chartKoszulRightComplex_exact i)

end MazurProof.RationalPointsN25QuotientTwoChartKoszulSheaf
