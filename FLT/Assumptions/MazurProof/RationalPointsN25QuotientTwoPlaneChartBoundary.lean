import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartLocalization
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The boundary of the N25 plane projection

The inverse projection from the canonical `w = 1` chart to the integral
plane sextic is defined away from `D = xz + x + z`.  This file analyzes the
complementary closed fibre `D = 0`.  Three explicit polynomial certificates
reduce its coordinates to

* `x = z^3 + z^2`,
* `y^2 + yz = 0`, and
* `z^4 + z^2 + z = 0`.

Rather than enumerating the resulting eight standard monomials, we realize
the boundary as a quotient of a tower of two monic `AdjoinRoot` extensions.
This proves structurally that the boundary coordinate ring is finite over
`F_2`, the zero-dimensional input needed to control components missed by the
principal-open plane equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartBoundary

open Polynomial
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoPlaneChartLocalization
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientSmoothF2

private abbrev k := ZMod 2
private abbrev W := ChartQuotient 3

/-! ## The closed fibre `D = 0` -/

/-- The principal projection denominator cuts out the part of the canonical
chart not seen by the plane-chart localization equivalence. -/
def canonicalWChartBoundaryIdeal : Ideal W :=
  Ideal.span {canonicalWChartProjectionDenominator}

/-- The coordinate ring of the boundary `D = 0` inside the canonical
`w = 1` chart. -/
abbrev CanonicalWChartBoundary :=
  W ⧸ canonicalWChartBoundaryIdeal

/-- The quotient map from the canonical chart to its projection boundary. -/
def canonicalWChartToBoundary : W →+* CanonicalWChartBoundary :=
  algebraMap W CanonicalWChartBoundary

/-- The three universal coordinates on the boundary fibre. -/
def boundaryX : CanonicalWChartBoundary :=
  canonicalWChartToBoundary canonicalWChartX

def boundaryY : CanonicalWChartBoundary :=
  canonicalWChartToBoundary canonicalWChartY

def boundaryZ : CanonicalWChartBoundary :=
  canonicalWChartToBoundary canonicalWChartZ

/-- The boundary quotient remains an `F_2`-algebra, so two vanishes even if
the quotient has not yet been shown nontrivial. -/
theorem boundary_two_eq_zero : (2 : CanonicalWChartBoundary) = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h := congrArg (algebraMap k CanonicalWChartBoundary) htwo
  simpa only [map_ofNat, map_zero] using h

/-- The projection denominator is zero in the boundary quotient by
construction. -/
theorem boundary_denominator_zero :
    projectionDenominator boundaryX boundaryZ = 0 := by
  change canonicalWChartToBoundary
      canonicalWChartProjectionDenominator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))

/-- The canonical quadric restricts on the boundary to `y^2 + yz = 0`. -/
theorem boundary_quadric_zero :
    projectionDenominator boundaryX boundaryZ +
        boundaryY ^ 2 + boundaryY * boundaryZ = 0 := by
  have hq :
      projectionDenominator canonicalWChartX canonicalWChartZ +
          canonicalWChartY ^ 2 + canonicalWChartY * canonicalWChartZ = 0 := by
    have h := chartQuotientPoint_quadric 3
    change canonicalQuadric25CharTwo canonicalWChartPoint = 0 at h
    rw [← wChartPoint_eq_canonicalWChartPoint,
      canonicalQuadric_wChart] at h
    exact h
  have h := congrArg canonicalWChartToBoundary hq
  simpa [projectionDenominator, boundaryX, boundaryY, boundaryZ] using h

/-- The canonical cubic restricts to the numerator relation `yD + N = 0`
before setting `D` to zero. -/
theorem boundary_cubic_zero :
    boundaryY * projectionDenominator boundaryX boundaryZ +
        projectionNumerator boundaryX boundaryZ = 0 := by
  have hc :
      canonicalWChartY *
          projectionDenominator canonicalWChartX canonicalWChartZ +
        projectionNumerator canonicalWChartX canonicalWChartZ = 0 := by
    have h := chartQuotientPoint_cubic 3
    change canonicalCubic25CharTwo canonicalWChartPoint = 0 at h
    rw [← wChartPoint_eq_canonicalWChartPoint,
      canonicalCubic_wChart] at h
    exact h
  have h := congrArg canonicalWChartToBoundary hc
  simpa [projectionDenominator, projectionNumerator, boundaryX, boundaryY,
    boundaryZ] using h

/-! ## Explicit boundary elimination certificates -/

/-- On the boundary, the `x` coordinate is reconstructed polynomially from
`z`.  The proof is the first checked lexicographic Groebner certificate,
expanded as an identity over the integers and then specialized to
characteristic two. -/
theorem boundary_x_relation :
    boundaryX + boundaryZ ^ 3 + boundaryZ ^ 2 = 0 := by
  have hD := boundary_denominator_zero
  have hC := boundary_cubic_zero
  simp only [projectionDenominator, projectionNumerator] at hD hC
  linear_combination
    (1 + boundaryZ + boundaryY + boundaryY * boundaryZ + boundaryX) *
        hD +
      (1 + boundaryZ) * hC -
      (boundaryX ^ 2 * boundaryZ + boundaryX ^ 2 +
        boundaryX * boundaryY * boundaryZ ^ 2 +
        2 * boundaryX * boundaryY * boundaryZ + boundaryX * boundaryY +
        boundaryX * boundaryZ ^ 2 + 2 * boundaryX * boundaryZ +
        boundaryY * boundaryZ ^ 2 + boundaryY * boundaryZ +
        boundaryZ ^ 2 + boundaryZ) * boundary_two_eq_zero

/-- The quadric and `D = 0` leave the monic quadratic relation
`y^2 + yz = 0`. -/
theorem boundary_y_relation :
    boundaryY ^ 2 + boundaryY * boundaryZ = 0 := by
  have hD := boundary_denominator_zero
  have hQ := boundary_quadric_zero
  simp only [projectionDenominator] at hD hQ
  linear_combination hD + hQ -
    (boundaryX * boundaryZ + boundaryX + boundaryZ) *
      boundary_two_eq_zero

/-- Eliminating `x` from the cubic on the boundary leaves the monic quartic
`z^4 + z^2 + z`.  This is the third checked lexicographic Groebner
certificate, again recorded as an integral identity. -/
theorem boundary_z_relation :
    boundaryZ ^ 4 + boundaryZ ^ 2 + boundaryZ = 0 := by
  have hD := boundary_denominator_zero
  have hC := boundary_cubic_zero
  simp only [projectionDenominator, projectionNumerator] at hD hC
  linear_combination
    (boundaryZ ^ 2 + boundaryY + boundaryY * boundaryZ ^ 2 +
        boundaryX + boundaryX * boundaryZ) * hD +
      (1 + boundaryZ ^ 2) * hC -
      (boundaryX ^ 2 * boundaryZ ^ 2 +
        boundaryX ^ 2 * boundaryZ + boundaryX ^ 2 +
        boundaryX * boundaryY * boundaryZ ^ 3 +
        boundaryX * boundaryY * boundaryZ ^ 2 +
        boundaryX * boundaryY * boundaryZ + boundaryX * boundaryY +
        boundaryX * boundaryZ ^ 3 + boundaryX * boundaryZ ^ 2 +
        boundaryX * boundaryZ + boundaryY * boundaryZ ^ 3 +
        boundaryY * boundaryZ + boundaryZ ^ 3) * boundary_two_eq_zero

/-- In characteristic two, the first boundary relation has the usual solved
form `x = z^3 + z^2`. -/
theorem boundary_x_eq_z :
    boundaryX = boundaryZ ^ 3 + boundaryZ ^ 2 := by
  linear_combination boundary_x_relation -
    (boundaryZ ^ 3 + boundaryZ ^ 2) * boundary_two_eq_zero

/-! ## A finite monic tower covering the boundary -/

/-- The monic quartic satisfied by the boundary `z` coordinate. -/
def boundaryZPolynomial : k[X] := X ^ 4 + X ^ 2 + X

/-- The quartic boundary polynomial is monic, so adjoining one of its roots
is finite free over `F_2`. -/
theorem boundaryZPolynomial_monic : boundaryZPolynomial.Monic := by
  unfold boundaryZPolynomial
  monicity!

/-- The first stage of the boundary model adjoins the algebraic `z`
coordinate. -/
abbrev BoundaryZAlgebra := AdjoinRoot boundaryZPolynomial

noncomputable instance boundaryZAlgebra_finite :
    Module.Finite k BoundaryZAlgebra :=
  boundaryZPolynomial_monic.finite_adjoinRoot

/-- Evaluation of the quartic at the actual boundary coordinate vanishes. -/
theorem boundaryZPolynomial_eval :
    boundaryZPolynomial.eval₂
        (Algebra.ofId k CanonicalWChartBoundary) boundaryZ = 0 := by
  simpa [boundaryZPolynomial, Algebra.ofId_apply] using boundary_z_relation

/-- The universal quartic root maps to the actual boundary coordinate `z`. -/
def boundaryZToBoundary : BoundaryZAlgebra →ₐ[k] CanonicalWChartBoundary :=
  AdjoinRoot.liftAlgHom (S := k) boundaryZPolynomial
    (Algebra.ofId k CanonicalWChartBoundary) boundaryZ
    boundaryZPolynomial_eval

@[simp]
theorem boundaryZToBoundary_root :
    boundaryZToBoundary (AdjoinRoot.root boundaryZPolynomial) = boundaryZ := by
  exact AdjoinRoot.liftAlgHom_root boundaryZPolynomial
    (Algebra.ofId k CanonicalWChartBoundary) boundaryZ
    boundaryZPolynomial_eval

/-- Over the quartic `z`-algebra, the boundary `y` coordinate satisfies the
monic quadratic `Y^2 + zY`. -/
def boundaryYPolynomial : BoundaryZAlgebra[X] :=
  X ^ 2 + C (AdjoinRoot.root boundaryZPolynomial) * X

/-- The quadratic relation is monic independently of whether the quartic
root is reduced. -/
theorem boundaryYPolynomial_monic : boundaryYPolynomial.Monic := by
  unfold boundaryYPolynomial
  monicity!

/-- The full finite tower adjoins the boundary `y` coordinate after `z`. -/
abbrev BoundaryZYAlgebra := AdjoinRoot boundaryYPolynomial

noncomputable instance boundaryZYAlgebra_finite_over_z :
    Module.Finite BoundaryZAlgebra BoundaryZYAlgebra :=
  boundaryYPolynomial_monic.finite_adjoinRoot

noncomputable instance boundaryZYAlgebra_finite :
    Module.Finite k BoundaryZYAlgebra :=
  Module.Finite.trans BoundaryZAlgebra BoundaryZYAlgebra

/-- The quadratic root relation holds after mapping the quartic root to the
actual boundary coordinate. -/
theorem boundaryYPolynomial_eval :
    boundaryYPolynomial.eval₂ boundaryZToBoundary boundaryY = 0 := by
  rw [show boundaryYPolynomial =
      X ^ 2 + C (AdjoinRoot.root boundaryZPolynomial) * X by rfl]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
  calc
    boundaryY ^ 2 + boundaryZToBoundary
          (AdjoinRoot.root boundaryZPolynomial) * boundaryY =
        boundaryY ^ 2 + boundaryZ * boundaryY := by
      congr 2
      exact boundaryZToBoundary_root
    _ = boundaryY ^ 2 + boundaryY * boundaryZ := by
      rw [mul_comm boundaryZ boundaryY]
    _ = 0 := boundary_y_relation

/-- The finite monic tower maps to the actual boundary by sending its two
successive roots to `z` and `y`. -/
def boundaryZYToBoundary :
    BoundaryZYAlgebra →ₐ[k] CanonicalWChartBoundary :=
  AdjoinRoot.liftAlgHom (S := k) boundaryYPolynomial boundaryZToBoundary boundaryY
    boundaryYPolynomial_eval

@[simp]
theorem boundaryZYToBoundary_root :
    boundaryZYToBoundary (AdjoinRoot.root boundaryYPolynomial) = boundaryY := by
  exact AdjoinRoot.liftAlgHom_root boundaryYPolynomial boundaryZToBoundary
    boundaryY boundaryYPolynomial_eval

/-- The quartic root embedded into the second stage still maps to the
boundary `z` coordinate. -/
def boundaryTowerZ : BoundaryZYAlgebra :=
  algebraMap BoundaryZAlgebra BoundaryZYAlgebra
    (AdjoinRoot.root boundaryZPolynomial)

@[simp]
theorem boundaryZYToBoundary_boundaryTowerZ :
    boundaryZYToBoundary boundaryTowerZ = boundaryZ := by
  simp [boundaryTowerZ, boundaryZYToBoundary]

/-- The polynomial expression for `x` inside the monic tower. -/
def boundaryTowerX : BoundaryZYAlgebra :=
  boundaryTowerZ ^ 3 + boundaryTowerZ ^ 2

@[simp]
theorem boundaryZYToBoundary_boundaryTowerX :
    boundaryZYToBoundary boundaryTowerX = boundaryX := by
  simp [boundaryTowerX, boundary_x_eq_z]

/-! ## Surjectivity and finite-dimensionality -/

/-- Reducing affine polynomials first by the canonical equations and then by
`D` gives the natural polynomial presentation of the boundary fibre. -/
def affineToBoundary : AffineChart 3 →ₐ[k] CanonicalWChartBoundary :=
  (Ideal.Quotient.mkₐ k canonicalWChartBoundaryIdeal).comp
    (Ideal.Quotient.mkₐ k (chartAffineEquationIdeal 3))

/-- Every boundary class has an affine-polynomial representative. -/
theorem affineToBoundary_surjective :
    Function.Surjective affineToBoundary :=
  Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective

private def wAffineX : OtherCoordinate 3 := ⟨0, by decide⟩
private def wAffineY : OtherCoordinate 3 := ⟨1, by decide⟩
private def wAffineZ : OtherCoordinate 3 := ⟨2, by decide⟩

@[simp]
theorem affineToBoundary_X_x :
    affineToBoundary (MvPolynomial.X wAffineX) = boundaryX := by
  simp [affineToBoundary, boundaryX, canonicalWChartToBoundary,
    canonicalWChartX, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, wAffineX]

@[simp]
theorem affineToBoundary_X_y :
    affineToBoundary (MvPolynomial.X wAffineY) = boundaryY := by
  simp [affineToBoundary, boundaryY, canonicalWChartToBoundary,
    canonicalWChartY, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, wAffineY]

@[simp]
theorem affineToBoundary_X_z :
    affineToBoundary (MvPolynomial.X wAffineZ) = boundaryZ := by
  simp [affineToBoundary, boundaryZ, canonicalWChartToBoundary,
    canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, wAffineZ]

/-- The finite monic tower covers the boundary: constants lift along the
algebra map, sums lift termwise, and multiplication by each affine variable
uses the explicit tower representatives of `x`, `y`, and `z`. -/
theorem boundaryZYToBoundary_surjective :
    Function.Surjective boundaryZYToBoundary := by
  intro b
  obtain ⟨p, rfl⟩ := affineToBoundary_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨algebraMap k BoundaryZYAlgebra a, ?_⟩
      simp [affineToBoundary]
  | add p q hp hq =>
      rcases hp with ⟨p, hp⟩
      rcases hq with ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      rcases hp with ⟨p, hp⟩
      rcases i with ⟨i, hi⟩
      fin_cases i
      · refine ⟨p * boundaryTowerX, ?_⟩
        rw [map_mul, hp, boundaryZYToBoundary_boundaryTowerX, map_mul]
        congr 1
        simp [affineToBoundary, boundaryX, canonicalWChartToBoundary,
          canonicalWChartX, canonicalWChartPoint, chartQuotientPoint,
          mappedAmbientPoint, chartMap, ambientDehomogenize,
          dehomogenizedVariable]
      · refine ⟨p * AdjoinRoot.root boundaryYPolynomial, ?_⟩
        rw [map_mul, hp, boundaryZYToBoundary_root, map_mul]
        congr 1
        simp [affineToBoundary, boundaryY, canonicalWChartToBoundary,
          canonicalWChartY, canonicalWChartPoint, chartQuotientPoint,
          mappedAmbientPoint, chartMap, ambientDehomogenize,
          dehomogenizedVariable]
      · refine ⟨p * boundaryTowerZ, ?_⟩
        rw [map_mul, hp, boundaryZYToBoundary_boundaryTowerZ, map_mul]
        congr 1
        simp [affineToBoundary, boundaryZ, canonicalWChartToBoundary,
          canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
          mappedAmbientPoint, chartMap, ambientDehomogenize,
          dehomogenizedVariable]
      · exact (hi rfl).elim

/-- The boundary fibre `C/(D)` is a finite `F_2`-module.  This is the
structural zero-dimensionality certificate needed by the global integrality
argument; it uses only two monic extensions and a surjective linear map. -/
theorem canonicalWChartBoundary_moduleFinite :
    Module.Finite k CanonicalWChartBoundary := by
  exact Module.Finite.of_surjective
    boundaryZYToBoundary.toLinearMap boundaryZYToBoundary_surjective

end MazurProof.RationalPointsN25QuotientTwoPlaneChartBoundary
