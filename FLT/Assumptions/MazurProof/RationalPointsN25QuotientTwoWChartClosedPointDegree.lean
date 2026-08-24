import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWChartNormalization
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective

/-!
# Closed-point degrees on the canonical W-chart

For a maximal ideal of the canonical `W = 1` chart, the cardinality of its
residue field factors through the residue field of its contraction to
`F₂[z]`.  Comparing both cardinalities as powers of two shows that the
closed-point degree is the product of the contracted-prime degree and the
inertia degree.  This identifies the ideal-theoretic exponent appearing in
the relative norm with the degree already certified by the Frobenius-orbit
closed-point grading.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWChartClosedPointDegree

open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWChartNormalization

local notation "k₂" => ZMod 2
local notation "Rz" => Polynomial k₂
local notation "W" => WChartQuotient

/-- The binary degree of the residue field of the contracted base prime. -/
noncomputable def canonicalWChartBasePrimeDegree (P : Ideal W) : ℕ :=
  Module.finrank k₂ (Rz ⧸ canonicalWChartBasePrime P)

/-- The residue cardinality upstairs is the residue cardinality downstairs
raised to the inertia degree. -/
theorem canonicalWChartQuotient_card_eq_base_card_pow_inertia
    (P : Ideal W) [P.IsMaximal] :
    Nat.card (W ⧸ P) =
      Nat.card (Rz ⧸ canonicalWChartBasePrime P) ^
        (canonicalWChartBasePrime P).inertiaDeg P := by
  let p : Ideal Rz := canonicalWChartBasePrime P
  letI : p.IsMaximal := canonicalWChartBasePrime_isMaximal P
  letI : P.LiesOver p := canonicalWChartBasePrime_liesOver P
  letI : Field (Rz ⧸ p) := Ideal.Quotient.field p
  letI : Field (W ⧸ P) := Ideal.Quotient.field P
  letI quotientAlgebra : Algebra (Rz ⧸ p) (W ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (P.over_def p))
  letI : Module (Rz ⧸ p) (W ⧸ P) := quotientAlgebra.toModule
  have hcard := Module.natCard_eq_pow_finrank
    (K := Rz ⧸ p) (V := W ⧸ P)
  rw [← Ideal.inertiaDeg_algebraMap p P] at hcard
  exact hcard

/-- The contracted base residue field has `2` to the contracted-prime degree
elements. -/
theorem canonicalWChartBasePrime_residue_card
    (P : Ideal W) [P.IsMaximal] :
    Nat.card (Rz ⧸ canonicalWChartBasePrime P) =
      2 ^ canonicalWChartBasePrimeDegree P := by
  let p : Ideal Rz := canonicalWChartBasePrime P
  letI : p.IsMaximal := canonicalWChartBasePrime_isMaximal P
  letI : Field (Rz ⧸ p) := Ideal.Quotient.field p
  letI : Algebra.FiniteType k₂ (Rz ⧸ p) := inferInstance
  letI : Module.Finite k₂ (Rz ⧸ p) :=
    finite_of_finite_type_of_isJacobsonRing k₂ (Rz ⧸ p)
  simpa [p, canonicalWChartBasePrimeDegree] using
    Module.natCard_eq_pow_finrank (K := k₂) (V := Rz ⧸ p)

/-- For every nonboundary full closed-point atom, the product of its
contracted-prime degree and its inertia degree is its Frobenius-orbit degree. -/
theorem canonicalWChartBasePrimeDegree_mul_inertiaDeg_eq_atomDegree
    (A : FullNonBoundaryAtom25Two) :
    canonicalWChartBasePrimeDegree (fullNonBoundaryPrimeIdeal A) *
        (canonicalWChartBasePrime
          (fullNonBoundaryPrimeIdeal A)).inertiaDeg
            (fullNonBoundaryPrimeIdeal A) =
      fullClosedPointGrading25Two.atomDegree A.1 := by
  letI : (fullNonBoundaryPrimeIdeal A).IsMaximal :=
    (fullNonBoundaryPrimeData A).isMaximal
  have hcard := fullNonBoundaryPrimeIdeal_residue_card A
  rw [canonicalWChartQuotient_card_eq_base_card_pow_inertia,
    canonicalWChartBasePrime_residue_card] at hcard
  have hpow :
      2 ^ (canonicalWChartBasePrimeDegree
          (fullNonBoundaryPrimeIdeal A) *
          (canonicalWChartBasePrime
            (fullNonBoundaryPrimeIdeal A)).inertiaDeg
              (fullNonBoundaryPrimeIdeal A)) =
        2 ^ fullClosedPointGrading25Two.atomDegree A.1 := by
    simpa only [pow_mul] using hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow

end MazurProof.RationalPointsN25QuotientTwoWChartClosedPointDegree
