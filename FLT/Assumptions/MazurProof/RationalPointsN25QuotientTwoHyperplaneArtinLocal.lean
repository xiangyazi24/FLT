import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoHyperplaneArtinKernel
import Mathlib.RingTheory.Localization.Algebra

/-!
# Principal-open presentations of the binary hyperplane-section Artin factors

The affine kernel calculations identify the double and triple normal forms
before localization.  This file performs the remaining scheme-local step.
It maps the actual chart equations into the principal opens isolating the two
nonreduced points, proves the localized equation ideals equal the corresponding
normal ideals, and uses the general theorem that localization commutes with
kernels to identify both ideals as exact kernels of the Artin evaluations.

Thus the principal-open quotient rings themselves, rather than merely their
closed points or vector-space dimensions, have the required length-two and
length-three Artin presentations.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin

/-! ## Exact kernels after inverting one element -/

/-- Extending a ring map across a principal open set localizes its kernel,
provided the chosen denominator already maps to a unit.  This packages the
general Mathlib theorem that localization commutes with kernels in the exact
form needed by the two Artin evaluations below. -/
theorem awayLift_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (hr : IsUnit (f r)) :
    RingHom.ker (Localization.awayLift f r hr) =
      Ideal.map (algebraMap R (Localization.Away r)) (RingHom.ker f) := by
  letI : IsLocalization.Away (f r) S :=
    IsLocalization.away_of_isUnit_of_bijective S hr Function.bijective_id
  rw [show Localization.awayLift f r hr =
      IsLocalization.Away.map (Localization.Away r) S f r from
    IsLocalization.ringHom_ext (.powers r) (by
      ext x
      simp [IsLocalization.Away.map])]
  exact IsLocalization.ker_map S f (Submonoid.map_powers f r)

/-- The local equation ideal on `D(y+z+1)` is the doubled triangular ideal. -/
theorem wLocalized_intersectionIdeal_eq_normalForm :
    Ideal.span
        {(algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 0)) ^ 2 +
            algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 1),
          algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 1) *
            (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                  (MvPolynomial.X 0) +
                algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                  (MvPolynomial.X 1) + 1)} =
      Ideal.span
        {(algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
            (MvPolynomial.X 0)) ^ 2,
          algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
            (MvPolynomial.X 1)} := by
  exact wChart_intersectionIdeal_eq_normalForm
      (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
        (MvPolynomial.X 0))
      (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
        (MvPolynomial.X 1))
      (by
        let f := algebraMap BinaryAffinePlane
          (Localization.Away wChartDenominator)
        change IsUnit (f (MvPolynomial.X 0) + f (MvPolynomial.X 1) + 1)
        rw [← map_one f, ← map_add, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit wChartDenominator)

/-- The local equation ideal on `D(1+b)` is the tripled triangular ideal. -/
theorem yzLocalized_intersectionIdeal_eq_normalForm :
    Ideal.span
        {algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 0) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 1),
          (1 + algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 0)) *
              algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 1) *
            (algebraMap BinaryAffinePlane
                  (Localization.Away yzChartDenominator) (MvPolynomial.X 0) +
              algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 1))} =
      Ideal.span
        {algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 0) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 1),
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
            (MvPolynomial.X 1)) ^ 3} := by
  exact yzChart_intersectionIdeal_eq_normalForm
      (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
        (MvPolynomial.X 0))
      (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
        (MvPolynomial.X 1))
      (by
        have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
        have htwoSource : (2 : BinaryAffinePlane) = 0 := by
          change MvPolynomial.C (2 : ZMod 2) = 0
          rw [htwoCoeff, map_zero]
        simpa only [map_ofNat, map_zero] using congrArg
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
          htwoSource)
      (by
        let f := algebraMap BinaryAffinePlane
          (Localization.Away yzChartDenominator)
        change IsUnit (1 + f (MvPolynomial.X 1))
        rw [← map_one f, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit yzChartDenominator)

/-! ## Exact local Artin presentations -/

/-- Mapping the two chart equations into `D(y+z+1)` gives exactly the mapped
double-point normal ideal. -/
theorem wLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}) =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        doubleNormalIdeal := by
  simpa [wChartQuadricPolynomial, wChartCubicPolynomial, doubleNormalIdeal,
    Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using
    wLocalized_intersectionIdeal_eq_normalForm

/-- Mapping the translated chart equations into `D(1+b)` gives exactly the
mapped triple-point normal ideal. -/
theorem yzLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial}) =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        tripleNormalIdeal := by
  simpa [yzChartQuadricPolynomial, yzChartCubicPolynomial, tripleNormalIdeal,
    Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using
    yzLocalized_intersectionIdeal_eq_normalForm

/-- The kernel of the doubled evaluation on the principal open set is the
extension of the doubled normal ideal. -/
theorem doubleLocalizedEvaluation_ker :
    RingHom.ker doubleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        doubleNormalIdeal := by
  rw [doubleLocalizedEvaluation, awayLift_ker, doubleEvaluation_ker]

/-- The kernel of the tripled evaluation on the principal open set is the
extension of the tripled normal ideal. -/
theorem tripleLocalizedEvaluation_ker :
    RingHom.ker tripleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        tripleNormalIdeal := by
  rw [tripleLocalizedEvaluation, awayLift_ker, tripleEvaluation_ker]

/-- On `D(y+z+1)`, the actual chart equations cut out precisely the kernel of
the evaluation to `F₂[t]/(t²)`. -/
theorem doubleLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker doubleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}) := by
  rw [doubleLocalizedEvaluation_ker, wLocalized_chartIdeal_eq_normalIdeal]

/-- On `D(1+b)`, the actual translated chart equations cut out precisely the
kernel of the evaluation to `F₂[t]/(t³)`. -/
theorem tripleLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker tripleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial}) := by
  rw [tripleLocalizedEvaluation_ker, yzLocalized_chartIdeal_eq_normalIdeal]

/-! ## Quotient-ring presentations -/

/-- The localized doubled evaluation remains surjective because every target
element already has a preimage before the denominator is inverted. -/
theorem doubleLocalizedEvaluation_surjective :
    Function.Surjective doubleLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := doubleEvaluation_surjective x
  refine ⟨algebraMap BinaryAffinePlane
    (Localization.Away wChartDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq
    wChartDenominator doubleEvaluation_denominator_isUnit p

/-- The localized tripled evaluation remains surjective for the same
structural reason. -/
theorem tripleLocalizedEvaluation_surjective :
    Function.Surjective tripleLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := tripleEvaluation_surjective x
  refine ⟨algebraMap BinaryAffinePlane
    (Localization.Away yzChartDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq
    yzChartDenominator tripleEvaluation_denominator_isUnit p

/-- The actual local equation quotient on `D(y+z+1)` is the doubled Artin
ring `F₂[t]/(t²)`.  This is the first isomorphism theorem applied to the
exact localized kernel calculation above. -/
noncomputable def doubleLocalizedChartQuotientEquiv :
    (Localization.Away wChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial})) ≃+*
      DoubleArtin :=
  (Ideal.quotEquivOfEq doubleLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      doubleLocalizedEvaluation_surjective)

/-- The actual local equation quotient on `D(1+b)` is the tripled Artin ring
`F₂[t]/(t³)`. -/
noncomputable def tripleLocalizedChartQuotientEquiv :
    (Localization.Away yzChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial})) ≃+*
      TripleArtin :=
  (Ideal.quotEquivOfEq tripleLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      tripleLocalizedEvaluation_surjective)

end MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin
