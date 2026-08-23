import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFullClosedPoints

/-!
# Canonical affine primes attached to binary closed points

An exact-period geometric point determines a prime on the affine chart
selected by its normalized pivot.  The pivot and the evaluation kernel are
both Frobenius invariant.  Passing through the product of the four chart
rings gives a fixed target in which the prime descends to the exact
Frobenius orbit class.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoClosedPointPrime

open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoClosedPointChart
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoFullClosedPoints

/-- The product of the four canonical affine chart rings.  Its prime
spectrum is the disjoint union of the spectra of the four factors. -/
abbrev CanonicalChartProductTwo :=
  ∀ i : Fin 4, ChartQuotient i

/-- A curve point, equipped with its own canonical normalized chart. -/
def pointOnCanonicalChart
    {K : Type} [Field K] (P : CurvePointTwo K) :
    CurvePointOnChart (normalizedPivot P.1) K :=
  ⟨P, rfl⟩

/-- Evaluation on the canonical chart, expressed on a fixed product ring so
that the target prime-spectrum type does not depend on the pivot. -/
def canonicalChartProductEval
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) : CanonicalChartProductTwo →+* K :=
  (chartQuotientEval (normalizedPivot P.1) (pointOnCanonicalChart P)).comp
    (Pi.evalRingHom (fun i : Fin 4 => ChartQuotient i)
      (normalizedPivot P.1))

/-- Arithmetic Frobenius postcomposes evaluation on the fixed chart-product
ring by the field Frobenius. -/
theorem canonicalChartProductEval_frobenius
    (d : ℕ) (P : CurvePointTwo (CommonField 2 d)) :
    canonicalChartProductEval
        (pointFrobenius canonicalTwoModel 2 d P) =
      (commonFrobenius 2 d).toRingEquiv.toRingHom.comp
        (canonicalChartProductEval P) := by
  cases P with
  | mk P hP =>
      cases P <;>
        apply RingHom.ext <;>
        intro f <;>
        exact DFunLike.congr_fun
          (chartQuotientEval_frobenius d _
            (pointOnCanonicalChart ⟨_, hP⟩)) (f _)

/-- The fixed chart-product prime attached to a geometric curve point. -/
def canonicalChartProductPrime
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    PrimeSpectrum CanonicalChartProductTwo :=
  ⟨RingHom.ker (canonicalChartProductEval P),
    RingHom.ker_isPrime (canonicalChartProductEval P)⟩

/-- The product-ring prime is exactly the image of the evaluation prime on
the canonical pivot factor. -/
theorem canonicalChartProductPrime_eq_sigmaToPi
    {K : Type} [Field K] [Algebra (ZMod 2) K]
    (P : CurvePointTwo K) :
    canonicalChartProductPrime P =
      PrimeSpectrum.sigmaToPi
        (fun i : Fin 4 => ChartQuotient i)
        ⟨normalizedPivot P.1,
          chartPointPrime _ (pointOnCanonicalChart P)⟩ := by
  apply PrimeSpectrum.ext
  rfl

/-- A point and its Frobenius conjugate define the same chart-product
prime. -/
@[simp]
theorem canonicalChartProductPrime_frobenius
    (d : ℕ) (P : CurvePointTwo (CommonField 2 d)) :
    canonicalChartProductPrime
        (pointFrobenius canonicalTwoModel 2 d P) =
      canonicalChartProductPrime P := by
  apply PrimeSpectrum.ext
  change RingHom.ker
      (canonicalChartProductEval
        (pointFrobenius canonicalTwoModel 2 d P)) =
    RingHom.ker (canonicalChartProductEval P)
  rw [canonicalChartProductEval_frobenius]
  ext f
  simp

/-- Every Frobenius iterate defines the same chart-product prime. -/
theorem canonicalChartProductPrime_frobenius_iterate
    (d n : ℕ) (P : CurvePointTwo (CommonField 2 d)) :
    canonicalChartProductPrime
        (((pointFrobenius canonicalTwoModel 2 d : _ → _)^[n]) P) =
      canonicalChartProductPrime P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        canonicalChartProductPrime_frobenius, ih]

/-- The chart-product prime attached to an exact-period geometric point. -/
def exactPeriodicPointChartPrime
    (d : ℕ)
    (P : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    PrimeSpectrum CanonicalChartProductTwo :=
  canonicalChartProductPrime P.1

/-- Exact-period points in the same Frobenius orbit determine the same
chart-product prime. -/
theorem exactPeriodicPointChartPrime_eq_of_sameOrbit
    (d : ℕ)
    (P Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hPQ : SameExactOrbit (degreePointFrobeniusTwo d) d P Q) :
    exactPeriodicPointChartPrime d P =
      exactPeriodicPointChartPrime d Q := by
  rcases hPQ with ⟨n, hn⟩
  unfold exactPeriodicPointChartPrime
  rw [← hn]
  simpa only [degreePointFrobeniusTwo] using
    (canonicalChartProductPrime_frobenius_iterate d n.1 P.1).symm

/-- A positive-degree closed orbit determines a canonical affine prime,
independently of the chosen exact-period representative. -/
def fullClosedPointChartPrime
    : (d : ℕ) → 0 < d →
      fullClosedPointGrading25Two.Closed d →
        PrimeSpectrum CanonicalChartProductTwo
  | 0, hd, _ => by omega
  | n + 1, _, P =>
      Quotient.lift
        (exactPeriodicPointChartPrime (n + 1))
        (exactPeriodicPointChartPrime_eq_of_sameOrbit (n + 1)) P

/-- The descended product-ring prime lies on the factor selected by the
closed orbit's canonical pivot. -/
theorem fullClosedPointChartPrime_lies_over_pivot
    (d : ℕ) (hd : 0 < d)
    (P : fullClosedPointGrading25Two.Closed d) :
    ∃ q : PrimeSpectrum
        (ChartQuotient (fullClosedPointPivot hd P)),
      fullClosedPointChartPrime d hd P =
        PrimeSpectrum.sigmaToPi
          (fun i : Fin 4 => ChartQuotient i)
          ⟨fullClosedPointPivot hd P, q⟩ := by
  revert hd P
  cases d with
  | zero =>
      intro hd
      omega
  | succ n =>
      intro hd P
      induction P using Quotient.inductionOn with
      | _ Q =>
          refine ⟨chartPointPrime _ (pointOnCanonicalChart Q.1), ?_⟩
          simpa [fullClosedPointChartPrime, fullClosedPointPivot,
            exactPeriodicPointChartPrime] using
            canonicalChartProductPrime_eq_sigmaToPi Q.1

end MazurProof.RationalPointsN25QuotientTwoClosedPointPrime
