import FLT.Assumptions.MazurProof.CurveDedekindDivisor
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWChartNormalization
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPrimeSurjective

abbrev W := WChartQuotient

abbrev WMaxIdeal := {m : Ideal W // m.IsMaximal}

abbrev WHeightOne := IsDedekindDomain.HeightOneSpectrum W

/-! ## Reindexing the affine divisor to projective atoms

The fixed W-chart is Dedekind. Its height-one primes identify with the
nonboundary atoms of the full closed-point grading. This transports the
existing affine principal-divisor homomorphism without yet asserting the
projective product formula or degree zero.
-/

/-- The maximal-ideal equivalence returns the geometric prime ideal itself. -/
@[simp]
theorem fullNonBoundaryAtomEquivMaximalIdeal_val
    (A : FullNonBoundaryAtom25Two) :
    (fullNonBoundaryAtomEquivMaximalIdeal A).1 =
      fullNonBoundaryPrimeIdeal A := by
  rfl

/-- Nonboundary full atoms correspond to height-one primes of the W-chart.
The nonzero-prime datum supplies the final field required by the
`HeightOneSpectrum` constructor. -/
noncomputable def fullNonBoundaryAtomEquivHeightOne :
    FullNonBoundaryAtom25Two ≃ WHeightOne where
  toFun A :=
    { asIdeal := (fullNonBoundaryAtomEquivMaximalIdeal A).1
      isPrime := (fullNonBoundaryAtomEquivMaximalIdeal A).2.isPrime
      ne_bot := by
        rw [fullNonBoundaryAtomEquivMaximalIdeal_val]
        exact (fullNonBoundaryPrimeData A).ne_bot }
  invFun v :=
    fullNonBoundaryAtomEquivMaximalIdeal.symm
      ⟨v.asIdeal,
        IsDedekindDomain.HeightOneSpectrum.isMaximal v⟩
  left_inv A := by
    apply fullNonBoundaryAtomEquivMaximalIdeal.injective
    rw [fullNonBoundaryAtomEquivMaximalIdeal.apply_symm_apply]
    apply Subtype.ext
    rfl
  right_inv v := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    simpa using
      congrArg Subtype.val
        (fullNonBoundaryAtomEquivMaximalIdeal.apply_symm_apply
          (⟨v.asIdeal,
              IsDedekindDomain.HeightOneSpectrum.isMaximal v⟩ :
            WMaxIdeal))

/-- The associated height-one prime is the original W-chart prime. -/
@[simp]
theorem fullNonBoundaryAtomEquivHeightOne_asIdeal
    (A : FullNonBoundaryAtom25Two) :
    (fullNonBoundaryAtomEquivHeightOne A).asIdeal =
      fullNonBoundaryPrimeIdeal A := by
  rfl

/-- The residue-field degree agrees with the degree assigned by the
full closed-point grading. -/
@[simp]
theorem residueDegree_fullNonBoundaryAtomEquivHeightOne
    (A : FullNonBoundaryAtom25Two) :
    residueDegree (fullNonBoundaryAtomEquivHeightOne A).asIdeal =
      fullClosedPointGrading25Two.atomDegree A.1 := by
  rw [fullNonBoundaryAtomEquivHeightOne_asIdeal]
  exact residueDegree_fullNonBoundaryPrimeIdeal A

/-- The affine Dedekind principal divisor reindexed by nonboundary full
closed-point atoms. Finite support and additivity are inherited from the
existing affine homomorphism. -/
noncomputable def nonBoundaryPrincipalDivisor :
    Additive ((FractionRing W)ˣ) →+
      (FullNonBoundaryAtom25Two →₀ ℤ) :=
  (Finsupp.domCongr
      fullNonBoundaryAtomEquivHeightOne.symm).toAddMonoidHom.comp
    (CurveDedekindDivisor.principalDivisor :
      Additive ((FractionRing W)ˣ) →+
        (WHeightOne →₀ ℤ))

/-- Each nonboundary coefficient is the affine Dedekind order at its
corresponding height-one prime. -/
@[simp]
theorem nonBoundaryPrincipalDivisor_apply
    (f : Additive ((FractionRing W)ˣ))
    (A : FullNonBoundaryAtom25Two) :
    nonBoundaryPrincipalDivisor f A =
      CurveDedekindDivisor.principalDivisor f
        (fullNonBoundaryAtomEquivHeightOne A) := by
  rfl

end MazurProof.N25F_NonBoundaryPrincipalDivisor
