import FLT.Assumptions.MazurProof.N13GaussianDifferentSupport
import FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam

/-!
# Zero-carrier N13 fake squareclasses

The structural analysis of the different proves that the normalized Kummer
integer is a maximal-order unit times an integral square.  Transporting that
identity through the named-unit basis leaves only the three unit coordinates.
The rational scalar used for primitive normalization is invisible in the fake
squareclass quotient.  Hence the actual Mumford Kummer value has fourth
candidate coordinate zero.
-/

namespace MazurProof.N13GaussianZeroCarrierCapstone

noncomputable section

abbrev LowRep := N13LowDegreeKummerHom.LowRep
abbrev Ls := N13SexticSquareclass.SexticAlgebra

/-- The normalized integral unit lies in the three-dimensional named-unit
subspace of the fake squareclass target. -/
theorem normalizedIntegralUnit_fakeClass_eq_candidateClass_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D :
          Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
        N13CandidateCollapse.candidateClass i j k 0 := by
  obtain ⟨ε, y, hxy⟩ :=
    N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq D
  have hx :=
    N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  have hunit :
      N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D =
        N13GaussianNormalizationOrderTransport.unitOfNonzero
          (N13GlobalKummerNormalization.normalizedKummerInteger D) hx := by
    apply Units.ext
    rfl
  obtain ⟨i, j, k, hclass⟩ :=
    N13GaussianNormalizationOrderTransport.fakeClass_eq_candidateClass_zeroCarrier
      (N13GlobalKummerNormalization.normalizedKummerInteger D)
      hx ε y hxy
  refine ⟨i, j, k, ?_⟩
  rw [hunit]
  exact hclass

/-- The actual sextic Kummer unit has the same zero-carrier candidate class.
No case split on the three unit coordinates is used. -/
theorem uThetaUnit_fakeClass_eq_candidateClass_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
        N13CandidateCollapse.candidateClass i j k 0 := by
  apply
    N13GaussianNormalizedSquareclassSeam.uThetaUnit_candidateClass_of_normalized
  exact normalizedIntegralUnit_fakeClass_eq_candidateClass_zero D

end

end MazurProof.N13GaussianZeroCarrierCapstone
