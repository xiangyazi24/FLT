import FLT.Assumptions.MazurProof.N13GaussianZeroCarrierCapstone
import FLT.Assumptions.MazurProof.N13FakeDescentAssembly

/-!
# Zero-carrier candidates for the N13 Kummer homomorphism

The zero-carrier theorem for each low-degree semirepresentative descends
immediately to the chosen structural fake-Kummer homomorphism on the oriented
Picard group.  This module performs only that representation bridge; it does
not use any local logarithm calculation.
-/

namespace MazurProof.N13GaussianZeroCarrierGroup

noncomputable section

abbrev G := N13LowDegreeKummerHom.G

/-- Every value of the genuine fake-Kummer homomorphism belongs to the
three-dimensional named-unit subspace with fourth coordinate zero. -/
theorem actualKummer_eq_zeroCarrierCandidate
    (P : G) :
    ∃ i j k : ZMod 2,
      N13FakeDescentAssembly.actualKummer P =
        N13FakeDescentAssembly.candidateValue i j k 0 := by
  let D : N13LowDegreeKummerHom.LowRep :=
    N13LowDegreeKummerHom.representative P
  obtain ⟨i, j, k, hclass⟩ :=
    N13GaussianZeroCarrierCapstone.uThetaUnit_fakeClass_eq_candidateClass_zero D
  refine ⟨i, j, k, ?_⟩
  change
    Additive.ofMul
        (((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) :
            N13MumfordKummerValue.Lˣ)) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      Additive.ofMul
        (N13CandidateCollapse.candidateClass i j k 0)
  exact congrArg Additive.ofMul hclass

end

end MazurProof.N13GaussianZeroCarrierGroup
