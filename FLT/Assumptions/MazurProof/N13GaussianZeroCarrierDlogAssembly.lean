import FLT.Assumptions.MazurProof.N13GaussianZeroCarrierGroup

/-!
# Dlog assembly on the zero-carrier N13 candidate slice

The old four-coordinate candidate family has a one-dimensional kernel under
the first ramified logarithm.  The global argument now fixes the fourth
coordinate to zero, and the compiled cubic minimal-polynomial calculation
then detects all three remaining coordinates.

This file isolates the sole remaining local semantic input: a candidate
representing an actual Kummer value must have zero ramified logarithm.
-/

namespace MazurProof.N13GaussianZeroCarrierDlogAssembly

noncomputable section

abbrev G := N13LowDegreeKummerHom.G

/-- The remaining global-to-local compatibility, restricted to the
zero-carrier candidate slice already forced by global arithmetic. -/
structure ZeroCarrierDlogCompatibility : Prop where
  dlog_zero :
    ∀ (P : G) (i j k : ZMod 2),
      N13FakeDescentAssembly.actualKummer P =
          N13FakeDescentAssembly.candidateValue i j k 0 →
        N13LocalDlogTwo.candidateDlog i j k 0 = 0

/-- On the zero-carrier slice, vanishing of the first ramified logarithm
forces all three named-unit coordinates to vanish.  This is coefficient
uniqueness in the cubic residue field, not a case split. -/
theorem zeroCarrier_coordinates_eq_zero
    {i j k : ZMod 2}
    (h : N13LocalDlogTwo.candidateDlog i j k 0 = 0) :
    i = 0 ∧ j = 0 ∧ k = 0 := by
  obtain ⟨hi, hj, hk⟩ :=
    (N13LocalDlogTwo.candidateDlog_eq_zero_iff i j k 0).mp h
  exact ⟨hi, hj, by simpa using hk⟩

/-- The specialized compatibility supplies the existing generic candidate
localization, with its support coordinate fixed to zero. -/
theorem candidateLocalization
    (H : ZeroCarrierDlogCompatibility) :
    N13FakeDescentAssembly.CandidateLocalization
      N13FakeDescentAssembly.actualKummer where
  exists_candidate P := by
    obtain ⟨i, j, k, hP⟩ :=
      N13GaussianZeroCarrierGroup.actualKummer_eq_zeroCarrierCandidate P
    exact ⟨i, j, k, 0, hP, H.dlog_zero P i j k hP⟩

/-- Once the one remaining local compatibility is supplied, the genuine
N13 fake-Kummer homomorphism is identically zero. -/
theorem actualKummer_trivial
    (H : ZeroCarrierDlogCompatibility) :
    ∀ P : G, N13FakeDescentAssembly.actualKummer P = 0 :=
  N13FakeDescentAssembly.actualKummer_trivial_of_candidateLocalization
    (candidateLocalization H)

end

end MazurProof.N13GaussianZeroCarrierDlogAssembly
