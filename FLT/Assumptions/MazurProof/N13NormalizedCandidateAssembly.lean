import FLT.Assumptions.MazurProof.N13FakeDescentAssembly
import FLT.Assumptions.MazurProof.N13GaussianCandidateDlog
import FLT.Assumptions.MazurProof.N13GaussianLowDegreeNormalization
import FLT.Assumptions.MazurProof.N13GaussianRamifiedNormalization

/-!
# Normalized local assembly of the N13 candidates

Both sides of the remaining local comparison now have canonical integral
first jets:

* a global four-generator candidate reduces to
  `N13GaussianCandidateDlog.candidateJet`;
* the chosen low-degree Mumford polynomial is cleared of `ℤ₂` denominators,
  divided by its content, and reduces to `canonicalLowJet`.

The latter has zero first logarithm.  Thus it is enough for the global
candidate-envelope argument to identify the candidate jet with this
canonical jet up to a square of a dual-number unit and a constant unit.
This file proves that such an identification supplies exactly the
`CandidateLocalization` required by the weak-descent assembly.

The square is required to be a *unit in the first-jet ring*.  An arbitrary
square in the localized field is not silently reduced: the ramified
uniformizer itself is not a unit modulo its square.  This keeps the local
valuation-parity issue explicit.
-/

namespace MazurProof.N13NormalizedCandidateAssembly

noncomputable section

open N13GaussianLowDegree
open N13GaussianLowDegreeNormalization
open N13GaussianCandidateDlog
open N13GaussianRamifiedNormalization
open N13LocalDlogTwo

abbrev G : Type :=
  N13FakeDescentAssembly.G

abbrev F8 : Type :=
  N13LocalDlogTwo.F8

abbrev Z2 : Type :=
  N13GaussianLowDegreeNormalization.Z2

abbrev JetUnit : Type :=
  (DualNumber F8)ˣ

/-- The fixed low-degree representative used by the actual Kummer
homomorphism. -/
def lowRepresentative (P : G) :
    N13LowDegreeKummerHom.LowRep :=
  N13LowDegreeKummerHom.representative P

/-- Its canonical primitive `ℤ₂` polynomial. -/
def canonicalLowPolynomial (P : G) : Polynomial Z2 :=
  primitiveNormalization (lowRepresentative P).toSemi.u

theorem canonicalLowPolynomial_residue_ne_zero (P : G) :
    residuePolynomial (canonicalLowPolynomial P) ≠ 0 :=
  residuePolynomial_primitiveNormalization_ne_zero
    (lowRepresentative P).toSemi.u

theorem canonicalLowPolynomial_residue_degree (P : G) :
    (residuePolynomial (canonicalLowPolynomial P)).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (primitiveNormalization_natDegree_le
      (lowRepresentative P).degree_le_two)

/-- The genuine first jet of the normalized low-degree Kummer polynomial. -/
def canonicalLowJet (P : G) : JetUnit :=
  lowDegreeJet
    (canonicalLowPolynomial P)
    (canonicalLowPolynomial_residue_ne_zero P)
    (canonicalLowPolynomial_residue_degree P)

theorem dlog_canonicalLowJet (P : G) :
    RamifiedDlog.dlog (canonicalLowJet P) = 0 := by
  exact
    dlog_primitiveNormalization
      (lowRepresentative P).degree_le_two

/-- The sharpened global/local candidate package.  Unlike the older
`CandidateLocalization`, its local clause is an equality between the two
actual integral first jets, modulo precisely the operations killed by the
dual-number logarithm. -/
structure NormalizedCandidateEnvelope : Prop where
  exists_candidate :
    ∀ P : G, ∃ a b c d : ZMod 2,
      N13FakeDescentAssembly.actualKummer P =
        N13FakeDescentAssembly.candidateValue a b c d ∧
      ∃ r : F8ˣ, ∃ w : JetUnit,
        candidateJet a b c d =
          canonicalLowJet P * w ^ 2 *
            RamifiedDlog.constantUnit r

/-- The form naturally produced by global ideal factorization.  If the
ramified-prime valuation is `2m`, division by the rational scalar `2^m`
leaves `(-i)^m`; equivalently, it shifts the `ζ` exponent by the parity of
`m`.  Recording `m` here prevents the fake square-class quotient from
discarding this local correction. -/
structure RamifiedFactorizationEnvelope : Prop where
  exists_factorization :
    ∀ P : G, ∃ m : ℕ, ∃ a b c d : ZMod 2,
      N13FakeDescentAssembly.actualKummer P =
        N13FakeDescentAssembly.candidateValue
          (a + (m : ZMod 2)) b c d ∧
      ∃ r : F8ˣ, ∃ w : JetUnit,
        normalizedCandidateJet m a b c d =
          canonicalLowJet P * w ^ 2 *
            RamifiedDlog.constantUnit r

/-- Ramified normalization supplies the previously abstract local
candidate agreement, with no parity cases. -/
theorem normalizedEnvelope_of_ramifiedFactorization
    (H : RamifiedFactorizationEnvelope) :
    NormalizedCandidateEnvelope where
  exists_candidate P := by
    obtain ⟨m, a, b, c, d, hglobal, r, w, hlocal⟩ :=
      H.exists_factorization P
    refine
      ⟨a + (m : ZMod 2), b, c, d, hglobal,
        r, w, ?_⟩
    rw [← normalizedCandidateJet_eq_parityShift]
    exact hlocal

theorem candidateDlog_eq_zero_of_localAgreement
    (P : G) (a b c d : ZMod 2)
    (hlocal :
      ∃ r : F8ˣ, ∃ w : JetUnit,
        candidateJet a b c d =
          canonicalLowJet P * w ^ 2 *
            RamifiedDlog.constantUnit r) :
    candidateDlog a b c d = 0 := by
  obtain ⟨r, w, hw⟩ := hlocal
  rw [← dlog_candidateJet, hw,
    RamifiedDlog.dlog_mul, RamifiedDlog.dlog_mul,
    dlog_canonicalLowJet, RamifiedDlog.dlog_sq,
    RamifiedDlog.dlog_constantUnit]
  simp

/-- A normalized candidate envelope supplies the exact semantic package
consumed by the existing fake-descent assembly. -/
theorem candidateLocalization_of_normalizedEnvelope
    (H : NormalizedCandidateEnvelope) :
    N13FakeDescentAssembly.CandidateLocalization
      N13FakeDescentAssembly.actualKummer where
  exists_candidate P := by
    obtain ⟨a, b, c, d, hglobal, hlocal⟩ :=
      H.exists_candidate P
    exact
      ⟨a, b, c, d, hglobal,
        candidateDlog_eq_zero_of_localAgreement
          P a b c d hlocal⟩

theorem actualKummer_trivial_of_normalizedEnvelope
    (H : NormalizedCandidateEnvelope) :
    ∀ P : G, N13FakeDescentAssembly.actualKummer P = 0 :=
  N13FakeDescentAssembly.actualKummer_trivial_of_candidateLocalization
    (candidateLocalization_of_normalizedEnvelope H)

theorem actualKummer_trivial_of_ramifiedFactorization
    (H : RamifiedFactorizationEnvelope) :
    ∀ P : G, N13FakeDescentAssembly.actualKummer P = 0 :=
  actualKummer_trivial_of_normalizedEnvelope
    (normalizedEnvelope_of_ramifiedFactorization H)

/-- After the normalized global/local comparison, only the genuine converse
Kummer-kernel theorem remains before doubling surjectivity. -/
theorem twoSurjective_of_normalizedEnvelope
    (kernel_double_or_infinity :
      ∀ P : G,
        N13FakeDescentAssembly.actualKummer P = 0 ↔
          (∃ Q : G, P = 2 • Q) ∨
          (∃ Q : G,
            P = 2 • Q +
              N13KummerKernelAssembly.infinityClass))
    (H : NormalizedCandidateEnvelope) :
    N13TwoAdicEndgame.TwoSurjective G :=
  N13FakeDescentAssembly.twoSurjective_of_actualCandidateLocalization
    kernel_double_or_infinity
    (candidateLocalization_of_normalizedEnvelope H)

theorem twoSurjective_of_ramifiedFactorization
    (kernel_double_or_infinity :
      ∀ P : G,
        N13FakeDescentAssembly.actualKummer P = 0 ↔
          (∃ Q : G, P = 2 • Q) ∨
          (∃ Q : G,
            P = 2 • Q +
              N13KummerKernelAssembly.infinityClass))
    (H : RamifiedFactorizationEnvelope) :
    N13TwoAdicEndgame.TwoSurjective G :=
  twoSurjective_of_normalizedEnvelope
    kernel_double_or_infinity
    (normalizedEnvelope_of_ramifiedFactorization H)

end

end MazurProof.N13NormalizedCandidateAssembly
