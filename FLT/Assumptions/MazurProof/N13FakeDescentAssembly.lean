import FLT.Assumptions.MazurProof.N13CandidateCollapse
import FLT.Assumptions.MazurProof.N13KummerKernelAssembly
import FLT.Assumptions.MazurProof.N13MumfordKummerValue

/-!
# Assembly of the structural N13 fake descent

The finite algebra is already complete: a candidate whose first ramified
logarithm vanishes has trivial fake square class.  This file isolates the two
semantic arithmetic inputs needed to apply that calculation to the genuine
Jacobian Kummer map:

1. every global Kummer value has a representative in the four-generator
   candidate envelope;
2. the representative attached to a rational Jacobian class has vanishing
   first local logarithm at two.

No candidate enumeration, Mordell--Weil generators, or finiteness hypothesis
is used in the assembly.
-/

namespace MazurProof.N13FakeDescentAssembly

noncomputable section

open N13SexticSquareclass

abbrev G : Type :=
  N13KummerKernelAssembly.G

abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget

/-- The additive version of the four-generator fake square class. -/
def candidateValue (i j k s : ZMod 2) : Target :=
  Additive.ofMul (N13CandidateCollapse.candidateClass i j k s)

/-- The honest global-to-local semantic package.  The exponents may depend on
the Jacobian class; no finite list of Jacobian generators is assumed. -/
structure CandidateLocalization (kummer : G →+ Target) : Prop where
  exists_candidate :
    ∀ P : G, ∃ i j k s : ZMod 2,
      kummer P = candidateValue i j k s ∧
      N13LocalDlogTwo.candidateDlog i j k s = 0

/-- Structural candidate collapse in the additive fake-Kummer target. -/
theorem candidateValue_eq_zero_of_dlog_eq_zero
    (i j k s : ZMod 2)
    (hlocal : N13LocalDlogTwo.candidateDlog i j k s = 0) :
    candidateValue i j k s = 0 := by
  change
    Additive.ofMul
        (N13CandidateCollapse.candidateClass i j k s) =
      Additive.ofMul 1
  exact congrArg Additive.ofMul
    (N13CandidateCollapse.candidateClass_eq_one_of_dlog_eq_zero
      i j k s hlocal)

/-- The two semantic bridges and the structural candidate calculation make
the genuine fake-Kummer map trivial. -/
theorem kummer_trivial_of_candidateLocalization
    (kummer : G →+ Target)
    (H : CandidateLocalization kummer) :
    ∀ P : G, kummer P = 0 := by
  intro P
  obtain ⟨i, j, k, s, hP, hlocal⟩ :=
    H.exists_candidate P
  rw [hP]
  exact candidateValue_eq_zero_of_dlog_eq_zero i j k s hlocal

/-- Full weak-descent assembly.  The generic even-sextic kernel theorem and
the global/local candidate localization are the only remaining inputs; the
N13 infinity ambiguity is removed by its explicit half-class. -/
theorem twoSurjective_of_candidateLocalization
    (kummer : G →+ Target)
    (kernel_double_or_infinity :
      ∀ P : G, kummer P = 0 ↔
        (∃ Q : G, P = 2 • Q) ∨
        (∃ Q : G,
          P = 2 • Q + N13KummerKernelAssembly.infinityClass))
    (H : CandidateLocalization kummer) :
    N13TwoAdicEndgame.TwoSurjective G := by
  exact N13KummerKernelAssembly.twoSurjective_of_kummer_trivial
    kummer kernel_double_or_infinity
    (kummer_trivial_of_candidateLocalization kummer H)

end

end MazurProof.N13FakeDescentAssembly
