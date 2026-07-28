import FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog
import FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber

/-!
# Surjectivity of doubling for the N13 concrete Picard group

The global zero-carrier calculation proves that the actual Mumford Kummer
homomorphism is identically zero.  The structural identity-fibre theorem
identifies its kernel with the subgroup of doubles.  Their composition is
exactly surjectivity of multiplication by two.
-/

namespace MazurProof.N13MumfordFullKummerTwoSurjective

noncomputable section

abbrev G : Type :=
  N13LowDegreeKummerHom.G

/-- Multiplication by two is surjective on the concrete N13 Picard group. -/
theorem twoSurjective :
    N13TwoAdicEndgame.TwoSurjective G := by
  intro P
  exact
    (N13MumfordFullKummerIdentityFiber.kernel_eq_doubles P).mp
      (N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial P)

/-- For the actual image quotient, no special-fibre group law or
exponent-nineteen argument is needed.  Finiteness of the quotient and a
separated reduction kernel already force injectivity. -/
theorem reduction_injective_of_finite_image
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (red : G →+ J₂)
    (red_surjective : Function.Surjective red)
    (separated :
      N18RouteC.Separated.NSeparated red.ker 2) :
    Function.Injective red :=
  N13TwoAdicEndgame.reduction_injective_of_finite_target
    red red_surjective twoSurjective separated

/-- Assemble the remaining geometric reduction data with the now-proved
doubling surjectivity. -/
def endgameData
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (abelFibres :
      N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (formalKernel :
      N13TwoAdicEndgame.FormalKernelData red.ker) :
    N13TwoAdicEndgame.Data G J₂ where
  abelFibres := abelFibres
  red := red
  twoSurjective := twoSurjective
  formalKernel := formalKernel

/-- Once the genuine special-fibre Abel data, reduction map, and formal
kernel are constructed, reduction injectivity is immediate. -/
theorem reduction_injective
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (abelFibres :
      N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (formalKernel :
      N13TwoAdicEndgame.FormalKernelData red.ker) :
    Function.Injective red :=
  (endgameData abelFibres red formalKernel).reduction_injective

end

end MazurProof.N13MumfordFullKummerTwoSurjective
