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

/-- The generic Padé square root and the exact half selected by the current
Kummer proof, retained instead of immediately erasing them behind
surjectivity.  This still makes no claim that the generic ideal root extends
to a normalized two-adic graph lattice. -/
structure ConstructedHalfData (P : G) where
  representative : N13LowDegreeKummerHom.LowRep
  representative_spec :
    N13LowDegreeKummerHom.lowClass representative = P
  finite :
    N13MumfordFullKummerIdentityFiber.FiniteIdealHalfData representative
  double_eq :
    P = 2 • finite.half

/-- Run the existing full-gauge and Padé construction while retaining its
chosen generic ideal root, principal correction, and half. -/
def constructedHalfData (P : G) :
    ConstructedHalfData P := by
  let D := N13LowDegreeKummerHom.representative P
  have hfull :
      N13MumfordOrientedFullKummer.orientedFullKummer P = 1 :=
    (N13MumfordOrientedFullKummer.structuralKummer_eq_zero_iff_full_eq_one
      P).mp
        (N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial P)
  let hcoordinates :=
    (N13MumfordFullKummerIdentityFiber.orientedFullKummer_eq_one_iff_exists_coordinates
      P).mp hfull
  let β := Classical.choose hcoordinates
  let hq := Classical.choose_spec hcoordinates
  let q := Classical.choose hq
  have hcoordinates_spec := Classical.choose_spec hq
  let root :=
    N13MumfordFullKummerIdentityFiber.finiteIdealGraphRootData_of_full_gauge
      D β q hcoordinates_spec.1 hcoordinates_spec.2
  let finite :=
    N13MumfordFullKummerIdentityFiber.finiteIdealHalfData
      D root
  refine
    { representative := D
      representative_spec :=
        N13LowDegreeKummerHom.lowClass_representative P
      finite := finite
      double_eq := ?_ }
  exact
    (N13LowDegreeKummerHom.lowClass_representative P).symm.trans
      finite.half_spec

/-- Multiplication by two is surjective on the concrete N13 Picard group. -/
theorem twoSurjective :
    N13TwoAdicEndgame.TwoSurjective G := by
  intro P
  let D := constructedHalfData P
  exact ⟨D.finite.half, D.double_eq⟩

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
