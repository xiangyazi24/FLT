import FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare
import FLT.Assumptions.MazurProof.N13GoodOrderSquareToCount
import FLT.Assumptions.MazurProof.N13GaussianNumberField

/-!
# Good-prime parity of normalized N13 Kummer values

The homogeneous Mumford relation gives a square ideal in the order obtained
by inverting its denominator scale and derivative.  This file specializes
the generic DVR bridge to the N13 maximal order: at every height-one prime
avoiding that single bad generator, the normalized Kummer principal-ideal
count is even.
-/

open scoped nonZeroDivisors

open IsDedekindDomain

namespace MazurProof.N13GlobalKummerGoodPrimeParity

noncomputable section

open N13GlobalKummerIdealSquare
open N13GlobalKummerNormalization
open GoodOrderSquareToCount

abbrev L : Type :=
  N13GlobalKummerIdealSquare.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O : Type :=
  N13GlobalKummerIdealSquare.O

local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L

local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O

abbrev AtPrime (P : HeightOneSpectrum O) : Type :=
  P.valuationSubringAtPrime L

/-- At a prime avoiding the denominator-and-different generator, the
normalized Kummer value has even height-one count in the maximal order. -/
theorem normalizedKummerInteger_count_even_of_not_mem_badGenerator
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hgood : badGenerator D ∉ P.asIdeal) :
    Even
      (FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          ((normalizedKummerInteger D : O) : L))) := by
  letI : P.asIdeal.IsPrime := P.isPrime

  let ρ : O →+* AtPrime P :=
    algebraMap O (AtPrime P)

  have hd : IsUnit (ρ (badGenerator D)) := by
    apply
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (AtPrime P) P.asIdeal (badGenerator D)).2
    exact hgood

  have hEven :=
    even_principalCount_of_away_ideal_sq
      (O := O) (L := L) (A := O)
      (badGenerator D) P ρ hd
      (goodBranchIdeal D)
      (algebraMap O (GoodOrder D)
        (normalizedKummerInteger D))
      (goodBranchIdeal_sq D)

  have himage :
      (((awayToAtPrime
          (badGenerator D) P ρ hd
          (algebraMap O (GoodOrder D)
            (normalizedKummerInteger D)) :
            AtPrime P) : L)) =
        ((normalizedKummerInteger D : O) : L) := by
    rw [awayToAtPrime_algebraMap]
    rfl

  rw [himage] at hEven
  simpa only [principalCount] using hEven

end

end MazurProof.N13GlobalKummerGoodPrimeParity
