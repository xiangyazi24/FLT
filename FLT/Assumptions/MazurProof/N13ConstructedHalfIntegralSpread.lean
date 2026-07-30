import FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective
import FLT.Assumptions.MazurProof.N13InfinityBaseChange
import FLT.Assumptions.MazurProof.N13SpecialProductLift

/-!
# The integral spread of the N13 constructed half

The proof of two-surjectivity selects a concrete invertible fractional-ideal
root over `ℚ`.  Base change sends that exact root to `ℚ₂`.  Multiplication by
its canonical fractional-ideal denominator produces an ordinary ideal, so
the existing contraction/divisorial-hull machinery applies without choosing
a different half.

The resulting hull has generic fibre equal to the selected root up to the
displayed principal denominator.  Its remaining integral invertibility
condition is exactly the existing three-product special trace lift.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13ConstructedHalfIntegralSpread

noncomputable section
open SexticMumford

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev G : Type :=
  N13MumfordFullKummerTwoSurjective.G

abbrev Q₂ : Type :=
  N13InfinityBaseChange.Q₂

abbrev Mℚ : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev M₂ : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

/-- Base change on invertible affine fractional ideals from `ℚ` to `ℚ₂`. -/
def invFracBaseChange :
    SexticMumford.InvFrac Mℚ →*
      SexticMumford.InvFrac M₂ :=
  SexticMumford.OrientedBaseChange.invFracMap
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (N13InfinityBaseChange.map_n13_f
      N13InfinityBaseChange.ratToQ₂)

/-- The exact Padé-selected ideal root, after coefficient extension to
`ℚ₂`. -/
def twoAdicIdealRoot (P : G) :
    SexticMumford.InvFrac M₂ :=
  invFracBaseChange
    (N13MumfordFullKummerTwoSurjective.constructedHalfData
      P).finite.idealRoot

/-- The selected root still satisfies its exact square identity after
two-adic coefficient extension. -/
theorem twoAdicIdealRoot_square (P : G) :
    invFracBaseChange
        (SexticMumford.mumfordIdealUnit Mℚ
              (N13MumfordFullKummerTwoSurjective.constructedHalfData
                P).representative.toSemi *
          toPrincipalIdeal
            (SexticMumford.CoordinateRing Mℚ)
            (SexticMumford.FunctionField Mℚ)
            (N13MumfordFullKummerTwoSurjective.constructedHalfData
              P).finite.principalCorrection) =
      twoAdicIdealRoot P ^ 2 := by
  rw [(N13MumfordFullKummerTwoSurjective.constructedHalfData
    P).finite.square_eq, map_pow]
  rfl

/-- The underlying two-adic generic fractional ideal. -/
def rootFractional (P : G) :
    RationalFractionalIdeal :=
  (twoAdicIdealRoot P : RationalFractionalIdeal)

/-- Clear the canonical denominator of the selected generic root.  This is
an ordinary ideal in the two-adic generic affine coordinate ring. -/
def rootIdeal (P : G) : Ideal RationalRing :=
  (rootFractional P).num

/-- Clearing the canonical denominator changes the selected root only by
the displayed principal fractional ideal. -/
theorem span_den_mul_rootFractional (P : G) :
    FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing)) *
        rootFractional P =
      (rootIdeal P : RationalFractionalIdeal) := by
  exact
    FractionalIdeal.den_mul_self_eq_num'
      RationalRing⁰ FunctionField (rootFractional P)

theorem rootFractional_isUnit (P : G) :
    IsUnit (rootFractional P) :=
  (twoAdicIdealRoot P).isUnit

private theorem root_den_ne_zero (P : G) :
    algebraMap RationalRing FunctionField
        ((rootFractional P).den : RationalRing) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective RationalRing FunctionField).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp
        (rootFractional P).den.property)

theorem rootIdeal_isUnit (P : G) :
    IsUnit (rootIdeal P : RationalFractionalIdeal) := by
  have hprincipal :
      IsUnit
        (FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing))) := by
    apply
      (FractionalIdeal.mul_inv_cancel_iff_isUnit
        FunctionField).mp
    exact
      FractionalIdeal.spanSingleton_mul_inv
        FunctionField (root_den_ne_zero P)
  rw [← span_den_mul_rootFractional P]
  exact hprincipal.mul (rootFractional_isUnit P)

theorem rootIdeal_ne_bot (P : G) :
    rootIdeal P ≠ ⊥ := by
  intro hzero
  have hfrac :
      (rootIdeal P : RationalFractionalIdeal) = 0 := by
    rw [hzero]
    rfl
  exact (rootIdeal_isUnit P).ne_zero hfrac

/-- The canonical integral divisorial spread of the exact constructed
half-root. -/
def integralRootHull (P : G) :
    N13IntegralFractionalHull.IntegralFractionalIdeal :=
  N13IntegralFractionalHull.divisorialHull (rootIdeal P)

/-- Its generic fibre is the denominator-cleared selected root. -/
theorem extend_integralRootHull (P : G) :
    N13IntegralFractionalHull.extendFractional
        (integralRootHull P) =
      (rootIdeal P : RationalFractionalIdeal) :=
  N13IntegralFractionalHull.extendFractional_divisorialHull_eq
    (rootIdeal_ne_bot P) (rootIdeal_isUnit P)

/-- Equivalently, the generic fibre is the actual Padé-selected root
multiplied by its explicit principal denominator. -/
theorem extend_integralRootHull_eq_principal_mul (P : G) :
    N13IntegralFractionalHull.extendFractional
        (integralRootHull P) =
      FractionalIdeal.spanSingleton RationalRing⁰
          (algebraMap RationalRing FunctionField
            ((rootFractional P).den : RationalRing)) *
        rootFractional P := by
  rw [extend_integralRootHull, span_den_mul_rootFractional]

/-- The remaining special-fibre obligation for this exact constructed
half: lift the three explicit special trace products into the contracted
root and its multiplier inverse. -/
abbrev SpecialProductLift (P : G) : Type :=
  N13SpecialProductLift.Data (rootIdeal P)

/-- That single special trace lift makes the integral spread invertible. -/
theorem integralRootHull_isUnit
    (P : G) (D : SpecialProductLift P) :
    IsUnit (integralRootHull P) :=
  D.isUnit_divisorialHull
    (rootIdeal_ne_bot P) (rootIdeal_isUnit P)

end

end MazurProof.N13ConstructedHalfIntegralSpread
