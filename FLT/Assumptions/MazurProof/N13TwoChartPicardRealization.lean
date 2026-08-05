import FLT.Assumptions.MazurProof.N13SpecialDivisorCharts
import FLT.Assumptions.MazurProof.N13AbelFiberTwoModel
import FLT.Assumptions.MazurProof.SexticOrientedPic

/-!
# Two-fibre Picard realization of proper N13 lines

Mathlib does not currently descend the two chart ideals of a `TwoChartLine`
to a global invertible sheaf on the glued curve.  The N13 endgame needs less:
an oriented generic fractional ideal and a literal degree-two divisor on the
special fibre.

The structure in this file retains precisely that rigorous ring-level data.
Its two special equalities compare both reduced chart ideals with the
canonical chart pair of one effective divisor.  The generic and special
Picard classes are consequently definitions, rather than hypothesized class
maps.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13TwoChartPicardRealization

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Proper line data on the ordinary affine and infinity charts. -/
abbrev Line : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

/-- The two-adic coefficient field. -/
abbrev Q₂ : Type :=
  N13InfinityBaseChange.Q₂

/-- The good sextic N13 model over the two-adic field. -/
abbrev Model : SexticMumford.Model Q₂ :=
  N13Mumford.model Q₂

/-- The oriented generic Picard group used by the N13 Mumford model. -/
abbrev GenericPic : Type :=
  SexticMumford.ConcretePic
    Model
    (N13Infinity.positiveInfinityOrder Q₂)

/-- The set-valued special Picard model obtained from the Abel fibres. -/
abbrev SpecialPic : Type :=
  N13AbelFiberTwoModel.PicTwoSetModel

/-- Literal degree-two effective divisors on the completed special curve. -/
abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo

/-- Algebra structure used to extend an integral fractional ideal to the
generic sextic coordinate ring. -/
local instance integralRationalAlgebra :
    Algebra N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

/-- The common function field is the fraction field of the integral affine
coordinate ring. -/
local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Extension of the invertible affine ideal of a proper line to the generic
sextic coordinate ring. -/
def genericIdealUnit (L : Line) :
    Units N13IntegralFractionalHull.RationalFractionalIdeal :=
  Units.map
    N13IntegralFractionalHull.extendFractional.toMonoidHom
    L.affine_isUnit.unit

/-- Coercing the generic ideal unit to a fractional ideal recovers the
literal extension of the line's affine ideal.

This bridge is independent of the geometric origin of the proper line and is
therefore shared by point and quadratic Picard realizations. -/
@[simp] theorem coe_genericIdealUnit
    (L : Line) :
    (genericIdealUnit L :
        N13IntegralFractionalHull.RationalFractionalIdeal) =
      (Ideal.map
        N13IntegralFractionalHull.integralToRational
        L.affineIdeal :
        N13IntegralFractionalHull.RationalFractionalIdeal) := by
  change
    N13IntegralFractionalHull.extendFractional
        (L.affine_isUnit.unit :
          N13IntegralFractionalHull.IntegralFractionalIdeal) =
      _
  rw [L.affine_isUnit.unit_spec,
    N13IntegralFractionalHull.extendFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]

/-- Oriented generic fractional-ideal datum of a proper line.

The integer is explicit because the generic affine ideal alone cannot
distinguish the two points at infinity or record an infinity twist. -/
def genericRaw (L : Line) (infinityOrder : ℤ) :
    SexticMumford.OrientedFrac Model :=
  (genericIdealUnit L, Multiplicative.ofAdd infinityOrder)

/-- Equality of mapped generic affine ideals determines equality of their
packaged fractional-ideal units.

The statement retains the exact Mumford representative rather than passing
prematurely to the oriented Picard quotient. -/
theorem genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericIdealUnit L =
      SexticMumford.mumfordIdealUnit Model D.toSemi := by
  apply Units.ext
  rw [coe_genericIdealUnit,
    SexticMumford.coe_mumfordIdealUnit]
  exact
    congrArg
      (fun I : Ideal N13IntegralFractionalHull.RationalRing =>
        (I : N13IntegralFractionalHull.RationalFractionalIdeal))
      hmap

/-- A proper line with the exact Mumford affine ideal realizes the literal
oriented Mumford datum when marked by the representative's exponent
`nInf - 1`.

This is the generic-fibre bridge used uniformly by point and quadratic
two-chart realizations. -/
theorem genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericRaw L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D := by
  apply Prod.ext
  · exact
      genericIdealUnit_eq_mumfordIdealUnit_of_map_affineIdeal_eq
        L D hmap
  · rfl

/-- Oriented generic Picard class carried by a marked proper line. -/
def genericClass (L : Line) (infinityOrder : ℤ) :
    GenericPic :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (SexticMumford.principalOriented
        Model
        (N13Infinity.positiveInfinityOrder Q₂)).range
      (genericRaw L infinityOrder)

/-- Exact mapped-ideal equality also identifies the induced generic Picard
class with the standard oriented class of the Mumford representative. -/
theorem genericClass_eq_classOf_of_map_affineIdeal_eq
    (L : Line)
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    genericClass L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder Q₂)
        D := by
  unfold genericClass SexticMumford.classOf
  rw [genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq L D hmap]

/-- One proper line together with exact interpretations on both fibres.

The special equalities retain both chart ideals.  Thus the special divisor
cannot be chosen merely from the affine support while silently forgetting
which infinity sheet or infinity multiplicity the proper line carries. -/
structure Data where
  charts : Line
  infinityOrder : ℤ
  specialDivisor : EffectiveDivisorTwo
  special_affine :
    (N13TwoChartSpecialRestriction.restrict charts).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor specialDivisor).affineIdeal
  special_infinity :
    (N13TwoChartSpecialRestriction.restrict charts).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor specialDivisor).infinityIdeal

namespace Data

/-- The oriented generic class represented by the proper line. -/
def toGenericPic (D : Data) : GenericPic :=
  genericClass D.charts D.infinityOrder

/-- The special Abel class represented by the same proper line after
chartwise reduction. -/
def toSpecialPic (D : Data) : SpecialPic :=
  N13AbelFiberTwoModel.abel D.specialDivisor

/-- Both fibre classes, retained as a pair because the present special model
is a set quotient rather than an additive Picard group. -/
def fibreClasses (D : Data) : GenericPic × SpecialPic :=
  (D.toGenericPic, D.toSpecialPic)

end Data

end

end MazurProof.N13TwoChartPicardRealization
