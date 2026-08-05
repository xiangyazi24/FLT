import FLT.Assumptions.MazurProof.N13SplitQuadraticSpecialRestriction
import FLT.Assumptions.MazurProof.N13TwoChartPicardRealization

/-!
# Picard realization of split quadratic N13 graphs

The split and repeated-root constructors already produce a proper line with
the exact generic quadratic Mumford ideal and the exact two chart ideals of a
literal special divisor.  Marking that line by the representative's oriented
exponent `nInf - 1` therefore fills every field of the two-fibre Picard
realization.

This file performs only that semantic packaging.  In particular, it does not
alter the vanishing-ideal convention or infer a divisor sign from support.
-/

namespace MazurProof.N13SplitQuadraticPicardRealization

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The good sextic model over the two-adic field. -/
abbrev Model : SexticMumford.Model
    N13TwoChartPicardRealization.Q₂ :=
  N13TwoChartPicardRealization.Model

/-- Proper two-chart lines on the integral good model. -/
abbrev Line : Type :=
  N13TwoChartPicardRealization.Line

/-- Literal effective degree-two divisors on the completed special fibre. -/
abbrev EffectiveDivisorTwo : Type :=
  N13TwoChartPicardRealization.EffectiveDivisorTwo

/-- Package one proper line and its two exact special chart comparisons as
two-fibre Picard data for a chosen Mumford representative.

The generic affine ideal equality is not needed to construct the data; it is
consumed separately to identify the resulting generic class. -/
def dataOfSpecialRealization
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal) :
    N13TwoChartPicardRealization.Data where
  charts := L
  infinityOrder := (D.nInf : ℤ) - 1
  specialDivisor := Δ
  special_affine := haffine
  special_infinity := hinfinity

/-- Exact generic affine-ideal equality identifies the raw generic datum of
`dataOfSpecialRealization` with the literal Mumford raw datum. -/
theorem dataOfSpecialRealization_genericRaw_eq_mumfordRaw
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    N13TwoChartPicardRealization.genericRaw
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).charts
        (dataOfSpecialRealization
          D L Δ haffine hinfinity).infinityOrder =
      SexticMumford.mumfordRaw Model D := by
  change
    N13TwoChartPicardRealization.genericRaw
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.mumfordRaw Model D
  exact
    N13TwoChartPicardRealization.genericRaw_eq_mumfordRaw_of_map_affineIdeal_eq
      L D hmap

/-- The generic Picard class of the packaged realization is the standard
oriented class of the same Mumford representative. -/
theorem dataOfSpecialRealization_toGenericPic_eq_classOf
    (D : SexticMumford.Mumford Model)
    (L : Line)
    (Δ : EffectiveDivisorTwo)
    (haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal)
    (hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal)
    (hmap :
      Ideal.map
          N13IntegralFractionalHull.integralToRational
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v) :
    (dataOfSpecialRealization
      D L Δ haffine hinfinity).toGenericPic =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D := by
  change
    N13TwoChartPicardRealization.genericClass
        L ((D.nInf : ℤ) - 1) =
      SexticMumford.classOf
        Model
        (N13Infinity.positiveInfinityOrder
          N13TwoChartPicardRealization.Q₂)
        D
  exact
    N13TwoChartPicardRealization.genericClass_eq_classOf_of_map_affineIdeal_eq
      L D hmap

/-- A distinct-root quadratic Mumford graph admits complete two-fibre Picard
data with its literal generic class and an explicit reduced secant divisor. -/
theorem exists_data_of_distinct_split
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity⟩ :=
    N13SplitQuadraticSpecialRestriction.exists_twoChartLine_and_specialDivisor_of_distinct_split
      D hdeg x₁ x₂ hfactor hneq
  let R :=
    dataOfSpecialRealization D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_⟩
  · exact
      dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap

/-- A repeated-root quadratic Mumford graph admits complete two-fibre Picard
data whose special divisor retains the doubled reduced point. -/
theorem exists_data_of_repeated_root
    (D : SexticMumford.Mumford Model)
    (x : N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity⟩ :=
    N13SplitQuadraticSpecialRestriction.exists_twoChartLine_and_specialDivisor_of_repeated_root
      D x hfactor
  let R :=
    dataOfSpecialRealization D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_⟩
  · exact
      dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap

end

end MazurProof.N13SplitQuadraticPicardRealization
