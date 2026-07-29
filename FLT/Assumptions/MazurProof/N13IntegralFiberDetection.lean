import FLT.Assumptions.MazurProof.N13IntegralFractionalHull
import FLT.Assumptions.MazurProof.N13GeneralizedMumfordReduction
import Mathlib.Algebra.Ring.GeomSum

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralFiberDetection

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

def integralToRational : IntegralRing →+* RationalRing :=
  N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  integralToRational.toAlgebra

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

def reduceCoordinate : IntegralRing →+* SpecialRing :=
  N13GeneralizedMumfordReduction.reduceCoordinate

/-- An integral ideal is the unit ideal as soon as both its vertical generic
fibre and its special fibre are the unit ideal.  A generic unit supplies one
nonzero two-adic scalar in the ideal; the DVR structure replaces it by a
power of two.  A special unit lifts to an element congruent to one modulo
two, and a finite geometric series combines the two witnesses. -/
theorem eq_top_of_generic_and_special_eq_top
    (I : Ideal IntegralRing)
    (hGeneric :
      Ideal.map integralToRational I = ⊤)
    (hSpecial :
      Ideal.map reduceCoordinate I = ⊤) :
    I = ⊤ := by
  have hGenericOne :
      algebraMap IntegralRing RationalRing 1 ∈
        Ideal.map (algebraMap IntegralRing RationalRing) I := by
    change integralToRational 1 ∈
      Ideal.map integralToRational I
    rw [hGeneric]
    simp
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    N13IntegralModelContraction.verticalScalars] at hGenericOne
  obtain ⟨m, hm, hmI⟩ := hGenericOne
  simp only [mul_one] at hmI
  change
    ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
      algebraMap R₂ IntegralRing r = m at hm
  obtain ⟨r, hr, rfl⟩ := hm
  have hr0 : r ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hr
  obtain ⟨n, hn⟩ :=
    PadicInt.ideal_eq_span_pow_p
      (s := Ideal.span ({r} : Set R₂))
      (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact hr0)
  have hpowSpan :
      (2 : R₂) ^ n ∈
        Ideal.span ({r} : Set R₂) := by
    rw [hn]
    exact Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at hpowSpan
  obtain ⟨c, hc⟩ := hpowSpan
  have htwoPow :
      algebraMap R₂ IntegralRing ((2 : R₂) ^ n) ∈ I := by
    rw [hc, map_mul]
    exact I.mul_mem_right _ hmI
  have hSpecialOne :
      (1 : SpecialRing) ∈
        Ideal.map reduceCoordinate I := by
    rw [hSpecial]
    simp
  rw [Ideal.mem_map_iff_of_surjective
    reduceCoordinate
    N13GeneralizedMumfordReduction.reduceCoordinate_surjective] at hSpecialOne
  obtain ⟨q, hqI, hqOne⟩ := hSpecialOne
  have hqSub :
      q - 1 ∈ RingHom.ker reduceCoordinate := by
    rw [RingHom.mem_ker, map_sub, hqOne, map_one, sub_self]
  change
    q - 1 ∈
      RingHom.ker
        N13GeneralizedMumfordReduction.reduceCoordinate at hqSub
  rw [N13GeneralizedMumfordReduction.ker_reduceCoordinate,
    Ideal.mem_span_singleton] at hqSub
  obtain ⟨a, ha⟩ := hqSub
  have hq :
      q =
        1 + algebraMap R₂ IntegralRing (2 : R₂) * a := by
    calc
      q = (q - 1) + 1 := by ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) * a + 1 := by
        rw [ha]
      _ = 1 + algebraMap R₂ IntegralRing (2 : R₂) * a := by
        ring
  let x : IntegralRing :=
    -(algebraMap R₂ IntegralRing (2 : R₂) * a)
  have hxPow : x ^ n ∈ I := by
    have hbase :
        (algebraMap R₂ IntegralRing (2 : R₂)) ^ n ∈ I := by
      simpa only [map_pow] using htwoPow
    have hmul :=
      I.mul_mem_right ((-a) ^ n) hbase
    change
      (-(algebraMap R₂ IntegralRing (2 : R₂) * a)) ^ n ∈ I
    rw [show
      -(algebraMap R₂ IntegralRing (2 : R₂) * a) =
        algebraMap R₂ IntegralRing (2 : R₂) * (-a) by ring,
      mul_pow]
    exact hmul
  have hqAs :
      1 - x = q := by
    dsimp only [x]
    rw [hq]
    ring
  have hOneSub : 1 - x ^ n ∈ I := by
    rw [← geom_sum_mul_neg x n, hqAs]
    exact I.mul_mem_left _ hqI
  rw [Ideal.eq_top_iff_one]
  have hadd := I.add_mem hOneSub hxPow
  simpa using hadd

/-- The remaining obstruction to invertibility is purely special-fibre:
once the defect ideal maps onto the special ring, generic invertibility and
the fibre-detection theorem force it to be the unit ideal. -/
theorem isUnit_of_map_defectIdeal_eq_top
    {H : N13IntegralFractionalHull.IntegralFractionalIdeal}
    (hH : H ≠ 0)
    (hGeneric :
      IsUnit
        (N13IntegralFractionalHull.extendFractional H))
    (hSpecial :
      Ideal.map reduceCoordinate
        (N13IntegralFractionalHull.defectIdeal H) = ⊤) :
    IsUnit H := by
  have hDefect :
      N13IntegralFractionalHull.defectIdeal H = ⊤ :=
    eq_top_of_generic_and_special_eq_top
      (N13IntegralFractionalHull.defectIdeal H)
      (N13IntegralFractionalHull.map_defectIdeal_eq_top
        hH hGeneric)
      hSpecial
  exact
    N13IntegralFractionalHull.isUnit_of_defectIdeal_eq_top
      hDefect

end

end MazurProof.N13IntegralFiberDetection
