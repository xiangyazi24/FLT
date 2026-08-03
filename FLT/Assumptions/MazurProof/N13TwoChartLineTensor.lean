import FLT.Assumptions.MazurProof.N13EscapingDegreeOneSpread

/-!
# Tensor products of explicit N13 two-chart lines

The ordinary affine and infinity presentations of a line multiply
chartwise.  Ideal extension commutes with multiplication, so the overlap
compatibility is preserved.  This turns the explicit escaping point lines
into proper spreads of split effective divisors without constructing a
Picard functor.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13TwoChartLineTensor

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal

abbrev InfinityFractionalIdeal : Type :=
  N13IntegralInfinityPointSpread.InfinityFractionalIdeal

local instance integralRationalAlgebra :
    Algebra N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing N13IntegralGraphJacobian.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

/-- Tensor product in the explicit two-chart presentation. -/
def tensor (L M : TwoChartLine) : TwoChartLine where
  affineIdeal := L.affineIdeal * M.affineIdeal
  infinityIdeal := L.infinityIdeal * M.infinityIdeal
  affine_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.affine_isUnit.mul M.affine_isUnit
  infinity_isUnit := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact L.infinity_isUnit.mul M.infinity_isUnit
  overlap_eq := by
    rw [Ideal.map_mul, Ideal.map_mul, L.overlap_eq, M.overlap_eq]

@[simp] theorem tensor_affineIdeal (L M : TwoChartLine) :
    (tensor L M).affineIdeal =
      L.affineIdeal * M.affineIdeal :=
  rfl

@[simp] theorem tensor_infinityIdeal (L M : TwoChartLine) :
    (tensor L M).infinityIdeal =
      L.infinityIdeal * M.infinityIdeal :=
  rfl

theorem map_tensor_affineIdeal
    (L M : TwoChartLine) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (tensor L M).affineIdeal =
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          M.affineIdeal := by
  rw [tensor_affineIdeal, Ideal.map_mul]

/-- The linear graph through two points with distinct horizontal
coordinates. -/
def secantV
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    N13EscapingDegreeOneSpread.Q₂[X] :=
  C z₁ +
    C ((z₂ - z₁) * (x₂ - x₁)⁻¹) * (X - C x₁)

@[simp] theorem secantV_eval_left
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₁ = z₁ := by
  simp [secantV]

@[simp] theorem secantV_eval_right
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    (secantV x₁ z₁ x₂ z₂).eval x₂ = z₂ := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  simp [secantV, hd]

private theorem linearFactors_coprime
    (x₁ x₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    ∃ a b : N13EscapingDegreeOneSpread.Q₂[X],
      a * (X - C x₁) + b * (X - C x₂) = 1 := by
  have hd : x₂ - x₁ ≠ 0 :=
    sub_ne_zero.mpr hneq.symm
  refine
    ⟨C ((x₂ - x₁)⁻¹), -C ((x₂ - x₁)⁻¹), ?_⟩
  calc
    C ((x₂ - x₁)⁻¹) * (X - C x₁) +
          -C ((x₂ - x₁)⁻¹) * (X - C x₂) =
        C ((x₂ - x₁)⁻¹) * C (x₂ - x₁) := by
      rw [map_sub]
      ring
    _ = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd, map_one]

/-- The product of two distinct point graphs is the quadratic graph of
their secant interpolant. -/
theorem pointIdeal_mul_eq_secantGraph
    (x₁ z₁ x₂ z₂ : N13EscapingDegreeOneSpread.Q₂)
    (hneq : x₁ ≠ x₂) :
    SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₁) (C z₁) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - C x₂) (C z₂) =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - C x₁) * (X - C x₂))
        (secantV x₁ z₁ x₂ z₂) := by
  have h₁ :
      X - C x₁ ∣ secantV x₁ z₁ x₂ z₂ - C z₁ := by
    simpa using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₁))
  have h₂ :
      X - C x₂ ∣ secantV x₁ z₁ x₂ z₂ - C z₂ := by
    simpa [secantV_eval_right x₁ z₁ x₂ z₂ hneq] using
      (X_sub_C_dvd_sub_C_eval
        (p := secantV x₁ z₁ x₂ z₂) (a := x₂))
  simpa [SexticMumford.mumfordIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    SexticMumford.ySubClass,
    GeneralizedGraphIdealCore.ySubClass,
    SexticMumford.xClassHom_apply] using
      (GeneralizedGraphIdealCore.graphIdeal_mul_of_coprime
        (SexticMumford.xClassHom
          N13EscapingDegreeOneSpread.Model)
        (SexticMumford.yClass
          N13EscapingDegreeOneSpread.Model)
        (X - C x₁) (X - C x₂) (C z₁) (C z₂)
        (secantV x₁ z₁ x₂ z₂)
        h₁ h₂ (linearFactors_coprime x₁ x₂ hneq))

/-- Tensor the proper lines of two escaping affine points. -/
def nonintegralPointPairLine
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    TwoChartLine :=
  tensor
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x₁ y₁ hx₁ hcurve₁)
    (N13IntegralInfinityPointSpread.nonintegralPointLine
      x₂ y₂ hx₂ hcurve₂)

/-- The generic affine ideal of the pair line is exactly the product of
the two standard sextic point ideals. -/
theorem map_nonintegralPointPairLine_affineIdeal
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (nonintegralPointPairLine
          x₁ y₁ x₂ y₂ hx₁ hcurve₁ hx₂ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - Polynomial.C x₁)
          (Polynomial.C
            (N13EscapingDegreeOneSpread.pointY x₁ y₁)) *
        SexticMumford.mumfordIdeal
          N13EscapingDegreeOneSpread.Model
          (X - Polynomial.C x₂)
          (Polynomial.C
            (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [nonintegralPointPairLine, map_tensor_affineIdeal]
  change
    Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityPointSpread.affinePointIdeal
            (N13EscapingDegreeOneSpread.lift x₁ y₁ hx₁ hcurve₁)) *
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityPointSpread.affinePointIdeal
            (N13EscapingDegreeOneSpread.lift x₂ y₂ hx₂ hcurve₂)) =
      _
  rw [
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint,
    N13EscapingDegreeOneSpread.genericIdeal_eq_standardPoint]

/-- With distinct horizontal coordinates, the generic fibre of the pair
line is one quadratic Mumford graph, not merely an ideal product. -/
theorem map_nonintegralPointPairLine_eq_secantGraph
    (x₁ y₁ x₂ y₂ : N13EscapingDegreeOneSpread.Q₂)
    (hx₁ : x₁.valuation < 0)
    (hcurve₁ : N13GoodModelTwo.AffineEquation x₁ y₁)
    (hx₂ : x₂.valuation < 0)
    (hcurve₂ : N13GoodModelTwo.AffineEquation x₂ y₂)
    (hneq : x₁ ≠ x₂) :
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (nonintegralPointPairLine
          x₁ y₁ x₂ y₂ hx₁ hcurve₁ hx₂ hcurve₂).affineIdeal =
      SexticMumford.mumfordIdeal
        N13EscapingDegreeOneSpread.Model
        ((X - C x₁) * (X - C x₂))
        (secantV
          x₁ (N13EscapingDegreeOneSpread.pointY x₁ y₁)
          x₂ (N13EscapingDegreeOneSpread.pointY x₂ y₂)) := by
  rw [map_nonintegralPointPairLine_affineIdeal,
    pointIdeal_mul_eq_secantGraph _ _ _ _ hneq]

end

end MazurProof.N13TwoChartLineTensor
