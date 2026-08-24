import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneFunctionField
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The separable quartic over `F₂(z)`

The plane projection polynomial is a monic irreducible quartic over
`F₂[z]`.  This file transports it to the rational function field and checks
separability from its explicit nonzero derivative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneQuarticSeparable

open Polynomial
open RationalPointsN25QuotientTwoPlaneFunctionField

local notation "k₂" => ZMod 2
local notation "Rz" => Polynomial k₂
local notation "Fz" => RatFunc k₂

/-- The outer degree of the plane polynomial is four. -/
theorem planeSexticPolynomial_natDegree :
    planeSexticPolynomial.natDegree = 4 := by
  unfold planeSexticPolynomial
  compute_degree!

/-- The formal derivative with respect to the outer `x` variable. -/
theorem planeSexticPolynomial_derivative :
    planeSexticPolynomial.derivative =
      C (X ^ 3 + 1) * X ^ 2 + C (X ^ 4) := by
  simp [planeSexticPolynomial, derivative_add, derivative_mul,
    derivative_pow]
  have htwo : (2 : Rz) = 0 := CharP.cast_eq_zero Rz 2
  have hthree : (3 : Rz) = 1 := by linear_combination htwo
  have hfour : (4 : Rz) = 0 := by linear_combination 2 * htwo
  rw [htwo, hthree, hfour]
  simp

/-- The quartic derivative is nonzero already over `F₂[z]`. -/
theorem planeSexticPolynomial_derivative_ne_zero :
    planeSexticPolynomial.derivative ≠ 0 := by
  rw [planeSexticPolynomial_derivative]
  intro h
  have hzero := congrArg (Polynomial.eval (0 : Rz)) h
  have hx : (X : Rz) ^ 4 ≠ 0 := pow_ne_zero 4 Polynomial.X_ne_zero
  exact hx (by simpa using hzero)

/-- The same quartic after extending coefficients from `F₂[z]` to
`F₂(z)`. -/
def planeQuarticRatFunc : Fz[X] :=
  planeSexticPolynomial.map (algebraMap Rz Fz)

theorem planeQuarticRatFunc_monic : planeQuarticRatFunc.Monic :=
  planeSexticPolynomial_monic.map (algebraMap Rz Fz)

/-- Gauss's lemma preserves irreducibility in the rational function field. -/
theorem planeQuarticRatFunc_irreducible :
    Irreducible planeQuarticRatFunc := by
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := Fz) planeSexticPolynomial_monic).mp
      planeSexticPolynomial_irreducible

/-- The derivative remains nonzero after passing to `F₂(z)`. -/
theorem planeQuarticRatFunc_derivative_ne_zero :
    planeQuarticRatFunc.derivative ≠ 0 := by
  rw [planeQuarticRatFunc, derivative_map,
    planeSexticPolynomial_derivative]
  intro h
  have hzero := congrArg (Polynomial.eval (0 : Fz)) h
  have hx : (RatFunc.X : Fz) ^ 4 ≠ 0 :=
    pow_ne_zero 4 RatFunc.X_ne_zero
  exact hx (by simpa using hzero)

/-- The quartic defining the generic fiber is separable over `F₂(z)`. -/
theorem planeQuarticRatFunc_separable :
    planeQuarticRatFunc.Separable :=
  (Polynomial.separable_iff_derivative_ne_zero
    planeQuarticRatFunc_irreducible).2
      planeQuarticRatFunc_derivative_ne_zero

/-- The generic quartic algebra used before comparison with the existing
plane function field. -/
abbrev PlaneQuarticField := AdjoinRoot planeQuarticRatFunc

instance planeQuarticRatFunc_irreducibleFact :
    Fact (Irreducible planeQuarticRatFunc) :=
  ⟨planeQuarticRatFunc_irreducible⟩

instance planeQuarticField_isField : Field PlaneQuarticField := inferInstance

/-- The generic quartic algebra has dimension four over `F₂(z)`. -/
theorem planeQuarticField_finrank :
    Module.finrank Fz PlaneQuarticField = 4 := by
  rw [(AdjoinRoot.powerBasis planeQuarticRatFunc_irreducible.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, planeQuarticRatFunc,
    natDegree_map_eq_of_injective]
  · exact planeSexticPolynomial_natDegree
  · exact IsFractionRing.injective Rz Fz

/-- The adjoined generic root is separable over `F₂(z)`. -/
theorem planeQuarticField_root_isSeparable :
    IsSeparable Fz (AdjoinRoot.root planeQuarticRatFunc) := by
  unfold IsSeparable
  rw [AdjoinRoot.minpoly_root planeQuarticRatFunc_irreducible.ne_zero,
    planeQuarticRatFunc_monic.leadingCoeff, inv_one, map_one, mul_one]
  exact planeQuarticRatFunc_separable

/-- The generic quartic field is a separable extension of `F₂(z)`. -/
instance planeQuarticField_isSeparable :
    Algebra.IsSeparable Fz PlaneQuarticField := by
  let hadjoin : Algebra.IsSeparable Fz
      (IntermediateField.adjoin Fz
        {AdjoinRoot.root planeQuarticRatFunc}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      Fz PlaneQuarticField).2
      planeQuarticField_root_isSeparable
  have htop : IntermediateField.adjoin Fz
      {AdjoinRoot.root planeQuarticRatFunc} =
      (⊤ : IntermediateField Fz PlaneQuarticField) :=
    IntermediateField.adjoin_root_eq_top planeQuarticRatFunc
  letI : Algebra.IsSeparable Fz
      (⊤ : IntermediateField Fz PlaneQuarticField) := htop ▸ hadjoin
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv :
      (⊤ : IntermediateField Fz PlaneQuarticField) ≃ₐ[Fz]
        PlaneQuarticField)

end MazurProof.RationalPointsN25QuotientTwoPlaneQuarticSeparable
