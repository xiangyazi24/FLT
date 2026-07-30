import FLT.Assumptions.MazurProof.N13RankTwoIdealRecovery
import FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis

/-!
# Recovering the integral N13 graph from the concrete two-fibre basis

The literal basis `{1,x}` turns multiplication by `x` into a monic
characteristic polynomial of degree two.  Expressing the quotient class of
`y` in that basis then recovers the canonical contraction literally as a
generalized Mumford graph ideal.
-/

open Module
open Polynomial

namespace MazurProof.N13ConcreteGraphRecovery

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

/-- The integral affine `y` coordinate. -/
def integralY : IntegralRing :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)

/-- Evaluation at the integral affine `x` coordinate is the coordinate
embedding of the polynomial subring. -/
@[simp] theorem aeval_integralX (p : R₂[X]) :
    aeval N13CanonicalContractionQuotient.integralX p =
      N13GeneralizedMumfordIntegral.xClass (R := R₂) p := by
  change
    aeval
        (algebraMap R₂[X] IntegralRing X) p =
      algebraMap R₂[X] IntegralRing p
  simpa using
    aeval_algebraMap_apply IntegralRing
      (X : R₂[X]) p

/-- The integral affine ring has polynomial normal form in `x,y`. -/
theorem integral_rankTwoPolynomialNormalForm :
    N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
      (R := R₂)
      N13CanonicalContractionQuotient.integralX integralY := by
  intro z
  refine
    ⟨N13GeneralizedMumfordIntegral.coeff0 z,
      N13GeneralizedMumfordIntegral.coeffY z, ?_⟩
  rw [aeval_integralX, aeval_integralX]
  exact
    (N13GeneralizedMumfordIntegral.recompose z).symm

/-- The remaining special-ideal equality forces the canonical contraction
to be a literal monic quadratic graph ideal. -/
theorem exists_integral_graph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ u v : R₂[X],
      u.Monic ∧
      u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let xbar : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let ybar : B :=
    Ideal.Quotient.mk I integralY
  obtain ⟨b, hb⟩ :=
    N13TwoFiberConcreteBasis.exists_contractQuotient_basis
      D hdeg hmap
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily] using h
  have hb1 : b 1 = xbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily, xbar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hy⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
        xbar ybar b hb0 hb1
  let u : R₂[X] :=
    (Algebra.lmul R₂ B xbar).charpoly
  let v : R₂[X] :=
    C a + C c * X
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x xbar
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
        xbar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
          xbar b hb0 hb1
  have hyv : ybar = aeval xbar v := by
    calc
      ybar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * xbar := hy
      _ = aeval xbar v := by
        simp [v]
  have hI :=
    N13RankTwoIdealRecovery.ideal_eq_span_aeval_y_sub
      (R := R₂)
      N13CanonicalContractionQuotient.integralX
      integralY I u v
      integral_rankTwoPolynomialNormalForm hker hyv
  refine ⟨u, v, huMonic, huDegree, ?_⟩
  change I =
    N13GeneralizedMumfordIntegral.mumfordIdeal
      (R := R₂) u v
  simpa [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.ySubClass,
    integralY,
    aeval_integralX] using hI

end

end MazurProof.N13ConcreteGraphRecovery
