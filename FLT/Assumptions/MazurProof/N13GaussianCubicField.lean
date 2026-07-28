import FLT.Assumptions.MazurProof.IntegralClosureOfEisensteinDiscr
import FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic
import FLT.Assumptions.MazurProof.PowerBasisDiscriminant

/-!
# The global N13 Gaussian cubic field

We form the fraction field `K = Frac(ℤ[i])` and adjoin a root of the
translated Gaussian cubic.  Its Eisenstein property proves irreducibility,
while the discriminant--Eisenstein criterion identifies the monogenic
Gaussian order with the full relative integral closure.

This file contains no class-group computation and no integral-basis search.
-/

open Algebra Module Polynomial

namespace MazurProof.N13GaussianCubicField

noncomputable section

open N13GaussianGlobalArithmetic

/-- The Gaussian rational field, kept as the literal fraction field of
`GaussianInt` so the integral-closure API applies definitionally. -/
abbrev K := FractionRing GI

/-- The translated cubic over the Gaussian rational field. -/
def hK : K[X] :=
  h.map (algebraMap GI K)

theorem hK_monic : hK.Monic :=
  h_monic.map (algebraMap GI K)

/-- Eisenstein gives irreducibility already over `ℤ[i]`. -/
theorem h_irreducible : Irreducible h :=
  h_eisenstein.irreducible pi_span_prime h_monic.isPrimitive
    (by rw [h_natDegree]; norm_num)

/-- Gauss's lemma transports the structural Eisenstein proof to the
Gaussian fraction field. -/
theorem hK_irreducible : Irreducible hK := by
  exact
    h_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      h_irreducible

@[reducible] def hKIrreducibleFact :
    Fact (Irreducible hK) :=
  ⟨hK_irreducible⟩

/-- The relative cubic field. -/
abbrev L := AdjoinRoot hK

/-- Exported opt-in field structure for downstream arithmetic files. -/
@[reducible] noncomputable def cubicField : Field L := by
  letI := hKIrreducibleFact
  infer_instance

local instance : Fact (Irreducible hK) :=
  hKIrreducibleFact

local instance fieldL : Field L :=
  AdjoinRoot.instField

/-- The shifted cubic generator. -/
def alpha : L :=
  AdjoinRoot.root hK

/-- The relative power basis `1, α, α²`. -/
def powerBasis : PowerBasis K L :=
  AdjoinRoot.powerBasis hK_monic.ne_zero

local instance finiteKL : Module.Finite K L :=
  powerBasis.finite

local instance separableKL : Algebra.IsSeparable K L :=
  inferInstance

@[simp] theorem powerBasis_gen :
    powerBasis.gen = alpha := by
  rfl

theorem powerBasis_dim :
    powerBasis.dim = 3 := by
  rw [powerBasis, AdjoinRoot.powerBasis_dim]
  rw [hK, h_monic.natDegree_map]
  exact h_natDegree

/-- The shifted generator is integral over the Gaussian integers. -/
theorem alpha_integral : IsIntegral GI alpha := by
  refine ⟨h, h_monic, ?_⟩
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  change h.eval₂ (algebraMap GI L) alpha = 0
  rw [hmap]
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root hK

/-- The integral minimal polynomial is exactly the translated cubic. -/
theorem minpoly_alpha :
    minpoly GI alpha = h := by
  apply Polynomial.map_injective
    (f := algebraMap GI K)
    (FaithfulSMul.algebraMap_injective GI K)
  calc
    (minpoly GI alpha).map (algebraMap GI K) =
        minpoly K alpha :=
      (minpoly.isIntegrallyClosed_eq_field_fractions'
        K alpha_integral).symm
    _ = hK := by
      change minpoly K (AdjoinRoot.root hK) = hK
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hK_monic
    _ = h.map (algebraMap GI K) := rfl

/-- Relative trace discriminant of the shifted power basis. -/
theorem powerBasis_discr :
    Algebra.discr K powerBasis.basis =
      algebraMap GI K (pi ^ 2) := by
  exact
    PowerBasisDiscriminant.powerBasis_discr_eq_map_discr
      powerBasis alpha_integral h minpoly_alpha
      |>.trans (congrArg (algebraMap GI K) h_discr)

/-- The monogenic Gaussian order is the full relative integral closure. -/
theorem integralClosure_eq_adjoin :
    integralClosure GI L =
      Algebra.adjoin GI ({alpha} : Set L) := by
  apply integralClosure_eq_adjoin_of_discr_eq_prime_pow
    (B := powerBasis) (p := pi) (n := 2)
  · exact pi_prime
  · simpa [powerBasis_gen] using alpha_integral
  · exact powerBasis_discr
  · simpa [powerBasis_gen, minpoly_alpha] using h_eisenstein

/-! ## The relative integral basis -/

local instance faithfulGIL : FaithfulSMul GI L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply IsFractionRing.injective GI K
  apply (algebraMap K L).injective
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  rw [hmap] at hxy
  exact hxy

/-- The power basis on the generated Gaussian order, transported to the
proved relative integral closure. -/
def relativeIntegralPowerBasis :
    PowerBasis GI (integralClosure GI L) :=
  (Algebra.adjoin.powerBasis' (R := GI) alpha_integral).map
    (Subalgebra.equivOfEq _ _
      integralClosure_eq_adjoin.symm)

@[simp] theorem relativeIntegralPowerBasis_dim :
    relativeIntegralPowerBasis.dim = 3 := by
  simp [relativeIntegralPowerBasis, minpoly_alpha,
    h_natDegree]

@[simp] theorem coe_relativeIntegralPowerBasis_gen :
    ((relativeIntegralPowerBasis.gen :
        integralClosure GI L) : L) = alpha := by
  simp [relativeIntegralPowerBasis]

/-- The literal relative integral basis `(1, α, α²)`. -/
def relativeIntegralBasis :
    Basis (Fin 3) GI (integralClosure GI L) :=
  relativeIntegralPowerBasis.basis.reindex
    (finCongr relativeIntegralPowerBasis_dim)

@[simp] theorem coe_relativeIntegralBasis_apply
    (j : Fin 3) :
    ((relativeIntegralBasis j :
        integralClosure GI L) : L) =
      alpha ^ (j : ℕ) := by
  rw [relativeIntegralBasis, Basis.reindex_apply,
    relativeIntegralPowerBasis.basis_eq_pow]
  have hindex :
      (((finCongr relativeIntegralPowerBasis_dim).symm j) :
        ℕ) = (j : ℕ) := rfl
  change
    ((relativeIntegralPowerBasis.gen :
      integralClosure GI L) : L) ^
        (((finCongr relativeIntegralPowerBasis_dim).symm j) :
          ℕ) =
      alpha ^ (j : ℕ)
  rw [coe_relativeIntegralPowerBasis_gen]
  rw [hindex]

@[simp] theorem coe_relativeIntegralBasis_zero :
    ((relativeIntegralBasis 0 :
        integralClosure GI L) : L) = 1 := by
  simp

@[simp] theorem coe_relativeIntegralBasis_one :
    ((relativeIntegralBasis 1 :
        integralClosure GI L) : L) = alpha := by
  simp

@[simp] theorem coe_relativeIntegralBasis_two :
    ((relativeIntegralBasis 2 :
        integralClosure GI L) : L) = alpha ^ 2 := by
  simp

end

end MazurProof.N13GaussianCubicField
