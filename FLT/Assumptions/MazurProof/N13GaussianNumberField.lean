import FLT.Assumptions.MazurProof.N13GaussianCubicField
import FLT.Assumptions.MazurProof.N13GaussianFractionField
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The absolute N13 number field

The N13 Gaussian cubic is a degree-three extension of the quadratic
Gaussian field.  Combining the structural bases in the two stages gives
the six-element rational basis

`1, α, α², i, iα, iα²`.

This is a tower-basis construction; no embeddings or field elements are
enumerated.
-/

open Algebra Module

namespace MazurProof.N13GaussianNumberField

noncomputable section

open N13GaussianGlobalArithmetic

abbrev K := FractionRing GI

abbrev L := AdjoinRoot N13GaussianCubicField.hK

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

/-- The relative `K`-basis `(1, α, α²)`, with a fixed index type. -/
def relativeBasis : Basis (Fin 3) K L :=
  N13GaussianCubicField.powerBasis.basis.reindex
    (finCongr N13GaussianCubicField.powerBasis_dim)

@[simp] theorem relativeBasis_apply (j : Fin 3) :
    relativeBasis j =
      N13GaussianCubicField.alpha ^ (j : ℕ) := by
  rw [relativeBasis, Basis.reindex_apply,
    N13GaussianCubicField.powerBasis.basis_eq_pow]
  have hindex :
      (((finCongr
          N13GaussianCubicField.powerBasis_dim).symm j) :
        ℕ) = (j : ℕ) := rfl
  rw [hindex, N13GaussianCubicField.powerBasis_gen]

/-- The absolute tower basis
`1, α, α², i, iα, iα²`, indexed base-first. -/
def absoluteBasis : Basis (Fin 2 × Fin 3) ℚ L :=
  N13GaussianFractionField.gaussianBasis.smulTower
    relativeBasis

@[simp] theorem absoluteBasis_apply
    (ij : Fin 2 × Fin 3) :
    absoluteBasis ij =
      algebraMap K L
          (N13GaussianFractionField.gaussianBasis ij.1) *
        N13GaussianCubicField.alpha ^ (ij.2 : ℕ) := by
  rw [absoluteBasis, Basis.smulTower_apply,
    Algebra.smul_def, relativeBasis_apply]

instance finiteKL : Module.Finite K L :=
  N13GaussianCubicField.powerBasis.finite

instance finiteQL : Module.Finite ℚ L :=
  Module.Finite.trans K L

instance numberFieldL : NumberField L :=
  NumberField.of_module_finite K L

@[simp] theorem finrank_K_L :
    Module.finrank K L = 3 := by
  rw [Module.finrank_eq_card_basis relativeBasis]
  simp

@[simp] theorem finrank_Q_L :
    Module.finrank ℚ L = 6 := by
  rw [Module.finrank_eq_card_basis absoluteBasis]
  simp

/-- Independent tower-law check of the absolute degree. -/
theorem finrank_Q_L_tower :
    Module.finrank ℚ L =
      Module.finrank ℚ K * Module.finrank K L := by
  exact (Module.finrank_mul_finrank ℚ K L).symm

/-! ## The absolute ring of integers -/

/-- For an integral scalar extension `R → S`, integrality over `R` and
over `S` cut out the same subring in the top algebra. -/
theorem integralClosure_toSubring_eq_of_isIntegral
    {R S A : Type*}
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [Algebra.IsIntegral R S] :
    (integralClosure R A).toSubring =
      (integralClosure S A).toSubring := by
  ext x
  change IsIntegral R x ↔ IsIntegral S x
  constructor
  · exact IsIntegral.tower_top
  · intro hx
    exact isIntegral_trans x hx

/-- Absolute and Gaussian-relative integral elements in `L` have the same
underlying carrier. -/
theorem absoluteIntegralClosure_toSubring_eq :
    (integralClosure ℤ L).toSubring =
      (integralClosure GI L).toSubring :=
  integralClosure_toSubring_eq_of_isIntegral
    (R := ℤ) (S := GI) (A := L)

/-- Change only the proof that an element of `L` is integral. -/
def relativeToAbsoluteAddEquiv :
    integralClosure GI L ≃+ integralClosure ℤ L where
  toFun x := ⟨x.1, isIntegral_trans x.1 x.2⟩
  invFun x := ⟨x.1, x.2.tower_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl

/-- The same carrier change as an integer-linear equivalence. -/
def relativeToAbsoluteLinearEquiv :
    integralClosure GI L ≃ₗ[ℤ] integralClosure ℤ L :=
  relativeToAbsoluteAddEquiv.toIntLinearEquiv

/-- The absolute integral basis obtained by composing the Gaussian integral
basis with the relative cubic integral basis. -/
def absoluteIntegralBasis :
    Basis (Fin 2 × Fin 3) ℤ (integralClosure ℤ L) :=
  (N13GaussianFractionField.gaussianIntBasis.smulTower
      N13GaussianCubicField.relativeIntegralBasis).map
    relativeToAbsoluteLinearEquiv

@[simp] theorem coe_absoluteIntegralBasis_apply
    (ij : Fin 2 × Fin 3) :
    ((absoluteIntegralBasis ij :
        integralClosure ℤ L) : L) =
      algebraMap GI L
          (N13GaussianFractionField.gaussianIntBasis ij.1) *
        N13GaussianCubicField.alpha ^ (ij.2 : ℕ) := by
  simp [absoluteIntegralBasis, relativeToAbsoluteLinearEquiv,
    relativeToAbsoluteAddEquiv, Algebra.smul_def]

end

end MazurProof.N13GaussianNumberField
