import FLT.Assumptions.MazurProof.N13RankTwoQuotientAlgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.LocalRing.Module

/-!
# Lifting the literal special-fibre basis `{1,x}`

For a finite flat algebra over a local ring, a family whose residue-field
base change is a basis is already a basis over the local ring.  This file
specializes the structural local lifting theorem to the literal family
`{1,x}` needed by the N13 quotient.
-/

open scoped TensorProduct
open Module

namespace MazurProof.N13FiniteFlatBasisLift

noncomputable section

universe uR uB

variable {R : Type uR} {B : Type uB}
variable [CommRing R] [IsLocalRing R]
variable [CommRing B] [Algebra R B]
variable [Module.Finite R B] [Module.Flat R B]

local notation "k" => IsLocalRing.ResidueField R

/-- The literal two-element family. -/
def oneX (x : B) : Fin 2 → B :=
  ![1, x]

@[simp] theorem oneX_zero (x : B) :
    oneX x (0 : Fin 2) = 1 := by
  simp [oneX]

@[simp] theorem oneX_one (x : B) :
    oneX x (1 : Fin 2) = x := by
  simp [oneX]

/--
If `{1,x}` becomes a supplied basis after residue-field base change, then
the same literal family is a basis over the local ring.
-/
theorem exists_basis_oneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = oneX x := by
  have hfamily :
      (TensorProduct.mk R k B 1 ∘ oneX x) =
        (b₀ : Fin 2 → k ⊗[R] B) := by
    funext i
    exact hb₀ i
  have hk :
      Function.Bijective
        (Finsupp.linearCombination k
          (TensorProduct.mk R k B 1 ∘ oneX x)) := by
    rw [hfamily]
    exact
      ⟨b₀.linearIndependent,
        fun y => ⟨b₀.repr y, b₀.linearCombination_repr y⟩⟩
  have hR :
      Function.Bijective
        (Finsupp.linearCombination R (oneX x)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat
      (R := R) (M := B) (oneX x) hk
  have hspan :
      ⊤ ≤ Submodule.span R (Set.range (oneX x)) := by
    rw [← Finsupp.range_linearCombination]
    exact (LinearMap.range_eq_top.mpr hR.2).ge
  refine ⟨Basis.mk hR.1 hspan, ?_⟩
  exact Basis.coe_mk hR.1 hspan

/-- A chosen integral basis with underlying family literally `{1,x}`. -/
def basisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    Basis (Fin 2) R B :=
  Classical.choose (exists_basis_oneX (R := R) (B := B) x b₀ hb₀)

@[simp] theorem coe_basisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    (basisOneX (R := R) (B := B) x b₀ hb₀ : Fin 2 → B) =
      oneX x :=
  Classical.choose_spec
    (exists_basis_oneX (R := R) (B := B) x b₀ hb₀)

@[simp] theorem basisOneX_zero
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    basisOneX (R := R) (B := B) x b₀ hb₀ (0 : Fin 2) = 1 := by
  rw [show
    basisOneX (R := R) (B := B) x b₀ hb₀ (0 : Fin 2) =
      oneX x (0 : Fin 2) by
    exact congrFun (coe_basisOneX (R := R) (B := B) x b₀ hb₀) 0]
  exact oneX_zero x

@[simp] theorem basisOneX_one
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    basisOneX (R := R) (B := B) x b₀ hb₀ (1 : Fin 2) = x := by
  rw [show
    basisOneX (R := R) (B := B) x b₀ hb₀ (1 : Fin 2) =
      oneX x (1 : Fin 2) by
    exact congrFun (coe_basisOneX (R := R) (B := B) x b₀ hb₀) 1]
  exact oneX_one x

/-- The lifted literal basis gives the power basis consumed by the
characteristic-polynomial quotient algebra. -/
def powerBasisOneX
    (x : B)
    (b₀ : Basis (Fin 2) k (k ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R k B 1 (oneX x i) = b₀ i) :
    PowerBasis R B :=
  N13RankTwoQuotientAlgebra.powerBasisOfOneX
    x (basisOneX x b₀ hb₀)
    (basisOneX_zero x b₀ hb₀)
    (basisOneX_one x b₀ hb₀)

end

end MazurProof.N13FiniteFlatBasisLift
