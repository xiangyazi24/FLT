import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

/-! Model-independent linear algebra and exact integer deficit arithmetic.
No curve, valuation, section-space, or kernel-membership model is introduced. -/
noncomputable section
namespace KernelSectionLinearAlgebra
variable {k M Q : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup Q] [Module k Q]

/-- Restrict the ambient subtype map using an independently proved membership theorem. -/
def kernelIntoSubmodule (S T : Submodule k M) (q : S →ₗ[k] Q)
    (h : ∀ f : S, q f = 0 → (f : M) ∈ T) : LinearMap.ker q →ₗ[k] T where
  toFun f := ⟨f.1.1, h f.1 f.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem kernelIntoSubmodule_injective (S T : Submodule k M) (q : S →ₗ[k] Q)
    (h : ∀ f : S, q f = 0 → (f : M) ∈ T) :
    Function.Injective (kernelIntoSubmodule S T q h) := by
  intro f g he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : T => (z : M)) he

theorem finrank_kernel_le (S T : Submodule k M) [Module.Finite k T]
    (q : S →ₗ[k] Q) (h : ∀ f : S, q f = 0 → (f : M) ∈ T) :
    Module.finrank k (LinearMap.ker q) ≤ Module.finrank k T :=
  LinearMap.finrank_le_finrank_of_injective (kernelIntoSubmodule_injective S T q h)

/-- The natural deficits retain their exact signed values under domination. -/
theorem deficits_cast (n : ℕ) (x y z : ℤ)
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ 2 * (n : ℤ)) :
    (((n : ℤ) - x).toNat : ℤ) = n - x ∧
    (((n : ℤ) - y).toNat : ℤ) = n - y ∧
    ((2 * (n : ℤ) - z).toNat : ℤ) = 2 * (n : ℤ) - z := by
  omega

/-- Once the genuine affine degree identity is supplied, no further geometry
is hidden in cancellation of the three boundary costs. -/
theorem deficit_cost_identity (n cost : ℕ) (x y z degD : ℤ)
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ 2 * (n : ℤ))
    (hdegree : degD = x + y + z - cost) :
    (cost : ℤ) + ((n : ℤ) - x).toNat + ((n : ℤ) - y).toNat +
      (2 * (n : ℤ) - z).toNat = 4 * (n : ℤ) - degD := by
  obtain ⟨ha, hb, hc⟩ := deficits_cast n x y z hx hy hz
  omega

#print axioms kernelIntoSubmodule
#print axioms kernelIntoSubmodule_injective
#print axioms finrank_kernel_le
#print axioms deficits_cast
#print axioms deficit_cost_identity
end KernelSectionLinearAlgebra
