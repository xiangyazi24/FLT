import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityFiberComplete

/-- Three distinct positive-weight points with weights 1,1,2 exhaust a
finite fiber whose total weight is four. -/
theorem exhaustive_of_weights {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : w a = 1) (hb : w b = 1) (hc : w c = 2)
    (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 4) :
    ∀ i, i = a ∨ i = b ∨ i = c := by
  classical
  intro i
  by_contra hi
  have hia : i ≠ a := fun h => hi (Or.inl h)
  have hib : i ≠ b := fun h => hi (Or.inr (Or.inl h))
  have hic : i ≠ c := fun h => hi (Or.inr (Or.inr h))
  have hle : ∑ x ∈ ({i, a, b, c} : Finset ι), w x ≤ ∑ x, w x :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    hia, hib, hic, hab, hac, hbc, or_self, not_false_eq_true,
    Finset.sum_singleton, ha, hb, hc] at hle
  have hp := hpos i
  rw [hsum] at hle
  omega

#print axioms exhaustive_of_weights
end MazurProof.N25F_InfinityFiberComplete
