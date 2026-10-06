import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

namespace DegreeReindex
/-- Pure finite-support reindexing; no geometric objects or assumptions. -/
theorem sum_neg_reindex {ι κ : Type*} (e : ι ≃ κ)
    (d : ι →₀ ℤ) (c : κ →₀ ℤ)
    (hc : ∀ i, d i = -c (e i)) (w : κ → ℤ) :
    d.sum (fun i z => z * w (e i)) = -c.sum (fun j z => z * w j) := by
  classical
  have h : d.sum (fun i z => z * w (e i)) = c.sum (fun j z => -z * w j) := by
    unfold Finsupp.sum
    apply Finset.sum_bij (fun i _ => e i)
    · intro i hi
      simpa only [Finsupp.mem_support_iff, hc, neg_ne_zero] using hi
    · intro i hi j hj he
      exact e.injective he
    · intro j hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      simpa only [Finsupp.mem_support_iff, hc, e.apply_symm_apply, neg_ne_zero] using hj
    · intro i hi
      rw [hc]
  rw [h]
  simp only [Finsupp.sum, neg_mul, Finset.sum_neg_distrib]

/-- Cancellation used by the coarse bound, separately from the geometric identity. -/
theorem coarse_bound (n poleBound baseRank sectionRank cost a b c : ℕ) (degree : ℤ)
    (hbase : 4 * n ≤ baseRank + 4 * poleBound)
    (hcost : baseRank ≤ sectionRank + cost + a + b + c)
    (hdegree : (cost : ℤ) + a + b + c = 4 * (n : ℤ) - degree) :
    degree ≤ (sectionRank : ℤ) + 4 * (poleBound : ℤ) := by
  omega
#print axioms sum_neg_reindex
#print axioms coarse_bound
end DegreeReindex
