import Mathlib

/-!
# Low-degree coefficients of the curve Euler product

Let `A n` be the number of effective divisors of degree `n` and let `N n` be
the number of rational points over the degree-`n` extension of the base field.
The logarithmic derivative of the closed-point Euler product gives the
denominator-free recurrence

`n A_n = sum_{k=1}^n N_k A_(n-k)`.

This file records that recurrence as a reusable interface and proves its first
four consequences.  The separate geometric-combinatorial layer must prove the
interface by decomposing effective divisors into closed points; no zeta or
Jacobian cardinality is assumed here.
-/

namespace MazurProof.CurveZetaEulerRecurrence

open scoped BigOperators

/-- The denominator-free coefficient recurrence obtained from the
closed-point Euler product.  Indexing the sum by `j < n` represents
`k=j+1`, so no zero-extension convention is needed. -/
def SatisfiesEulerRecurrence (A N : ℕ → ℕ) : Prop :=
  A 0 = 1 ∧
    ∀ n, 1 ≤ n →
      n * A n = ∑ j ∈ Finset.range n, N (j + 1) * A (n - (j + 1))

/-- A normalized Euler recurrence has at most one coefficient sequence.
The proof is strong induction: the degree-`n` equation involves only smaller
effective-divisor degrees, after which multiplication by positive `n` can be
cancelled in the natural numbers. -/
theorem SatisfiesEulerRecurrence.unique
    {A B N : ℕ → ℕ}
    (hA : SatisfiesEulerRecurrence A N)
    (hB : SatisfiesEulerRecurrence B N) :
    A = B := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact hA.1.trans hB.1.symm
      · have hnpos : 1 ≤ n := by omega
        have hrecA := hA.2 n hnpos
        have hrecB := hB.2 n hnpos
        have hsum :
            (∑ j ∈ Finset.range n, N (j + 1) * A (n - (j + 1))) =
              ∑ j ∈ Finset.range n, N (j + 1) * B (n - (j + 1)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih (n - (j + 1))]
          exact Nat.sub_lt hnpos (by omega)
        rw [hsum] at hrecA
        exact mul_left_cancel₀ hn (hrecA.trans hrecB.symm)

/-- The first four N25 extension-field counts force the effective-divisor
counts `A_0,...,A_4 = 1,5,15,40,116` through the Euler recurrence.

The calculation is triangular: the degree-`n` equation contains `n*A_n` and
only previously determined effective-divisor counts on its right-hand side. -/
theorem first_four_effective_counts_of_n25_data
    (A N : ℕ → ℕ)
    (hEuler : SatisfiesEulerRecurrence A N)
    (hN1 : N 1 = 5) (hN2 : N 2 = 5)
    (hN3 : N 3 = 20) (hN4 : N 4 = 89) :
    A 0 = 1 ∧ A 1 = 5 ∧ A 2 = 15 ∧ A 3 = 40 ∧ A 4 = 116 := by
  rcases hEuler with ⟨hA0, hrec⟩
  have hrec1 := hrec 1 (by omega)
  have hA1 : A 1 = 5 := by
    norm_num [Finset.sum_range_succ, hA0, hN1] at hrec1
    omega
  have hrec2 := hrec 2 (by omega)
  have hA2 : A 2 = 15 := by
    norm_num [Finset.sum_range_succ, hA0, hA1, hN1, hN2] at hrec2
    omega
  have hrec3 := hrec 3 (by omega)
  have hA3 : A 3 = 40 := by
    norm_num [Finset.sum_range_succ, hA0, hA1, hA2, hN1, hN2, hN3] at hrec3
    omega
  have hrec4 := hrec 4 (by omega)
  have hA4 : A 4 = 116 := by
    norm_num [Finset.sum_range_succ, hA0, hA1, hA2, hA3, hN1, hN2, hN3,
      hN4] at hrec4
    omega
  exact ⟨hA0, hA1, hA2, hA3, hA4⟩

/-- Only degrees two and four are needed by middle-degree Riemann--Roch for a
genus-four curve.  This projection keeps the final N25 consumer small. -/
theorem effective_counts_two_and_four_of_n25_data
    (A N : ℕ → ℕ)
    (hEuler : SatisfiesEulerRecurrence A N)
    (hN1 : N 1 = 5) (hN2 : N 2 = 5)
    (hN3 : N 3 = 20) (hN4 : N 4 = 89) :
    A 2 = 15 ∧ A 4 = 116 := by
  rcases first_four_effective_counts_of_n25_data A N hEuler hN1 hN2 hN3 hN4
    with ⟨_, _, hA2, _, hA4⟩
  exact ⟨hA2, hA4⟩

end MazurProof.CurveZetaEulerRecurrence
