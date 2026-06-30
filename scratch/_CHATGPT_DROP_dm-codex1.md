# Q2443-RETRY3 twoA_triangle_param Lean route

Minimal route: use the verified Mathlib API directly.  The code below is namespace-neutral; paste it either at top level or inside the namespace already used by `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

```lean
import Mathlib.NumberTheory.PythagoreanTriples

/-- Direct specialization of `PythagoreanTriple.coprime_classification'` to the
triangle whose even leg is `2*A`. -/
theorem twoA_triangle_param
    {A B C : ℤ}
    (hpy : PythagoreanTriple B (2*A) C)
    (hg : Int.gcd B (2*A) = 1)
    (hBodd : B % 2 = 1)
    (hCpos : 0 < C) :
    ∃ m n : ℤ,
      B = m^2 - n^2 ∧
      2*A = 2*m*n ∧
      C = m^2 + n^2 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      0 ≤ m := by
  simpa using
    PythagoreanTriple.coprime_classification' hpy hg hBodd hCpos

/-- Integer cancellation helper for the exact shape returned by the
Pythagorean classification.  The only normalization needed is reassociating
`2*m*n` to `2*(m*n)`. -/
lemma eq_mul_of_two_mul_eq_two_mul_mul
    {A m n : ℤ}
    (h : 2*A = 2*m*n) :
    A = m*n := by
  have h' : (2 : ℤ) * A = (2 : ℤ) * (m*n) := by
    simpa [mul_assoc] using h
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h'

/-- Same parametrization, but with the cancellable conclusion `A = m*n`
instead of `2*A = 2*m*n`. -/
theorem twoA_triangle_param_with_A
    {A B C : ℤ}
    (hpy : PythagoreanTriple B (2*A) C)
    (hg : Int.gcd B (2*A) = 1)
    (hBodd : B % 2 = 1)
    (hCpos : 0 < C) :
    ∃ m n : ℤ,
      B = m^2 - n^2 ∧
      A = m*n ∧
      C = m^2 + n^2 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      0 ≤ m := by
  rcases twoA_triangle_param hpy hg hBodd hCpos with
    ⟨m, n, hB, h2A, hC, hgmn, hpar, hm_nonneg⟩
  refine ⟨m, n, hB, ?_, hC, hgmn, hpar, hm_nonneg⟩
  exact eq_mul_of_two_mul_eq_two_mul_mul h2A

/-- Optional nonzero refinement: if `A ≠ 0`, then the parameters in the
`A = m*n` version are both nonzero.  No sign normalization for `n` is needed. -/
theorem twoA_triangle_param_with_A_nonzero
    {A B C : ℤ}
    (hpy : PythagoreanTriple B (2*A) C)
    (hg : Int.gcd B (2*A) = 1)
    (hBodd : B % 2 = 1)
    (hCpos : 0 < C)
    (hA0 : A ≠ 0) :
    ∃ m n : ℤ,
      B = m^2 - n^2 ∧
      A = m*n ∧
      C = m^2 + n^2 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      0 ≤ m ∧
      m ≠ 0 ∧ n ≠ 0 := by
  rcases twoA_triangle_param_with_A hpy hg hBodd hCpos with
    ⟨m, n, hB, hAeq, hC, hgmn, hpar, hm_nonneg⟩
  have hm0 : m ≠ 0 := by
    intro hm
    apply hA0
    rw [hAeq, hm, zero_mul]
  have hn0 : n ≠ 0 := by
    intro hn
    apply hA0
    rw [hAeq, hn, mul_zero]
  exact ⟨m, n, hB, hAeq, hC, hgmn, hpar, hm_nonneg, hm0, hn0⟩
```

Notes for integration:

* If `RationalPointsN12.lean` already imports a project file that imports `Mathlib.NumberTheory.PythagoreanTriples`, no new import is needed there.
* The direct theorem is intentionally just `simpa using PythagoreanTriple.coprime_classification' hpy hg hBodd hCpos` because the verified API already has the exact target shape with `x = B`, `y = 2*A`, `z = C`.
* The exact cancellation step from `2*A = 2*m*n` to `A = m*n` is:

```lean
have h' : (2 : ℤ) * A = (2 : ℤ) * (m*n) := by
  simpa [mul_assoc] using h
exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h'
```

No `ring` or `norm_num` is required.  If preferred, `(by decide : (2 : ℤ) ≠ 0)` can be replaced by `(by norm_num : (2 : ℤ) ≠ 0)` after importing `Mathlib.Tactic`.
