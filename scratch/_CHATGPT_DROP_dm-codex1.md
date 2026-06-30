# Q2343: specialize the `QuarticA` residual wrappers

```lean
-- In a separate check file, keep this import.  If this block is pasted
-- directly at the end of `FLT/Assumptions/MazurProof/RationalPointsN12.lean`,
-- omit the import line.
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Checked wrapper: the assembled `QuarticAParamBridge` and checked extraction
produce the project residual proposition. -/
theorem quarticA_to_eisensteinQuarticResidual_checked
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    EisensteinQuarticResidual := by
  exact
    quarticA_to_eisensteinQuarticResidual_of_bridge
      quarticAParamBridge_checked
      coprimeSquareProductExtraction
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

/-- Checked wrapper: the assembled `QuarticAParamBridge` and checked extraction
produce the explicit Ljunggren/Eisenstein quartic residual equation. -/
theorem quarticA_to_eisenstein_residual_statement_checked
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  exact
    quarticA_to_eisenstein_residual_statement_of_bridge
      quarticAParamBridge_checked
      coprimeSquareProductExtraction
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

/-- Final contradiction wrapper if the project has, or later imports, a theorem
ruling out the residual proposition directly. -/
theorem quarticA_no_solution_of_no_eisensteinQuarticResidual
    (hNoResidual : ¬ EisensteinQuarticResidual)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  exact
    hNoResidual
      (quarticA_to_eisensteinQuarticResidual_checked
        (u := u) (v := v) (Z := Z)
        hcop huv0 hne hA)

/-- Recommended explicit Ljunggren/no-Eisenstein interface.

This avoids depending on the internal definition of `EisensteinQuarticResidual`:
the imported theorem only has to say that there are no nonzero coprime integer
solutions to the residual equation. -/
theorem quarticA_no_solution_of_no_eisenstein_residual_statement
    (hNoEisenstein :
      ∀ {m n c : ℤ},
        m * n ≠ 0 →
        Int.gcd m n = 1 →
        c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
        False)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  obtain ⟨m, n, c, hmn0, hmncop, hc⟩ :=
    quarticA_to_eisenstein_residual_statement_checked
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA
  exact hNoEisenstein (m := m) (n := n) (c := c) hmn0 hmncop hc

end MazurProof.RationalPointsN12
```

Audit notes:

* The two checked wrappers are only specializations of the bridge-parameterized theorems with:
  ```lean
  quarticAParamBridge_checked
  coprimeSquareProductExtraction
  ```
  No additional mathematical hypotheses are introduced.

* This closes the reduction from primitive, nonzero, nondegenerate `QuarticA u v Z` to the Eisenstein/Ljunggren residual equation.  It does **not** by itself close the QuarticA case as a contradiction.

* To close the QuarticA residual unconditionally, the project still needs an external no-residual theorem.  The most robust interface is the explicit statement used by `quarticA_no_solution_of_no_eisenstein_residual_statement`:
  ```lean
  ∀ {m n c : ℤ},
    m * n ≠ 0 →
    Int.gcd m n = 1 →
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    False
  ```
  This interface is preferable to tying the final contradiction to the internal shape of `EisensteinQuarticResidual`.

* If the project already has a theorem of type `¬ EisensteinQuarticResidual`, then the shorter wrapper `quarticA_no_solution_of_no_eisensteinQuarticResidual` is enough.

* No hidden circular dependency is present provided `quarticAParamBridge_checked` was assembled independently from the residual-producing theorems.  The dependency flow is:
  ```text
  quarticAParamBridge_checked
  coprimeSquareProductExtraction
    └─ quarticA_to_eisensteinQuarticResidual_of_bridge
         └─ quarticA_to_eisensteinQuarticResidual_checked

  quarticAParamBridge_checked
  coprimeSquareProductExtraction
    └─ quarticA_to_eisenstein_residual_statement_of_bridge
         └─ quarticA_to_eisenstein_residual_statement_checked
              └─ quarticA_no_solution_of_no_eisenstein_residual_statement
  ```
