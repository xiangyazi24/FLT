# Q2339: final dependency assembly for `QuarticAParamBridge`

```lean
-- In a separate check file, keep this import.  If this block is pasted
-- directly at the end of `FLT/Assumptions/MazurProof/RationalPointsN12.lean`,
-- omit the import line.
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Checked assembly of the odd/odd bridge from the divided-triple primitive
lemma and the primitive divided-triple classification lemma. -/
theorem quarticAOddOddRSDataTheorem_checked :
    QuarticAOddOddRSDataTheorem := by
  exact
    QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
      quarticAOddOddDividedTriplePrimitive
      quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem

/-- Checked project-facing odd/odd parameter bridge. -/
theorem quarticAOddOddParamBridge_checked :
    QuarticAOddOddParamBridge := by
  exact
    QuarticAOddOddParamBridge_of_RSDataTheorem
      quarticAOddOddRSDataTheorem_checked

/-- Checked project-facing opposite-parity parameter bridge. -/
theorem quarticAOppParityParamBridge_checked :
    QuarticAOppParityParamBridge := by
  refine quarticAOppParityParamBridge_of_leg_coprime ?_
  intro u v Z hcop huv0 hne hopp hA
  exact
    quarticA_oppParity_leg_coprime
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hopp hA

/-- Final checked `QuarticA` parameter bridge assembled from parity cases. -/
theorem quarticAParamBridge_checked :
    QuarticAParamBridge := by
  exact
    quarticA_paramBridge_of_parity_cases
      quarticAPrimitiveParitySplit_proof
      quarticAOppParityParamBridge_checked
      quarticAOddOddParamBridge_checked

end MazurProof.RationalPointsN12
```

The same code can be written without the intermediate `quarticAOddOddRSDataTheorem_checked` theorem, but keeping it makes the dependency graph explicit and gives a useful local target if a later name changes.

Dependency audit:

```text
quarticAOddOddDividedTriplePrimitive
quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem
  └─ QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
       └─ quarticAOddOddRSDataTheorem_checked
            └─ QuarticAOddOddParamBridge_of_RSDataTheorem
                 └─ quarticAOddOddParamBridge_checked

quarticA_oppParity_leg_coprime
  └─ quarticAOppParityParamBridge_of_leg_coprime
       └─ quarticAOppParityParamBridge_checked

quarticAPrimitiveParitySplit_proof
quarticAOppParityParamBridge_checked
quarticAOddOddParamBridge_checked
  └─ quarticA_paramBridge_of_parity_cases
       └─ quarticAParamBridge_checked
```

There is no hidden circular dependency in this assembly as long as the three leaf theorems below are proved independently of `quarticAParamBridge_checked` and its two checked bridge wrappers:

```lean
quarticAPrimitiveParitySplit_proof
quarticA_oppParity_leg_coprime
quarticAOddOddDividedTriplePrimitive
quarticA_oddOddRSDataOfPrimitiveDividedTripleTheorem
```

No extra hypothesis is missing from the final assembly.  The nondegeneracy hypothesis `u ^ 2 ≠ v ^ 2` is consumed by the branch bridge definitions and by the leg-coprime wrapper interface, not by the primitive parity split.  No `Z` sign normalization or separate `Z ≠ 0` assumption is needed for these wrappers.

The argument order used above matches the project-facing theorem statements in the prompt:

```lean
quarticA_paramBridge_of_parity_cases
  (hParity : QuarticAPrimitiveParitySplit)
  (hOpp : QuarticAOppParityParamBridge)
  (hOddOdd : QuarticAOddOddParamBridge)

quarticAOppParityParamBridge_of_leg_coprime
  (hlegcop_of_quarticA :
    ∀ {u v Z : ℤ},
      Int.gcd u v = 1 → u * v ≠ 0 → u ^ 2 ≠ v ^ 2 →
      ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) → QuarticA u v Z →
      Int.gcd Z (2 * v ^ 2) = 1)

QuarticAOddOddParamBridge_of_RSDataTheorem
  (hRSTheorem : QuarticAOddOddRSDataTheorem)

QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
  (hprim : QuarticAOddOddDividedTriplePrimitiveTheorem)
  (hclass : QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem)
```

The `intro u v Z ...` line in `quarticAOppParityParamBridge_checked` deliberately introduces the implicit variables of the leg-coprime functional hypothesis.  This avoids relying on binder names in `quarticAOppParityParamBridge_of_leg_coprime` and is usually more robust than passing the theorem by a named argument.
