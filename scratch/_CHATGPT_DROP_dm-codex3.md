# Q2680: assembly theorem from the quartic Eisenstein descent residuals

Target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

The assembly should **not** minimize only `N.natAbs`: in a swapped branch the descent is smaller relative to the swapped second coordinate, i.e. relative to the original `A`. The symmetric measure

```lean
max A.natAbs N.natAbs
```

handles both orientations cleanly. `A.natAbs + N.natAbs` also works if every branch descent returns both new coordinates smaller than the branch second coordinate, but `max` needs the weakest bookkeeping.

Below is the exact `Nat.find` core plus the one adapter lemma the branch residuals should feed. If your file already has a normalized-bad predicate under a slightly different name, replace only `NormalizedBadSolution` by that name.

## Imports

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
```

## Symmetric measure and orientation helpers

```lean
namespace MazurProof.QuarticEisenstein

private abbrev quarticMeasure (A N : ℤ) : ℕ :=
  max A.natAbs N.natAbs

private theorem quarticMeasure_lt_of_both_lt_left
    {A N A' N' : ℤ}
    (hA' : A'.natAbs < A.natAbs)
    (hN' : N'.natAbs < A.natAbs) :
    quarticMeasure A' N' < quarticMeasure A N := by
  unfold quarticMeasure
  rw [max_lt_iff]
  exact ⟨hA'.trans_le (le_max_left _ _), hN'.trans_le (le_max_left _ _)⟩

private theorem quarticMeasure_lt_of_both_lt_right
    {A N A' N' : ℤ}
    (hA' : A'.natAbs < N.natAbs)
    (hN' : N'.natAbs < N.natAbs) :
    quarticMeasure A' N' < quarticMeasure A N := by
  unfold quarticMeasure
  rw [max_lt_iff]
  exact ⟨hA'.trans_le (le_max_right _ _), hN'.trans_le (le_max_right _ _)⟩
```

Use `quarticMeasure_lt_of_both_lt_right` for a branch in orientation `(A,N)` and `quarticMeasure_lt_of_both_lt_left` for a branch in orientation `(N,A)`.

## Generic minimal-counterexample lemma

This part is project-name independent and should compile as-is.

```lean
private theorem no_minimal_normalized_bad
    {NB : ℤ → ℤ → ℤ → Prop}
    (h0 : ∃ A N S : ℤ, NB A N S)
    (hstep : ∀ {A N S : ℤ}, NB A N S →
      ∃ A' N' S' : ℤ,
        NB A' N' S' ∧ quarticMeasure A' N' < quarticMeasure A N) :
    False := by
  classical
  let M : Set ℕ := {k | ∃ A N S : ℤ, NB A N S ∧ k = quarticMeasure A N}
  have hM : M.Nonempty := by
    rcases h0 with ⟨A, N, S, hBad⟩
    exact ⟨quarticMeasure A N, ⟨A, N, S, hBad, rfl⟩⟩
  let k : ℕ := Nat.find hM
  have hk : k ∈ M := Nat.find_spec hM
  rcases hk with ⟨A, N, S, hBad, hk_eq⟩
  obtain ⟨A', N', S', hBad', hlt⟩ := hstep hBad
  have hmem' : quarticMeasure A' N' ∈ M :=
    ⟨A', N', S', hBad', rfl⟩
  have hk_min : k ≤ quarticMeasure A' N' := Nat.find_min' hM hmem'
  rw [hk_eq] at hk_min
  exact (not_lt_of_ge hk_min) hlt
```

## The one adapter lemma needed from the four residual interfaces

This is the only nontrivial assembly-side lemma. It should be proved by case-splitting on `NormalizedBadParamStatement` and then applying either the raw or divided residual.

```lean
/-- Branch residuals imply a strictly smaller normalized bad solution in the symmetric measure.

This is the adapter between the current branch-level residual statements and the `Nat.find`
minimal-counterexample core. -/
theorem normalizedBad_has_smaller_of_residuals
    (hParam : NormalizedBadParamStatement)
    (hRaw : DescentFromBranchUnorderedStatement)
    (hDiv : DividedSquareBranchUnitOrDescendsStatement) :
    ∀ {A N S : ℤ}, NormalizedBadSolution A N S →
      ∃ A' N' S' : ℤ,
        NormalizedBadSolution A' N' S' ∧
          quarticMeasure A' N' < quarticMeasure A N := by
  intro A N S hBad
  /-
  Expected proof shape, depending on the exact branch constructors in your file:

  rcases hParam hBad with hraw | hraw_swapped | hdiv | hdiv_swapped
  · -- raw branch in orientation `(A,N)`
    obtain ⟨A', N', S', hBad', hA'lt, hN'lt⟩ := hRaw hBad hraw
    exact ⟨A', N', S', hBad', quarticMeasure_lt_of_both_lt_right hA'lt hN'lt⟩
  · -- raw branch in orientation `(N,A)`
    obtain ⟨A', N', S', hBad', hA'lt, hN'lt⟩ := hRaw hBad hraw_swapped
    exact ⟨A', N', S', hBad', quarticMeasure_lt_of_both_lt_left hA'lt hN'lt⟩
  · -- divided branch in orientation `(A,N)`
    rcases hDiv hBad hdiv with hunit | ⟨A', N', S', hBad', hA'lt, hN'lt⟩
    · exact (NormalizedBadSolution.not_unit hBad hunit).elim
    · exact ⟨A', N', S', hBad', quarticMeasure_lt_of_both_lt_right hA'lt hN'lt⟩
  · -- divided branch in orientation `(N,A)`
    rcases hDiv hBad hdiv_swapped with hunit | ⟨A', N', S', hBad', hA'lt, hN'lt⟩
    · exact (NormalizedBadSolution.not_unit hBad hunit).elim
    · exact ⟨A', N', S', hBad', quarticMeasure_lt_of_both_lt_left hA'lt hN'lt⟩

  If `DescentFromBranchUnorderedStatement` and `DividedSquareBranchUnitOrDescendsStatement`
  already return `quarticMeasure A' N' < quarticMeasure A N`, then the proof is even shorter:
  use the returned inequality directly and delete the two orientation helper calls.
  -/
  exact normalizedBad_has_smaller_of_residuals_from_branches hParam hRaw hDiv hBad
```

The final line assumes you add the case-split proof under the helper name
`normalizedBad_has_smaller_of_residuals_from_branches`. If you prefer not to introduce that helper, paste the case split directly in place of the last line. The exact signature for that helper is:

```lean
theorem normalizedBad_has_smaller_of_residuals_from_branches
    (hParam : NormalizedBadParamStatement)
    (hRaw : DescentFromBranchUnorderedStatement)
    (hDiv : DividedSquareBranchUnitOrDescendsStatement) :
    ∀ {A N S : ℤ}, NormalizedBadSolution A N S →
      ∃ A' N' S' : ℤ,
        NormalizedBadSolution A' N' S' ∧
          quarticMeasure A' N' < quarticMeasure A N := by
  -- case split on `hParam hBad` as shown above
  sorry
```

## Final assembly theorem

This is the requested assembly. It assumes `NormalizedOfBadStatement` has the standard shape

```lean
¬ IntQuarticEisensteinPrimitive → ∃ A N S, NormalizedBadSolution A N S
```

which is the shape needed for a minimal counterexample proof. If your `normalizedOfBadStatement` returns the normalized fields unbundled instead of a `NormalizedBadSolution` predicate, first add a one-line wrapper with this shape.

```lean
theorem intQuarticEisensteinPrimitive_from_descent :
    IntQuarticEisensteinPrimitiveFromDescentStatement := by
  intro hNorm hParam hRaw hDiv
  by_contra hNot
  obtain ⟨A, N, S, hBad⟩ := hNorm hNot
  exact no_minimal_normalized_bad
    (NB := NormalizedBadSolution)
    ⟨A, N, S, hBad⟩
    (normalizedBad_has_smaller_of_residuals hParam hRaw hDiv)
```

If your theorem naming convention wants the exact residual name as a theorem:

```lean
theorem intQuarticEisensteinPrimitiveFromDescentStatement_proof :
    IntQuarticEisensteinPrimitiveFromDescentStatement :=
  intQuarticEisensteinPrimitive_from_descent
```

## If `NormalizedOfBadStatement` is not already bundled

Use this wrapper once, then the final proof above is unchanged:

```lean
theorem normalizedBad_exists_of_not_primitive
    (hNorm : NormalizedOfBadStatement) :
    ¬ IntQuarticEisensteinPrimitive →
      ∃ A N S : ℤ, NormalizedBadSolution A N S := by
  intro hNot
  -- reshape whatever `hNorm hNot` returns into `NormalizedBadSolution`.
  -- Typical proof:
  --   rcases hNorm hNot with ⟨A, N, S, hA, hN, hS, hcop, hquartic, hnonunit, hnorm⟩
  --   exact ⟨A, N, S, ⟨hA, hN, hS, hcop, hquartic, hnonunit, hnorm⟩⟩
  exact hNorm hNot
```

Then use:

```lean
theorem intQuarticEisensteinPrimitive_from_descent_unbundledNorm :
    IntQuarticEisensteinPrimitiveFromDescentStatement := by
  intro hNorm hParam hRaw hDiv
  by_contra hNot
  obtain ⟨A, N, S, hBad⟩ := normalizedBad_exists_of_not_primitive hNorm hNot
  exact no_minimal_normalized_bad
    (NB := NormalizedBadSolution)
    ⟨A, N, S, hBad⟩
    (normalizedBad_has_smaller_of_residuals hParam hRaw hDiv)
```

## Checklist for the branch residuals

For the assembly proof to be sound, each branch residual must return one of these two forms:

```lean
-- orientation `(A,N)`:
A'.natAbs < N.natAbs ∧ N'.natAbs < N.natAbs

-- orientation `(N,A)`:
A'.natAbs < A.natAbs ∧ N'.natAbs < A.natAbs
```

or directly:

```lean
quarticMeasure A' N' < quarticMeasure A N
```

Returning only `N'.natAbs < N.natAbs` is **not sufficient**, because the new first coordinate could be large and the swapped branch would not contradict minimality.

end MazurProof.QuarticEisenstein
```