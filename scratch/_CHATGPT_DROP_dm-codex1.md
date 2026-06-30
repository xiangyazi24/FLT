# Q2685 (dm-codex1): final assembly from residual descent interfaces

Assumptions: the definitions in the prompt are already present in `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`. The code below is the assembly layer only; it introduces no axioms and no `sorry`.

Paste this after the residual definitions. If the file is already syntactically inside `namespace MazurProof.RationalPointsN12`, omit the two namespace wrapper lines.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private lemma normalizedEisensteinBad_second_pos {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    0 < N := by
  exact lt_trans h.1 h.2.1

private lemma normalizedEisensteinBad_sq_ne {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    A ^ 2 ≠ N ^ 2 := by
  have hApos : 0 < A := h.1
  have hAltN : A < N := h.2.1
  have hdiffpos : 0 < N - A := by
    linarith
  have hsumpos : 0 < N + A := by
    have hNpos : 0 < N := lt_trans hApos hAltN
    linarith
  intro hsq
  have hfactor : N ^ 2 - A ^ 2 = (N - A) * (N + A) := by
    ring
  have hdiffsqpos : 0 < N ^ 2 - A ^ 2 := by
    rw [hfactor]
    exact mul_pos hdiffpos hsumpos
  have hzero : N ^ 2 - A ^ 2 = 0 := by
    rw [hsq]
    ring
  linarith

/-- A normalized bad triple is a positive primitive unordered bad triple. -/
theorem positivePrimitiveEisensteinBadUnordered_of_normalized {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    PositivePrimitiveEisensteinBadUnordered A N S := by
  have hsqne : A ^ 2 ≠ N ^ 2 := normalizedEisensteinBad_sq_ne h
  rcases h with ⟨hApos, hAltN, hSpos, hcop, heq⟩
  have hNpos : 0 < N := lt_trans hApos hAltN
  exact ⟨hApos, hNpos, hSpos, hcop, hsqne, heq⟩

/-- Swapping the two square sides preserves the unordered bad condition. -/
theorem positivePrimitiveEisensteinBadUnordered_swap_of_normalized {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    PositivePrimitiveEisensteinBadUnordered N A S := by
  have hsqne : A ^ 2 ≠ N ^ 2 := normalizedEisensteinBad_sq_ne h
  rcases h with ⟨hApos, hAltN, hSpos, hcop, heq⟩
  have hNpos : 0 < N := lt_trans hApos hAltN
  refine ⟨hNpos, hApos, hSpos, hcop.symm, ?_, ?_⟩
  · intro hsqswap
    exact hsqne hsqswap.symm
  · calc
      S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := heq
      _ = N ^ 4 - N ^ 2 * A ^ 2 + A ^ 4 := by
        ring

private lemma normalizedEisensteinBad_not_unit {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) := by
  intro hunit
  rcases hunit with ⟨hA, hN, _hS⟩
  have hlt : A < N := h.2.1
  have hbad : (1 : ℤ) < 1 := by
    simpa [hA, hN] using hlt
  exact (lt_irrefl (1 : ℤ)) hbad

private lemma normalizedEisensteinBad_not_swap_unit {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    ¬ (N = 1 ∧ A = 1 ∧ S = 1) := by
  intro hunit
  rcases hunit with ⟨hN, hA, _hS⟩
  have hlt : A < N := h.2.1
  have hbad : (1 : ℤ) < 1 := by
    simpa [hA, hN] using hlt
  exact (lt_irrefl (1 : ℤ)) hbad

/-- Assemble normalized descent from the parametrization and branch residuals. -/
theorem normalizedDescentStatement_from_branches
    (hParam : NormalizedBadParamStatement)
    (hSqDesc : DescentFromBranchUnorderedStatement)
    (hDivDesc : DividedSquareBranchUnitOrDescendsStatement) :
    NormalizedDescentStatement := by
  intro A N S hnorm
  have hAltN : A < N := hnorm.2.1
  have hunord : PositivePrimitiveEisensteinBadUnordered A N S :=
    positivePrimitiveEisensteinBadUnordered_of_normalized hnorm
  have hswap : PositivePrimitiveEisensteinBadUnordered N A S :=
    positivePrimitiveEisensteinBadUnordered_swap_of_normalized hnorm
  rcases hParam hnorm with ⟨m, n, hcases⟩
  rcases hcases with hSq | hSqSwap | hDiv | hDivSwap
  · exact hSqDesc hunord hSq
  · rcases hSqDesc hswap hSqSwap with ⟨A', N', S', hnorm', hlt⟩
    exact ⟨A', N', S', hnorm', lt_trans hlt hAltN⟩
  · rcases hDivDesc hunord hDiv with hunit | hdescent
    · exact False.elim (normalizedEisensteinBad_not_unit hnorm hunit)
    · exact hdescent
  · rcases hDivDesc hswap hDivSwap with hunit | hdescent
    · exact False.elim (normalizedEisensteinBad_not_swap_unit hnorm hunit)
    · rcases hdescent with ⟨A', N', S', hnorm', hlt⟩
      exact ⟨A', N', S', hnorm', lt_trans hlt hAltN⟩

/-- Infinite descent on the positive second coordinate, implemented via `Nat.find`. -/
theorem notNormalizedBad_of_descent
    (hDescent : NormalizedDescentStatement) :
    NotNormalizedBadStatement := by
  classical
  rintro ⟨A, N, S, hnorm⟩
  let P : ℕ → Prop := fun k =>
    ∃ A N S : ℤ, NormalizedEisensteinBad A N S ∧ N.natAbs = k
  have hExists : ∃ k : ℕ, P k := by
    refine ⟨N.natAbs, ?_⟩
    dsimp [P]
    exact ⟨A, N, S, hnorm, rfl⟩
  have hFindSpec : P (Nat.find hExists) := Nat.find_spec hExists
  dsimp [P] at hFindSpec
  rcases hFindSpec with ⟨A0, N0, S0, hnorm0, hN0_find⟩
  rcases hDescent hnorm0 with ⟨A1, N1, S1, hnorm1, hlt⟩
  have hN0pos : 0 < N0 := normalizedEisensteinBad_second_pos hnorm0
  have hN1pos : 0 < N1 := normalizedEisensteinBad_second_pos hnorm1
  have hnatlt : N1.natAbs < N0.natAbs := by
    have hN1nonneg : 0 ≤ N1 := le_of_lt hN1pos
    have hN0nonneg : 0 ≤ N0 := le_of_lt hN0pos
    rw [Int.natAbs_of_nonneg hN1nonneg, Int.natAbs_of_nonneg hN0nonneg]
    exact_mod_cast hlt
  have hPsmaller : P N1.natAbs := by
    dsimp [P]
    exact ⟨A1, N1, S1, hnorm1, rfl⟩
  have hmin_le : Nat.find hExists ≤ N1.natAbs := by
    exact Nat.find_min' hExists hPsmaller
  have hlt_find : N1.natAbs < Nat.find hExists := by
    simpa [hN0_find] using hnatlt
  exact (not_lt_of_ge hmin_le) hlt_find

/-- Final assembly: normalized bad reduction + branch descent imply the primitive theorem. -/
theorem intQuarticEisensteinPrimitiveFromDescentStatement :
    IntQuarticEisensteinPrimitiveFromDescentStatement := by
  intro hNormalizedOfBad hParam hSqDesc hDivDesc
  have hNormDesc : NormalizedDescentStatement :=
    normalizedDescentStatement_from_branches hParam hSqDesc hDivDesc
  have hNoNorm : NotNormalizedBadStatement :=
    notNormalizedBad_of_descent hNormDesc
  intro A N S hcop hNne heq
  by_cases hA0 : A = 0
  · exact Or.inl hA0
  · by_cases hsq : A ^ 2 = N ^ 2
    · exact Or.inr hsq
    · exfalso
      have hbad : EisensteinQuarticBad A N S := by
        exact ⟨hcop, hA0, hNne, hsq, heq⟩
      exact hNoNorm (hNormalizedOfBad hbad)

end MazurProof.RationalPointsN12
```

Notes for the two fragile-looking lines:

```lean
rw [Int.natAbs_of_nonneg hN1nonneg, Int.natAbs_of_nonneg hN0nonneg]
exact_mod_cast hlt
```

After rewriting `natAbs` of positive integers to `toNat`, `exact_mod_cast` proves the natural inequality from the integer inequality `hlt : N1 < N0`. If local simp behavior around `Int.toNat` differs, the proof obligation at that point is exactly:

```lean
N1.toNat < N0.toNat
```

with hypotheses:

```lean
hN1nonneg : 0 ≤ N1
hN0nonneg : 0 ≤ N0
hlt : N1 < N0
```

The `Nat.find_min'` use is intentionally direct:

```lean
have hmin_le : Nat.find hExists ≤ N1.natAbs := by
  exact Nat.find_min' hExists hPsmaller
```

and the contradiction is then just `not_lt_of_ge hmin_le` against the descended smaller witness.
