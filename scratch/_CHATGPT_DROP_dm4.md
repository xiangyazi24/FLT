# Q255 (dm4): closing `preΨ'_eval_eq_zero_iff_exists_non_two_torsion` sub-D

## (a) Does `[IsSepClosed k]` imply `[IsAlgClosed k]`?

No, not in general, and you should not expect a Mathlib instance

```lean
[IsSepClosed k] → IsAlgClosed k
```

because the implication is false mathematically in positive characteristic: a separably closed field can still have purely inseparable algebraic extensions.  The implication becomes true under an additional perfection hypothesis, for example in characteristic zero / perfect-field contexts, but not from `IsSepClosed` alone.

Therefore, with the pieces listed in the question, there are two clean options:

1. **Fast wiring option:** strengthen this theorem, or at least the `→` direction helper, with `[IsAlgClosed k]` and use the existing `exists_nonsingular` from `scratch/PointRealization.lean`.
2. **Best final API option:** keep the theorem under `[IsSepClosed k]`, but add a new point-realization lemma specialized to the separable fiber:

   ```lean
   theorem exists_nonsingular_of_Ψ₂Sq_eval_ne_zero
       [IsSepClosed k] (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) :
       ∃ y, (W⁄k).Nonsingular x y
   ```

   This is plausible because `hΨ₂` says the quadratic fiber over `x` has nonzero discriminant / is separable, so separable closedness should supply a root.  But this is a new lemma; the existing `exists_nonsingular` requiring `[IsAlgClosed k]` cannot be used from `[IsSepClosed k]` alone.

The exact proof term below is for option 1, because it uses the available `exists_nonsingular` directly.

## Minimal strengthened theorem

Add `[IsAlgClosed k]` to the theorem if you want to use the current point-realization lemma:

```lean
theorem preΨ'_eval_eq_zero_iff_exists_non_two_torsion
    [IsSepClosed k] [IsAlgClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) {x : k} :
    (W.preΨ' n).eval x = 0 ↔
      ∃ y, ∃ h : (W⁄k).Nonsingular x y,
        2 • (Point.some x y h : (W⁄k).Point) ≠ 0 ∧
          n • (Point.some x y h : (W⁄k).Point) = 0 := by
  constructor
  · intro hx
    have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 :=
      preΨ'_root_Ψ₂Sq_ne (W := W) (n := n) (x := x) hn hx
    rcases exists_nonsingular (W := W) (x := x) with ⟨y, h⟩
    let P : (W⁄k).Point := Point.some x y h
    have h₂ : 2 • P ≠ 0 := by
      exact (two_nsmul_ne_zero_iff_Ψ₂Sq_eval_ne_zero (W := W) (x := x) (y := y) h).2 hΨ₂
    have hnP : n • P = 0 := by
      exact
        (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
          (W := W) (n := n) h h₂).mpr hx
    exact ⟨y, h, by simpa [P] using h₂, by simpa [P] using hnP⟩
  · rintro ⟨y, h, h₂, hnP⟩
    exact
      (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
        (W := W) (n := n) h h₂).mp hnP
```

If your local equivalence theorem carries `hn` explicitly, use this variant at the two calls:

```lean
(nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
  (W := W) (n := n) (hn := hn) h h₂)
```

rather than the shorter version.

## If the 2-torsion lemma is stated with equality-to-zero

If your local file has the zero equivalence instead of the `ne_zero` equivalence, replace the proof of `h₂` by:

```lean
    have h₂ : 2 • P ≠ 0 := by
      intro h2zero
      have hΨ₂_zero : W.Ψ₂Sq.eval x = 0 := by
        exact
          (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero
            (W := W) (x := x) (y := y) h).mp (by simpa [P] using h2zero)
      exact hΨ₂ hΨ₂_zero
```

Equivalently, if the lemma is stated with the iff in the other direction, use `.1`/`.2` accordingly.  The proof is just contraposition of the direct 2-torsion criterion.

## If bridge-1 returns `(W.ΨSq (2 : ℤ)).eval x ≠ 0`

Some files state the bridge in terms of `ΨSq 2` rather than `Ψ₂Sq`.  Normalize once:

```lean
    have hΨSq2 : (W.ΨSq (2 : ℤ)).eval x ≠ 0 :=
      preΨ'_root_Ψ₂Sq_ne (W := W) (n := n) (x := x) hn hx
    have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := by
      simpa [WeierstrassCurve.ΨSq_two] using hΨSq2
```

or the reverse:

```lean
    have hΨSq2 : (W.ΨSq (2 : ℤ)).eval x ≠ 0 := by
      simpa [WeierstrassCurve.ΨSq_two] using hΨ₂
```

depending on what the 2-torsion lemma consumes.

## Keeping the original `[IsSepClosed k]` theorem

To keep exactly the original theorem signature, first add the separable-fiber point-realization lemma:

```lean
theorem exists_nonsingular_of_Ψ₂Sq_eval_ne_zero
    [IsSepClosed k] {x : k} (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ y, (W⁄k).Nonsingular x y := by
  -- Prove the fiber polynomial in `Y`
  --   Y^2 + (a₁*x + a₃) Y - (x^3 + a₂*x^2 + a₄*x + a₆)
  -- is separable from `hΨ₂`, then apply the `IsSepClosed` root theorem.
  -- This replaces the `IsAlgClosed`-based `exists_nonsingular`.
  sorry
```

Then the `→` direction becomes the same proof, with only the realization line changed:

```lean
  · intro hx
    have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 :=
      preΨ'_root_Ψ₂Sq_ne (W := W) (n := n) (x := x) hn hx
    rcases exists_nonsingular_of_Ψ₂Sq_eval_ne_zero (W := W) (x := x) hΨ₂ with ⟨y, h⟩
    let P : (W⁄k).Point := Point.some x y h
    have h₂ : 2 • P ≠ 0 := by
      exact (two_nsmul_ne_zero_iff_Ψ₂Sq_eval_ne_zero (W := W) (x := x) (y := y) h).2 hΨ₂
    have hnP : n • P = 0 := by
      exact
        (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
          (W := W) (n := n) h h₂).mpr hx
    exact ⟨y, h, by simpa [P] using h₂, by simpa [P] using hnP⟩
```

This is the non-strengthened final form I would aim for.  But until `exists_nonsingular_of_Ψ₂Sq_eval_ne_zero` exists, the theorem cannot be closed from only `[IsSepClosed k]` using the current `exists_nonsingular` lemma.

## Import/wiring reminder

The file closing this should import the files that provide:

```lean
import scratch.PointRealization      -- `exists_nonsingular`, if using `[IsAlgClosed k]`
import scratch.SeamE1_Core           -- `preΨ'_root_Ψ₂Sq_ne`
```

and the local torsion file must already contain, or import, the two criteria:

```lean
two_nsmul_ne_zero_iff_Ψ₂Sq_eval_ne_zero
nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
```

If either criterion is currently named differently, the proof above needs only that local name substitution; the term structure is unchanged.
