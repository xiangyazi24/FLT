# Q2823 dm-codex2: `E1FactorEvenPadicOutside23Statement` skeleton

Namespace: `MazurProof.RationalPointsN12`.

The local WIP helpers named in the prompt are enough. The cleanest proof is to prove one local valuation lemma for the triple

```lean
vX   := padicValRat p X
vXm1 := padicValRat p (X - 1)
vXp3 := padicValRat p (X + 3)
```

and then project its three `Even` conclusions into the three `EvenPadicOutside23` fields.

## 1. Math check

The pure integer lemma is exactly the right shape.

The false shortcut would be: “outside `2,3`, at most one of the three valuations is nonzero.” That is false when all three valuations are equal and negative. Example pattern: `vX = vXm1 = vXp3 = -2` is compatible with all pairwise unit-difference constraints.

Your lemma instead uses the correct local facts:

* if two factors differ by a `p`-adic unit and their valuations are strictly unequal, the smaller valuation is `0`;
* two such factors cannot both have positive valuation;
* the curve equation makes `vX + vXm1 + vXp3` even.

This covers the equal-negative case: if `vX = vXm1 = vXp3 = n < 0`, then the sum condition says `3*n` is even, hence `n` is even.

## 2. Pairwise difference equalities

Use these six equalities for the strict-inequality hypotheses:

```lean
X - (X - 1) = (1 : ℚ)
(X - 1) - X = (-1 : ℚ)
X - (X + 3) = (-3 : ℚ)
(X + 3) - X = (3 : ℚ)
(X - 1) - (X + 3) = (-4 : ℚ)
(X + 3) - (X - 1) = (4 : ℚ)
```

For the three `not_both_pos` hypotheses, it is enough to use the forward differences

```lean
X - (X - 1) = 1
X - (X + 3) = -3
(X - 1) - (X + 3) = -4
```

with unit valuation of `1`, `-3`, `-4` respectively.

## 3. Tiny local valuation-zero helpers

You already have `padicValRat_three_of_prime_ne_three` and `padicValRat_four_of_prime_ne_two`. The only nuisance is negative signs. In most current Mathlib/WIP contexts, `simpa` knows neg-invariance for `padicValRat`; if not, add a local helper using the local neg theorem name.

```lean
private theorem padicValRat_one_eq_zero (p : ℕ) [Fact p.Prime] :
    padicValRat p (1 : ℚ) = 0 := by
  simp

private theorem padicValRat_neg_one_eq_zero (p : ℕ) [Fact p.Prime] :
    padicValRat p (-1 : ℚ) = 0 := by
  simp

private theorem padicValRat_neg_three_of_prime_ne_three
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    padicValRat p (-3 : ℚ) = 0 := by
  simpa using (padicValRat_three_of_prime_ne_three (p := p) hp3)

private theorem padicValRat_neg_four_of_prime_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (-4 : ℚ) = 0 := by
  simpa using (padicValRat_four_of_prime_ne_two (p := p) hp2)
```

If either negative lemma fails, replace its proof by the local neg API. Common names are usually one of these shapes:

```lean
-- Example repair if needed; adapt theorem name to local Mathlib.
-- simpa using (padicValRat.neg (p := p) (q := (3 : ℚ))).trans
--   (padicValRat_three_of_prime_ne_three (p := p) hp3)
```

## 4. Sum-even lemma from the curve equation

The curve equation gives

```lean
2 * padicValRat p Y =
  padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3)
```

using `padicValRat.pow` on `Y^2` and `padicValRat.mul` twice on the right-hand product.

Skeleton:

```lean
private theorem e1_padic_factor_sum_even
    {X Y : ℚ} {p : ℕ} [Fact p.Prime]
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hX0 : X ≠ 0) (hXm10 : X - 1 ≠ 0) (hXp30 : X + 3 ≠ 0) :
    Even (padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3)) := by
  have hcurve : Y ^ 2 = X * (X - 1) * (X + 3) := by
    simpa [E1FullCoverCurve] using hE

  have hYpow : padicValRat p (Y ^ 2) = 2 * padicValRat p Y := by
    -- If the local theorem requires nonzero, pass `hY` as the final argument.
    simpa using (padicValRat.pow (p := p) (q := Y) (n := 2))

  have hprod :
      padicValRat p (X * (X - 1) * (X + 3)) =
        padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3) := by
    -- Variant A: if `padicValRat.mul` has no explicit nonzero hypotheses.
    rw [padicValRat.mul, padicValRat.mul]
    ring

    -- Variant B: if the local theorem requires nonzero hypotheses, use this instead:
    -- have hXXm1 : X * (X - 1) ≠ 0 := mul_ne_zero hX0 hXm10
    -- rw [padicValRat.mul (p := p) (q := X * (X - 1)) (r := X + 3) hXXm1 hXp30]
    -- rw [padicValRat.mul (p := p) (q := X) (r := X - 1) hX0 hXm10]
    -- ring

  have hsum_eq :
      padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3) =
        2 * padicValRat p Y := by
    calc
      padicValRat p X + padicValRat p (X - 1) + padicValRat p (X + 3)
          = padicValRat p (X * (X - 1) * (X + 3)) := hprod.symm
      _ = padicValRat p (Y ^ 2) := by rw [← hcurve]
      _ = 2 * padicValRat p Y := hYpow

  -- `Even` on integers is normally existential; this avoids relying on a named parity lemma.
  refine ⟨padicValRat p Y, ?_⟩
  omega
```

If the `Even` constructor in the local file expects `n = r + r` rather than `n = 2*r`, the final `omega` still closes the witness goal.

## 5. Main valuation-triple lemma

This is the shortest useful helper. It packages the sum-even fact and all nine pairwise hypotheses for your pure integer lemma.

```lean
private theorem e1_padic_factors_even_outside23
    {X Y : ℚ} {p : ℕ} [Fact p.Prime]
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Even (padicValRat p X) ∧
      Even (padicValRat p (X - 1)) ∧
      Even (padicValRat p (X + 3)) := by
  obtain ⟨hX0, hXm10, hXp30⟩ :=
    e1FullCoverCurve_factors_ne_zero (X := X) (Y := Y) hE hY

  let vX : ℤ := padicValRat p X
  let vXm1 : ℤ := padicValRat p (X - 1)
  let vXp3 : ℤ := padicValRat p (X + 3)

  have hsum : Even (vX + vXm1 + vXp3) := by
    dsimp [vX, vXm1, vXp3]
    exact e1_padic_factor_sum_even
      (X := X) (Y := Y) (p := p) hE hY hX0 hXm10 hXp30

  have hv1 : padicValRat p (1 : ℚ) = 0 := padicValRat_one_eq_zero p
  have hvm1 : padicValRat p (-1 : ℚ) = 0 := padicValRat_neg_one_eq_zero p
  have hv3 : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_three_of_prime_ne_three (p := p) hp3
  have hvm3 : padicValRat p (-3 : ℚ) = 0 :=
    padicValRat_neg_three_of_prime_ne_three (p := p) hp3
  have hv4 : padicValRat p (4 : ℚ) = 0 :=
    padicValRat_four_of_prime_ne_two (p := p) hp2
  have hvm4 : padicValRat p (-4 : ℚ) = 0 :=
    padicValRat_neg_four_of_prime_ne_two (p := p) hp2

  have hab_lt : vX < vXm1 → vX = 0 := by
    intro hlt
    dsimp [vX, vXm1] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X) (b := X - 1) (c := (1 : ℚ))
      (by ring) (by norm_num) hv1 hlt

  have hba_lt : vXm1 < vX → vXm1 = 0 := by
    intro hlt
    dsimp [vX, vXm1] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X - 1) (b := X) (c := (-1 : ℚ))
      (by ring) (by norm_num) hvm1 hlt

  have hac_lt : vX < vXp3 → vX = 0 := by
    intro hlt
    dsimp [vX, vXp3] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X) (b := X + 3) (c := (-3 : ℚ))
      (by ring) (by norm_num) hvm3 hlt

  have hca_lt : vXp3 < vX → vXp3 = 0 := by
    intro hlt
    dsimp [vX, vXp3] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X + 3) (b := X) (c := (3 : ℚ))
      (by ring) (by norm_num) hv3 hlt

  have hbc_lt : vXm1 < vXp3 → vXm1 = 0 := by
    intro hlt
    dsimp [vXm1, vXp3] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X - 1) (b := X + 3) (c := (-4 : ℚ))
      (by ring) (by norm_num) hvm4 hlt

  have hcb_lt : vXp3 < vXm1 → vXp3 = 0 := by
    intro hlt
    dsimp [vXm1, vXp3] at hlt ⊢
    exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
      (p := p) (a := X + 3) (b := X - 1) (c := (4 : ℚ))
      (by ring) (by norm_num) hv4 hlt

  have hab_pos : ¬ (0 < vX ∧ 0 < vXm1) := by
    dsimp [vX, vXm1]
    exact padicValRat_not_both_pos_of_sub_val_zero
      (p := p) (a := X) (b := X - 1) (c := (1 : ℚ))
      (by ring) (by norm_num) hv1

  have hac_pos : ¬ (0 < vX ∧ 0 < vXp3) := by
    dsimp [vX, vXp3]
    exact padicValRat_not_both_pos_of_sub_val_zero
      (p := p) (a := X) (b := X + 3) (c := (-3 : ℚ))
      (by ring) (by norm_num) hvm3

  have hbc_pos : ¬ (0 < vXm1 ∧ 0 < vXp3) := by
    dsimp [vXm1, vXp3]
    exact padicValRat_not_both_pos_of_sub_val_zero
      (p := p) (a := X - 1) (b := X + 3) (c := (-4 : ℚ))
      (by ring) (by norm_num) hvm4

  have h := even_each_of_sum_even_of_pairwise_unit_val
    (a := vX) (b := vXm1) (c := vXp3)
    hsum hab_lt hba_lt hac_lt hca_lt hbc_lt hcb_lt
    hab_pos hac_pos hbc_pos

  simpa [vX, vXm1, vXp3] using h
```

Tactic notes:

* The six difference goals are all closed by `ring`.
* The nonzero constants are closed by `norm_num`.
* The final `simpa [vX, vXm1, vXp3]` unfolds the local abbreviations.
* If `dsimp` does not unfold the `let` values under inequalities, replace `dsimp [vX, vXm1, vXp3]` by `change padicValRat p X < padicValRat p (X - 1) → padicValRat p X = 0` in the relevant branch.

## 6. Final theorem skeleton

```lean
theorem e1FactorEvenPadicOutside23Statement_proof :
    E1FactorEvenPadicOutside23Statement := by
  intro X Y hE hY
  obtain ⟨hX0, hXm10, hXp30⟩ :=
    e1FullCoverCurve_factors_ne_zero (X := X) (Y := Y) hE hY

  refine ⟨?_, ?_, ?_⟩

  · refine ⟨hX0, ?_⟩
    intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23
      (X := X) (Y := Y) (p := p) hE hY hp2 hp3).1

  · refine ⟨hXm10, ?_⟩
    intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23
      (X := X) (Y := Y) (p := p) hE hY hp2 hp3).2.1

  · refine ⟨hXp30, ?_⟩
    intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23
      (X := X) (Y := Y) (p := p) hE hY hp2 hp3).2.2
```

If the file wants a theorem with the exact proposition name, use the local naming convention, for example:

```lean
theorem E1FactorEvenPadicOutside23Statement_proved :
    E1FactorEvenPadicOutside23Statement := by
  exact e1FactorEvenPadicOutside23Statement_proof
```

## 7. Shortest assembly variant

To avoid recomputing the triple lemma three times, package it inside the final theorem:

```lean
theorem e1FactorEvenPadicOutside23Statement_proof :
    E1FactorEvenPadicOutside23Statement := by
  intro X Y hE hY
  obtain ⟨hX0, hXm10, hXp30⟩ :=
    e1FullCoverCurve_factors_ne_zero (X := X) (Y := Y) hE hY
  refine ⟨⟨hX0, ?_⟩, ⟨hXm10, ?_⟩, ⟨hXp30, ?_⟩⟩
  · intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23 (X := X) (Y := Y) (p := p) hE hY hp2 hp3).1
  · intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23 (X := X) (Y := Y) (p := p) hE hY hp2 hp3).2.1
  · intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    exact (e1_padic_factors_even_outside23 (X := X) (Y := Y) (p := p) hE hY hp2 hp3).2.2
```

## 8. Likely API adjustments

The only likely nontrivial API adjustments are:

1. `padicValRat.pow` may require a nonzero hypothesis for `Y`; pass `hY` if Lean reports a missing argument.
2. `padicValRat.mul` may require nonzero hypotheses. Use `hX0`, `hXm10`, `hXp30`, and `mul_ne_zero hX0 hXm10`.
3. `padicValRat (-q)` simplification may not fire. Add a one-line neg-invariance helper using the local theorem name; after that `-3` and `-4` are immediate from your existing `three`/`four` lemmas.
4. If `Even` unfolds to `∃ k, n = k + k`, `omega` closes the witness goal after `refine ⟨padicValRat p Y, ?_⟩`.
5. Do not use `nlinarith` for valuation parity. Use `omega` because all valuation expressions are integers.
