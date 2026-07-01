# Q2822 (dm-codex1): route for `SquareclassSupportedOn23OfEvenPadicOutside23Statement`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local worktree: `/Users/huangx/repos/flt-ai`  
Namespace: `MazurProof.RationalPointsN12`

## Verdict

The statement is true as written because `EvenPadicOutside23 q` includes `q ≠ 0`.

Without `q ≠ 0`, it would be false for your `SquareclassBy`, because `SquareclassBy 0 d` requires

```lean
∃ r : ℚ, r ≠ 0 ∧ 0 = (d : ℚ) * r ^ 2
```

and every `d ∈ S23` is nonzero.

The shortest realistic Lean route is **not** to construct a full rational squarefree kernel directly. Instead:

1. Define the `{±1,±2,±3,±6}` representative `d` from the sign of `q` and the parities of `padicValRat 2 q` and `padicValRat 3 q`.
2. Prove `q / d` is positive and has even `p`-adic valuation for **every** prime `p`.
3. Use a standalone theorem: a positive rational whose `p`-adic valuation is even at every prime is a rational square.
4. Multiply back by `d`.

This isolates the genuinely hard part into one reusable theorem about positive rationals.

Mathlib APIs confirmed useful from `Mathlib.NumberTheory.Padics.PadicVal.Basic`:

```lean
padicValRat.defn
padicValRat.multiplicity_sub_multiplicity
padicValRat.mul
padicValRat.pow
padicValRat.inv
padicValRat.div
```

For rational numerator/denominator work, useful APIs include:

```lean
Rat.num_ne_zero
Rat.den_ne_zero
Rat.num_divInt_den
Rat.pow_eq_divInt
Rat.div_def'
q.reduced        -- field of the Rat structure: q.num.natAbs.Coprime q.den
```

I found no ready-made Mathlib theorem named like `Rat.isSquare_intCast_iff` or `padicValRat square even`, so expect to prove the square criterion below.

## Imports

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12
```

Your local file already imports `Mathlib.NumberTheory.Padics.PadicVal.Basic` and `Mathlib.Tactic`; add `Mathlib.Data.Rat.Lemmas` only if the `Rat.num`/`Rat.den` lemmas are not already available transitively.

## Step 1: choose the representative `d ∈ S23`

Use parity of the valuations at `2` and `3`, and the sign of `q`.

```lean
/-- The signed squareclass representative supported on `{2,3}`.
It is one of `±1, ±2, ±3, ±6`. -/
noncomputable def sqclass23Rep (q : ℚ) : ℤ :=
  (if q < 0 then (-1 : ℤ) else 1) *
  (if Even (padicValRat 2 q) then (1 : ℤ) else 2) *
  (if Even (padicValRat 3 q) then (1 : ℤ) else 3)
```

The first small finite lemma is just cases on the three `if`s:

```lean
theorem sqclass23Rep_mem (q : ℚ) : InS23 (sqclass23Rep q) := by
  unfold sqclass23Rep InS23 S23
  by_cases hs : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hs, h2, h3]

theorem sqclass23Rep_ne_zero (q : ℚ) : sqclass23Rep q ≠ 0 := by
  unfold sqclass23Rep
  by_cases hs : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  norm_num [hs, h2, h3]
```

You also want a cast version:

```lean
theorem sqclass23Rep_rat_ne_zero (q : ℚ) :
    ((sqclass23Rep q : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast sqclass23Rep_ne_zero q
```

## Step 2: `q / d` is positive

Since `d` has the same sign as `q`, `q / d` is positive.

```lean
theorem sqclass23Rep_same_sign {q : ℚ} (hq0 : q ≠ 0) :
    0 < q / ((sqclass23Rep q : ℤ) : ℚ) := by
  unfold sqclass23Rep
  by_cases hqneg : q < 0
  · -- d is negative; q / d is positive.
    by_cases h2 : Even (padicValRat 2 q) <;>
    by_cases h3 : Even (padicValRat 3 q) <;>
    norm_num [hqneg, h2, h3]
    positivity
  · have hqpos : 0 < q := lt_of_le_of_ne (le_of_not_gt hqneg) (Ne.symm hq0)
    by_cases h2 : Even (padicValRat 2 q) <;>
    by_cases h3 : Even (padicValRat 3 q) <;>
    norm_num [hqneg, h2, h3]
    positivity
```

If `positivity` does not close the negative case, replace it by `have : 0 < -q := neg_pos.mpr hqneg` and `field_simp`.

## Step 3: valuation parity of `q / d`

First prove the valuation of the finite representative. It is easier to expose only parity, not exact valuations.

```lean
/-- Outside `{2,3}`, the chosen representative has zero valuation. -/
theorem even_padicValRat_sqclass23Rep_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (q : ℚ) :
    Even (padicValRat p (((sqclass23Rep q : ℤ) : ℚ))) := by
  unfold sqclass23Rep
  by_cases hs : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  -- all cases reduce to valuations of ±1, ±2, ±3, ±6 at p outside {2,3}
  -- use `padicValRat.mul`, `padicValRat.neg`, `padicValRat.of_int`, and
  -- `padicValInt.eq_zero_of_not_dvd`; `norm_num [hp2, hp3]` often closes.
  norm_num [hs, h2, h3, hp2, hp3]

/-- At `2`, subtracting the chosen factor makes the valuation even. -/
theorem even_padicValRat_div_sqclass23Rep_at_two
    {q : ℚ} (hq0 : q ≠ 0) :
    Even (padicValRat 2 (q / (((sqclass23Rep q : ℤ) : ℚ)))) := by
  have hd0 : (((sqclass23Rep q : ℤ) : ℚ)) ≠ 0 := sqclass23Rep_rat_ne_zero q
  rw [padicValRat.div hq0 hd0]
  unfold sqclass23Rep
  by_cases hs : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  -- if h2, the representative has 2-valuation 0; otherwise 1.
  -- In both cases `v2(q)-v2(d)` is even.
  norm_num [hs, h2, h3]

/-- At `3`, subtracting the chosen factor makes the valuation even. -/
theorem even_padicValRat_div_sqclass23Rep_at_three
    {q : ℚ} (hq0 : q ≠ 0) :
    Even (padicValRat 3 (q / (((sqclass23Rep q : ℤ) : ℚ)))) := by
  have hd0 : (((sqclass23Rep q : ℤ) : ℚ)) ≠ 0 := sqclass23Rep_rat_ne_zero q
  rw [padicValRat.div hq0 hd0]
  unfold sqclass23Rep
  by_cases hs : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  norm_num [hs, h2, h3]

/-- All prime valuations of `q / sqclass23Rep q` are even. -/
theorem even_padicValRat_div_sqclass23Rep_all
    {q : ℚ}
    (hq : EvenPadicOutside23 q) :
    ∀ p : ℕ, Fact p.Prime →
      Even (padicValRat p (q / (((sqclass23Rep q : ℤ) : ℚ)))) := by
  intro p hp
  rcases hq with ⟨hq0, houtside⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact even_padicValRat_div_sqclass23Rep_at_two hq0
  · by_cases hp3 : p = 3
    · subst hp3
      exact even_padicValRat_div_sqclass23Rep_at_three hq0
    · have hd0 : (((sqclass23Rep q : ℤ) : ℚ)) ≠ 0 := sqclass23Rep_rat_ne_zero q
      rw [padicValRat.div hq0 hd0]
      exact Even.sub (houtside p hp hp2 hp3)
        (even_padicValRat_sqclass23Rep_outside23 hp2 hp3 q)
```

The exact valuation lemmas for `2` and `3` may need a little more manual `padicValRat.mul` rewriting than the skeleton shows, but they are finite eight-case goals and are not the hard part.

## Step 4: positive rational with all valuations even is a square

This is the main reusable theorem. It is the only genuinely substantial sublemma.

```lean
/-- Positive rational square criterion via all prime valuations. -/
theorem rat_exists_sq_of_pos_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2 := by
  -- Prove by numerator/denominator.
  -- This is the recommended hard lemma to isolate.
  -- See the DAG below.
  sorry
```

### DAG for this square criterion

Use `Rat.num`/`Rat.den`, not a global rational UFD proof.

#### 4.1 Even exponents for numerator and denominator separately

For `t > 0`, `t.num` is positive and `t.den` is positive. Since `t.num.natAbs` and `t.den` are coprime, a prime cannot occur in both. Therefore evenness of

```lean
padicValRat p t = padicValInt p t.num - padicValNat p t.den
```

forces both individual exponents to be even.

```lean
theorem rat_num_den_even_of_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    (∀ p : ℕ, Fact p.Prime → Even (padicValInt p t.num)) ∧
    (∀ p : ℕ, Fact p.Prime → Even (padicValNat p t.den)) := by
  -- APIs:
  --   padicValRat_def
  --   padicValRat.multiplicity_sub_multiplicity
  --   t.reduced : t.num.natAbs.Coprime t.den
  --   padicValInt.eq_zero_iff / padicValNat.eq_zero_iff
  -- Route for each prime p:
  --   by_cases hpnum : (p:ℤ) ∣ t.num
  --   · coprimality implies ¬ p ∣ t.den, so denominator valuation is 0.
  --     Then hval gives numerator valuation even.
  --   · numerator valuation is 0, and hval gives denominator valuation even
  --     because `0 - vden` even iff `vden` even.
  sorry
```

#### 4.2 Natural number square criterion from even prime exponents

This is a clean `Nat.factorization` lemma.

```lean
/-- A natural number is a square if every prime exponent in its factorization is even. -/
theorem nat_exists_sq_of_even_prime_factorization
    {n : ℕ}
    (h : ∀ p : ℕ, Fact p.Prime → Even (n.factorization p)) :
    ∃ a : ℕ, n = a ^ 2 := by
  -- Use `Nat.factorization`.
  -- Define `a.factorization p = n.factorization p / 2` on primes in support.
  -- More practical in Mathlib: use `n.factorization` as a finsupp and the theorem
  -- `Nat.prod_factorization_eq_self` / equivalent, then construct
  --   a = n.factorization.prod fun p e => p ^ (e / 2)
  -- and prove by factorization extensionality.
  -- API names to look for if exact names differ:
  --   Nat.factorization
  --   Nat.factorization_mul
  --   Nat.factorization_pow
  --   Nat.factorization_eq_zero_of_not_dvd
  --   Nat.prod_factorization_eq_self
  sorry
```

You can also state it using `IsSquare n` if the local file imports an `IsSquare` API:

```lean
theorem nat_isSquare_of_even_prime_factorization
    {n : ℕ}
    (h : ∀ p : ℕ, Fact p.Prime → Even (n.factorization p)) :
    IsSquare n := by
  rcases nat_exists_sq_of_even_prime_factorization h with ⟨a, ha⟩
  exact ⟨a, ha⟩
```

#### 4.3 Convert numerator/denominator squares into a rational square

```lean
theorem rat_exists_sq_of_num_den_squares
    {t : ℚ}
    (htpos : 0 < t)
    (hnum : ∃ a : ℕ, t.num.natAbs = a ^ 2)
    (hden : ∃ b : ℕ, t.den = b ^ 2) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2 := by
  rcases hnum with ⟨a, ha⟩
  rcases hden with ⟨b, hb⟩
  refine ⟨(a : ℚ) / (b : ℚ), ?_, ?_⟩
  · -- nonzero: t>0 implies num and den are nonzero, hence a,b nonzero
    -- use `ha`, `hb`, `Rat.den_ne_zero`, and positivity of t.num from htpos.
    sorry
  · -- since t>0, `t.num = (a:ℤ)^2`, not negative.
    -- use `Rat.num_divInt_den`, `Rat.pow_eq_divInt`, `ha`, `hb`.
    sorry
```

Then assemble:

```lean
theorem rat_exists_sq_of_pos_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2 := by
  rcases rat_num_den_even_of_even_padicValRat htpos hval with ⟨hnumEven, hdenEven⟩
  have hnumSq : ∃ a : ℕ, t.num.natAbs = a ^ 2 :=
    nat_exists_sq_of_even_prime_factorization (by
      intro p hp
      -- `padicValInt p t.num` is `padicValNat p t.num.natAbs`.
      simpa [padicValInt] using hnumEven p hp)
  have hdenSq : ∃ b : ℕ, t.den = b ^ 2 :=
    nat_exists_sq_of_even_prime_factorization (by
      intro p hp
      simpa using hdenEven p hp)
  exact rat_exists_sq_of_num_den_squares htpos hnumSq hdenSq
```

This theorem is useful beyond this residual; keep it generic.

## Step 5: final residual assembly

Now the target theorem is short.

```lean
theorem squareclassSupportedOn23OfEvenPadicOutside23_checked :
    SquareclassSupportedOn23OfEvenPadicOutside23Statement := by
  intro q hq
  rcases hq with ⟨hq0, houtside⟩
  let d : ℤ := sqclass23Rep q
  have hdmem : InS23 d := by
    simpa [d] using sqclass23Rep_mem q
  have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by
    simpa [d] using sqclass23Rep_rat_ne_zero q
  have htpos : 0 < q / ((d : ℤ) : ℚ) := by
    simpa [d] using sqclass23Rep_same_sign hq0
  have hteven : ∀ p : ℕ, Fact p.Prime →
      Even (padicValRat p (q / ((d : ℤ) : ℚ))) := by
    simpa [d] using even_padicValRat_div_sqclass23Rep_all (q := q) ⟨hq0, houtside⟩
  rcases rat_exists_sq_of_pos_even_padicValRat htpos hteven with ⟨r, hr0, hsq⟩
  refine ⟨hq0, d, hdmem, ?_⟩
  refine ⟨r, hr0, ?_⟩
  -- hsq : q / d = r^2
  -- goal : q = d * r^2
  field_simp [hd0] at hsq ⊢
  exact hsq
```

Depending on `field_simp`, the last lines may need:

```lean
  calc
    q = ((d : ℚ)) * (q / ((d : ℚ))) := by field_simp [hd0]
    _ = ((d : ℚ)) * r ^ 2 := by rw [hsq]
```

## Alternative: direct numerator/denominator squarefree kernel

If the `Nat.factorization` square criterion is more convenient than all-prime `padicValRat` parity, you can skip `sqclass23Rep` first and build the squarefree kernel of `q.num` and `q.den`.

Target theorem:

```lean
theorem rat_squareclass_supported23_of_even_outside23_num_den
    {q : ℚ}
    (hq0 : q ≠ 0)
    (hout : ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 →
      Even (padicValRat p q)) :
    ∃ d : ℤ, InS23 d ∧ ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2 := by
  -- Build d by sign and parity of v2/v3 exactly as above, then apply the
  -- positive all-even square criterion to q/d.
  -- This is usually shorter than separately constructing squarefree kernels
  -- for numerator and denominator.
  sorry
```

The direct kernel route is conceptually fine, but it duplicates the same proof work: you must still show every prime outside `{2,3}` has even exponent in both numerator and denominator. The `q/d` square criterion centralizes that work.

## Pitfalls

1. **The statement needs `q ≠ 0`.** Your definition includes it; keep it threaded through every lemma.
2. **All-even valuations alone do not imply a rational square.** Example: `-1` has all valuations even but is not a square in `ℚ`. The square criterion must assume `0 < t`. This is why `d` includes the sign of `q`.
3. **Parity at `2` and `3` can be negative.** Use `Even (padicValRat p q)` over `ℤ`, not `Nat` parity. Subtracting `1` changes parity correctly even for negative valuations.
4. **Do not try to decide `d` from numerator divisibility only.** Denominator exponents matter; `padicValRat 2 q` and `padicValRat 3 q` already encode numerator minus denominator.
5. **Keep `rat_exists_sq_of_pos_even_padicValRat` generic.** It will also be useful for product-squareclass and future descent bridges.
6. **The finite membership proof for `d ∈ S23` is trivial only if `S23` is unfolded.** Your `S23` order is `[1, -1, 2, -2, 3, -3, 6, -6]`; the `simp` proof above matches that.

## Minimal lemma DAG

```text
sqclass23Rep
  ├─ sqclass23Rep_mem
  ├─ sqclass23Rep_rat_ne_zero
  ├─ sqclass23Rep_same_sign
  └─ even_padicValRat_div_sqclass23Rep_all
        ├─ at p=2 finite cases
        ├─ at p=3 finite cases
        └─ outside 2,3 from hypothesis and valuation of d = 0

rat_exists_sq_of_pos_even_padicValRat
  ├─ rat_num_den_even_of_even_padicValRat
  │    ├─ padicValRat_def / multiplicity_sub_multiplicity
  │    └─ q.reduced coprimality of num/den
  ├─ nat_exists_sq_of_even_prime_factorization
  └─ rat_exists_sq_of_num_den_squares

squareclassSupportedOn23OfEvenPadicOutside23_checked
  └─ choose d = sqclass23Rep q, square-root q/d, multiply back
```

This is the shortest route I would expect to survive Lean implementation without a large bespoke rational squarefree-kernel development.
