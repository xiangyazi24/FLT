# Q2833 (dm-codex1): `rat_exists_sq_of_pos_even_padicValRat`

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Namespace: `MazurProof.RationalPointsN12`

## Short answer

I did not find a ready Mathlib theorem saying “a positive rational with even `padicValRat` at every prime is a square.” The realistic route is a small theorem DAG:

1. Convert `padicValRat p t` to numerator/denominator prime exponents with `padicValRat_def` / `padicValRat.multiplicity_sub_multiplicity`.
2. Use `t.reduced : t.num.natAbs.Coprime t.den` to show each prime occurs in at most one of `t.num.natAbs` and `t.den`.
3. Deduce both `t.num.natAbs.factorization p` and `t.den.factorization p` are even.
4. Prove a natural-number lemma: nonzero `n` with even `n.factorization p` for every `p` is a square.
5. Build `r = (a : ℚ) / (b : ℚ)` from `t.num.natAbs = a^2` and `t.den = b^2`.

The hardest block is the natural square lemma via `Nat.factorization`; the rest is API plumbing around `Rat.num`, `Rat.den`, and parity casts.

Useful current Mathlib APIs I checked:

```lean
padicValRat_def
padicValRat.multiplicity_sub_multiplicity
padicValRat.mul
padicValRat.pow
padicValRat.div
padicValRat.inv
Rat.num_ne_zero
Rat.den_ne_zero
Rat.num_divInt_den
Rat.pow_eq_divInt
Nat.factorization_def
Nat.prod_factorization_pow_eq_self
Nat.prod_pow_factorization_eq_self
Nat.eq_of_factorization_eq
Nat.factorization_pow
Nat.factorization_eq_zero_of_not_prime
Int.even_coe_nat
```

Imports I would add for this isolated file:

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic
```

## Lemma DAG and code skeleton

### 1. Natural square criterion from even factorization

This is the clean core lemma. State it with all `p`, not only primes; non-prime factorization is `0` anyway.

```lean
namespace MazurProof.RationalPointsN12

/-- Half the prime-factorization of `n`. -/
noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e / 2) (by simp)

/-- Candidate square root built from half exponents. -/
noncomputable def sqrtOfEvenFactorization (n : ℕ) : ℕ :=
  (halfFactorization n).prod (fun p e => p ^ e)

/-- If every exponent in the factorization of a nonzero natural is even,
then the natural is a square. -/
theorem nat_exists_sq_of_even_factorization
    {n : ℕ} (hn : n ≠ 0)
    (hEven : ∀ p : ℕ, Even (n.factorization p)) :
    ∃ a : ℕ, n = a ^ 2 := by
  classical
  let f : ℕ →₀ ℕ := halfFactorization n
  let a : ℕ := f.prod (fun p e => p ^ e)
  have hf_prime : ∀ p ∈ f.support, Nat.Prime p := by
    intro p hp
    -- `p ∈ f.support` implies `p ∈ n.factorization.support`, hence prime.
    -- Use `support_mapRange`/`Finsupp.mem_support_iff` and
    -- `Nat.prime_of_mem_primeFactors` or the support of `n.factorization`.
    -- Skeleton:
    --   have hp0 : n.factorization p ≠ 0 := ...
    --   exact Nat.prime_of_mem_primeFactors (by simpa using hp0)
    sorry
  have hfac_a : a.factorization = f := by
    -- This is exactly the API from `Data.Nat.Factorization.Defs`:
    -- `Nat.prod_pow_factorization_eq_self hf_prime`.
    simpa [a] using (Nat.prod_pow_factorization_eq_self (f := f) hf_prime)
  have ha_ne : a ≠ 0 := by
    -- product of positive prime powers over finite support.
    -- Alternatively derive from `hfac_a` and `f` if needed.
    dsimp [a]
    exact Finsupp.prod_ne_zero_iff.mpr (by intro p hp; exact pow_ne_zero _ (hf_prime p hp).ne_zero)
  refine ⟨a, ?_⟩
  apply Nat.eq_of_factorization_eq hn (pow_ne_zero 2 ha_ne)
  intro p
  have hpow : (a ^ 2).factorization p = 2 * a.factorization p := by
    -- `Nat.factorization_pow a 2` gives `(a^2).factorization = 2 • a.factorization`.
    simpa [Finsupp.smul_apply, two_mul] using congrFun (congrArg DFunLike.coe (Nat.factorization_pow a 2)) p
  rw [hpow, hfac_a]
  -- Now the goal is `n.factorization p = 2 * (n.factorization p / 2)`.
  -- Because `hEven p` says `n.factorization p = 2*k`, `omega` closes.
  dsimp [f, halfFactorization]
  -- Expected simplifier: `Finsupp.mapRange_apply`.
  -- If it does not fire, rewrite it manually.
  rcases hEven p with ⟨k, hk⟩
  simp [Finsupp.mapRange_apply]
  omega
```

Notes:

* If `Finsupp.mapRange_apply` has a different name locally, avoid it by defining `f` as an explicit finitely-supported function using `n.factorization` and proving extensional equality once.
* The exact line for `hfac_a` is the intended Mathlib API: `Nat.prod_pow_factorization_eq_self` proves `(f.prod (·^·)).factorization = f` when the support of `f` consists of primes.
* `Nat.factorization_pow` is marked `[simp]`, so `simp [hfac_a, halfFactorization]` may close the exponent calculation after `rcases hEven p`.

If the `hf_prime` support proof is annoying, use the equivalence API instead:

```lean
-- Given `hf_prime : ∀ p ∈ f.support, Nat.Prime p`,
-- `(Nat.factorizationEquiv.symm ⟨f, hf_prime⟩).1` is definitionally a positive
-- natural with factorization `f`.
-- `Nat.factorizationEquiv_symm_apply_coe` rewrites it to `f.prod (·^·)`.
```

### 2. Convert `padicValRat` evenness into numerator/denominator evenness

This is the main numerator/denominator API lemma.

```lean
/-- Even rational valuations force even exponents in numerator and denominator
separately, because the rational is in lowest terms. -/
theorem rat_num_den_factorization_even_of_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    (∀ p : ℕ, Even (t.num.natAbs.factorization p)) ∧
    (∀ p : ℕ, Even (t.den.factorization p)) := by
  constructor
  · intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have hv : Even (padicValRat p t) := hval p inferInstance
      have hred : Nat.Coprime t.num.natAbs t.den := t.reduced
      by_cases hpnum : p ∣ t.num.natAbs
      · have hpden : ¬ p ∣ t.den := by
          intro hpd
          have hpgcd : p ∣ Nat.gcd t.num.natAbs t.den := Nat.dvd_gcd hpnum hpd
          have hpone : p ∣ 1 := by simpa [Nat.Coprime] using (by simpa [hred.gcd_eq_one] using hpgcd)
          exact hp.not_dvd_one hpone
        have hden0 : t.den.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpden
        have hvdef : padicValRat p t = (t.num.natAbs.factorization p : ℤ) - (t.den.factorization p : ℤ) := by
          -- Use definitions; `padicValInt p t.num = padicValNat p t.num.natAbs`.
          -- `Nat.factorization_def _ hp` rewrites factorization to `padicValNat`.
          simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
        have : Even ((t.num.natAbs.factorization p : ℤ)) := by
          simpa [hvdef, hden0] using hv
        exact (Int.even_coe_nat _).mp this
      · have hnum0 : t.num.natAbs.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnum
        have hvdef : padicValRat p t = (t.num.natAbs.factorization p : ℤ) - (t.den.factorization p : ℤ) := by
          simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
        -- Here `hv` says `Even (0 - denExp)`, equivalent to `Even denExp`.
        -- This branch is for numerator; it is zero, hence even.
        simp [hnum0]
    · simpa [Nat.factorization_eq_zero_of_not_prime t.num.natAbs hp]
  · intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have hv : Even (padicValRat p t) := hval p inferInstance
      have hred : Nat.Coprime t.num.natAbs t.den := t.reduced
      by_cases hpden : p ∣ t.den
      · have hpnum : ¬ p ∣ t.num.natAbs := by
          intro hpn
          have hpgcd : p ∣ Nat.gcd t.num.natAbs t.den := Nat.dvd_gcd hpn hpden
          have hpone : p ∣ 1 := by simpa [Nat.Coprime] using (by simpa [hred.gcd_eq_one] using hpgcd)
          exact hp.not_dvd_one hpone
        have hnum0 : t.num.natAbs.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnum
        have hvdef : padicValRat p t = (t.num.natAbs.factorization p : ℤ) - (t.den.factorization p : ℤ) := by
          simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
        have : Even (-(t.den.factorization p : ℤ)) := by
          simpa [hvdef, hnum0] using hv
        have : Even ((t.den.factorization p : ℤ)) := by
          simpa using this.neg
        exact (Int.even_coe_nat _).mp this
      · have hden0 : t.den.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpden
        simp [hden0]
    · simpa [Nat.factorization_eq_zero_of_not_prime t.den hp]
```

The two lines involving `hred.gcd_eq_one` may need adaptation. If `t.reduced` is literally `t.num.natAbs.Coprime t.den`, then `hred : Nat.Coprime ...`; use whichever local simp works:

```lean
have hpgcd : p ∣ Nat.gcd t.num.natAbs t.den := Nat.dvd_gcd hpnum hpden
have hpone : p ∣ 1 := by
  simpa [Nat.Coprime] using (by simpa [hred] using hpgcd)
```

or:

```lean
rw [hred] at hpgcd
exact hp.not_dvd_one hpgcd
```

### 3. Turn numerator/denominator squares into a rational square

```lean
/-- If numerator absolute value and denominator are natural squares, and `t>0`,
then `t` is a rational square. -/
theorem rat_exists_sq_of_num_den_squares
    {t : ℚ}
    (htpos : 0 < t)
    (hnum : ∃ a : ℕ, t.num.natAbs = a ^ 2)
    (hden : ∃ b : ℕ, t.den = b ^ 2) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2 := by
  rcases hnum with ⟨a, ha⟩
  rcases hden with ⟨b, hb⟩
  have hnum_pos : 0 < t.num := by
    -- `t > 0` and `t.den > 0` imply `t.num > 0`.
    -- If there is no direct API, use `Rat.num_divInt_den` and positivity.
    -- Common local APIs may include `Rat.num_pos` or be proved by `linarith`.
    sorry
  have hb_ne : (b : ℚ) ≠ 0 := by
    have hden_ne : t.den ≠ 0 := t.den_ne_zero
    intro hb0
    have : t.den = 0 := by
      rw [hb, show b ^ 2 = 0 by exact Nat.pow_eq_zero (by exact_mod_cast hb0) (by norm_num)]
    exact hden_ne this
  refine ⟨(a : ℚ) / (b : ℚ), ?_, ?_⟩
  · -- nonzero follows from numerator nonzero and b nonzero.
    have ha_ne : (a : ℚ) ≠ 0 := by
      intro ha0
      have hnum0 : t.num.natAbs = 0 := by
        rw [ha]
        norm_num [ha0]
      have : t.num = 0 := Int.natAbs_eq_zero.mp hnum0
      linarith
    exact div_ne_zero ha_ne hb_ne
  · -- Since `t.num > 0`, `t.num = (a:ℤ)^2`, not the negative square.
    have hnum_eq : t.num = (a : ℤ) ^ 2 := by
      have hcast : ((t.num.natAbs : ℕ) : ℤ) = ((a ^ 2 : ℕ) : ℤ) := by rw [ha]
      have hnatabs : ((t.num.natAbs : ℕ) : ℤ) = t.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
      rw [hnatabs] at hcast
      simpa using hcast
    -- Now use `Rat.num_divInt_den` and `Rat.pow_eq_divInt`.
    calc
      t = t.num /. t.den := by rw [Rat.num_divInt_den]
      _ = ((a : ℤ) ^ 2) /. ((b : ℕ) ^ 2) := by rw [hnum_eq, hb]
      _ = ((a : ℚ) / (b : ℚ)) ^ 2 := by
        -- Use `Rat.pow_eq_divInt` or `field_simp [hb_ne]`; final goal is pure casts.
        field_simp [hb_ne]
        ring
```

The only nontrivial local nuisance is proving `hnum_pos`. I would isolate it:

```lean
theorem Rat.num_pos_of_pos {t : ℚ} (ht : 0 < t) : 0 < t.num := by
  -- If not already in Mathlib under a nearby name.
  -- Use `t = t.num /. t.den`, `0 < t.den`, and order of `Rat.divInt`.
  sorry
```

If Mathlib has `Rat.num_pos` / `Rat.num_pos_iff_pos`, use it and delete the helper.

### 4. Assemble the generic rational theorem

```lean
theorem rat_exists_sq_of_pos_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2 := by
  have ht_ne : t ≠ 0 := ne_of_gt htpos
  have hnum_ne : t.num.natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ht_ne)
  have hden_ne : t.den ≠ 0 := t.den_ne_zero
  rcases rat_num_den_factorization_even_of_even_padicValRat htpos hval with
    ⟨hnumEven, hdenEven⟩
  have hnumSq : ∃ a : ℕ, t.num.natAbs = a ^ 2 :=
    nat_exists_sq_of_even_factorization hnum_ne hnumEven
  have hdenSq : ∃ b : ℕ, t.den = b ^ 2 :=
    nat_exists_sq_of_even_factorization hden_ne hdenEven
  exact rat_exists_sq_of_num_den_squares htpos hnumSq hdenSq
```

This is the theorem you need downstream.

## If you want a more “compilable now” split

The most robust way to land this in Lean is not to try the full theorem in one commit. Add these in order:

```lean
theorem nat_exists_sq_of_even_factorization
    {n : ℕ} (hn : n ≠ 0)
    (hEven : ∀ p : ℕ, Even (n.factorization p)) :
    ∃ a : ℕ, n = a ^ 2

theorem rat_num_den_factorization_even_of_even_padicValRat
    {t : ℚ}
    (htpos : 0 < t)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p t)) :
    (∀ p : ℕ, Even (t.num.natAbs.factorization p)) ∧
    (∀ p : ℕ, Even (t.den.factorization p))

theorem rat_exists_sq_of_num_den_squares
    {t : ℚ}
    (htpos : 0 < t)
    (hnum : ∃ a : ℕ, t.num.natAbs = a ^ 2)
    (hden : ∃ b : ℕ, t.den = b ^ 2) :
    ∃ r : ℚ, r ≠ 0 ∧ t = r ^ 2
```

Then the target theorem is a four-line assembly. This decomposition avoids mixing factorization extensionality, rational numerator signs, and `padicValRat` rewriting in a single proof state.

## Pitfalls

* `htpos` is essential. Even valuations alone would allow `t = -1`, which is not a square in `ℚ`.
* Use `t.num.natAbs`, not `t.num`, for natural factorization. Recover the positive sign of `t.num` only at the final rational construction step.
* `padicValRat p t` is an integer difference. When one side of the reduced fraction has `p`-valuation zero, use parity of `n` or `-n` and `Int.even_coe_nat` to convert back to Nat parity.
* Do not assume `Nat.factorization p = padicValNat p n` without `p.Prime`; use `Nat.factorization_def n hp` in prime branches and `Nat.factorization_eq_zero_of_not_prime` otherwise.
* `t.reduced` is the key reason numerator and denominator exponents do not both appear. Without reduced numerator/denominator, evenness of the difference would not force each side even.

## Mathlib names to try first

```lean
#check padicValRat_def
#check padicValRat.multiplicity_sub_multiplicity
#check Nat.factorization_def
#check Nat.factorization_pow
#check Nat.prod_factorization_pow_eq_self
#check Nat.prod_pow_factorization_eq_self
#check Nat.eq_of_factorization_eq
#check Nat.factorization_eq_zero_of_not_prime
#check Int.even_coe_nat
#check Rat.num_ne_zero
#check Rat.den_ne_zero
#check Rat.num_divInt_den
#check Rat.pow_eq_divInt
```

I did not find a direct existing theorem for the final square criterion; the lemma DAG above is the shortest realistic route against current Mathlib APIs.
