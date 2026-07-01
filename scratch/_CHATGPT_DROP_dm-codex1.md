# Q2837 (dm-codex1): square criterion from even factorizations / valuations

Namespace: `MazurProof.RationalPointsN12`

## Imports

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Sqrt
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic
```

## Existing Mathlib theorem

For rationals, the key existing theorem is exactly:

```lean
#check Rat.isSquare_iff
-- Rat.isSquare_iff : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den
```

I did **not** find an existing theorem that directly states:

```lean
0 < q → (∀ p, Fact p.Prime → Even (padicValRat p q)) → IsSquare q
```

So use the following DAG.

## 1. Natural square from even factorization

This is the cleanest implementation target. It uses `Nat.factorization` and constructs the square root by halving all exponents.

```lean
namespace MazurProof.RationalPointsN12

noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e / 2) (by simp)

noncomputable def sqrtOfEvenFactorization (n : ℕ) : ℕ :=
  (halfFactorization n).prod (fun p e => p ^ e)

/-- If every prime exponent in a nonzero natural number is even, then it is a square. -/
theorem nat_isSquare_of_factorization_even
    {n : ℕ} (hn : n ≠ 0)
    (hev : ∀ p : ℕ, p.Prime → Even (n.factorization p)) :
    IsSquare n := by
  classical
  let f : ℕ →₀ ℕ := halfFactorization n
  let a : ℕ := f.prod (fun p e => p ^ e)

  have hf_prime : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    have hfp : f p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hnfp : n.factorization p ≠ 0 := by
      intro hzero
      apply hfp
      simp [f, halfFactorization, hzero]
    have hp_mem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hnfp
    simpa [Nat.support_factorization] using Nat.prime_of_mem_primeFactors hp_mem

  have hfac_a : a.factorization = f := by
    simpa [a] using (Nat.prod_pow_factorization_eq_self (f := f) hf_prime)

  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact Finsupp.prod_ne_zero_iff.mpr (by
      intro p hp
      exact pow_ne_zero _ (hf_prime p hp).ne_zero)

  have hfac_pow : ∀ p : ℕ, (a ^ 2).factorization p = 2 * a.factorization p := by
    intro p
    have h := congrFun (congrArg DFunLike.coe (Nat.factorization_pow a 2)) p
    simpa [Finsupp.smul_apply, two_mul] using h

  refine ⟨a, ?_⟩
  apply Nat.eq_of_factorization_eq hn (pow_ne_zero 2 ha_ne)
  intro p
  by_cases hp : p.Prime
  · have he : Even (n.factorization p) := hev p hp
    rcases he with ⟨k, hk⟩
    rw [hfac_pow, hfac_a]
    dsimp [f, halfFactorization]
    -- If your local simp does not know this theorem name, try:
    --   simp [Finsupp.mapRange_apply]
    simp [Finsupp.mapRange_apply]
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    rw [hfac_pow, hfac_a]
    dsimp [f, halfFactorization]
    simp [Finsupp.mapRange_apply, Nat.factorization_eq_zero_of_not_prime n hp]
```

### Possible local API adjustments

The two names most likely to vary are:

```lean
Finsupp.mapRange_apply
Finsupp.prod_ne_zero_iff
```

If `Finsupp.mapRange_apply` does not fire, replace the simp lines by an `ext p` proof of:

```lean
(halfFactorization n) p = n.factorization p / 2
```

If `Finsupp.prod_ne_zero_iff` is unavailable, use the positive product theorem used internally by Mathlib’s factorization equivalence:

```lean
prod_pow_pos_of_zero_notMem_support
```

or define `a` through `Nat.factorizationEquiv.symm ⟨f, hf_prime⟩`, whose value is a positive natural by construction.

## 2. Converting even `padicValRat` to numerator/denominator square data

Use `Rat.isSquare_iff`, so the rational theorem should first prove numerator and denominator are squares.

The denominator is a natural; the numerator is an integer. Because `q > 0`, `q.num > 0`, so it is enough to prove `q.num.natAbs` is a natural square.

```lean
/-- Convert a nonnegative integer whose absolute value is a natural square into an integer square. -/
theorem int_isSquare_of_natAbs_isSquare_of_nonneg {z : ℤ}
    (hz : 0 ≤ z) (hsq : IsSquare z.natAbs) :
    IsSquare z := by
  rcases hsq with ⟨a, ha⟩
  refine ⟨(a : ℤ), ?_⟩
  calc
    z = (z.natAbs : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = (a ^ 2 : ℕ) := by rw [ha]
    _ = (a : ℤ) * (a : ℤ) := by norm_num [pow_two]
```

The API-sensitive numerator/denominator parity lemma is:

```lean
/-- Even rational valuations force even numerator and denominator factorizations separately.
This is the main bridge from `padicValRat` to `Rat.isSquare_iff`. -/
theorem rat_num_den_factorization_even_of_even_padicValRat
    {q : ℚ}
    (hqpos : 0 < q)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    (∀ p : ℕ, p.Prime → Even (q.num.natAbs.factorization p)) ∧
    (∀ p : ℕ, p.Prime → Even (q.den.factorization p)) := by
  constructor
  · intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hv : Even (padicValRat p q) := hval p inferInstance
    have hred : Nat.Coprime q.num.natAbs q.den := q.reduced
    by_cases hpnum : p ∣ q.num.natAbs
    · have hpden : ¬ p ∣ q.den := by
        intro hpd
        have hpgcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpnum hpd
        have hpone : p ∣ 1 := by
          simpa [hred.gcd_eq_one] using hpgcd
        exact hp.not_dvd_one hpone
      have hden0 : q.den.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpden
      have hvdef : padicValRat p q = (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := by
        simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
      have hvnum : Even ((q.num.natAbs.factorization p : ℤ)) := by
        simpa [hvdef, hden0] using hv
      exact (Int.even_coe_nat _).mp hvnum
    · have hnum0 : q.num.natAbs.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnum
      simp [hnum0]
  · intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hv : Even (padicValRat p q) := hval p inferInstance
    have hred : Nat.Coprime q.num.natAbs q.den := q.reduced
    by_cases hpden : p ∣ q.den
    · have hpnum : ¬ p ∣ q.num.natAbs := by
        intro hpn
        have hpgcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpn hpden
        have hpone : p ∣ 1 := by
          simpa [hred.gcd_eq_one] using hpgcd
        exact hp.not_dvd_one hpone
      have hnum0 : q.num.natAbs.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnum
      have hvdef : padicValRat p q = (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := by
        simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
      have hvden_neg : Even (-(q.den.factorization p : ℤ)) := by
        simpa [hvdef, hnum0] using hv
      have hvden : Even ((q.den.factorization p : ℤ)) := by
        simpa using hvden_neg.neg
      exact (Int.even_coe_nat _).mp hvden
    · have hden0 : q.den.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpden
      simp [hden0]
```

Notes:

* `q.reduced` is the key API: `q.num.natAbs.Coprime q.den`.
* The lines using `hred.gcd_eq_one` may need local rewriting as:

```lean
have : Nat.gcd q.num.natAbs q.den = 1 := hred
rw [this] at hpgcd
```

or simply:

```lean
simpa [Nat.Coprime] using hpgcd
```

depending on how `Nat.Coprime` unfolds in your Mathlib snapshot.

## 3. Rational square criterion using `Rat.isSquare_iff`

```lean
/-- Positive rational with even `p`-adic valuation at every prime is a square. -/
theorem rat_isSquare_of_pos_even_padicValRat
    {q : ℚ}
    (hqpos : 0 < q)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    IsSquare q := by
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hnum_ne : q.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hqne)
  have hden_ne : q.den ≠ 0 := q.den_ne_zero

  rcases rat_num_den_factorization_even_of_even_padicValRat hqpos hval with
    ⟨hnumEven, hdenEven⟩

  have hnumSqNat : IsSquare q.num.natAbs :=
    nat_isSquare_of_factorization_even hnum_ne hnumEven
  have hdenSq : IsSquare q.den :=
    nat_isSquare_of_factorization_even hden_ne hdenEven

  have hnum_nonneg : 0 ≤ q.num := by
    -- In current Mathlib, try first:
    --   exact le_of_lt (Rat.num_pos.mpr hqpos)
    -- If there is no `Rat.num_pos`, prove it from `q = q.num /. q.den` and `q.den_pos`.
    -- This is the only remaining small Rat-order API nuisance.
    have hnum_pos : 0 < q.num := by
      -- local helper recommended:
      -- theorem Rat.num_pos_of_pos {q : ℚ} (hq : 0 < q) : 0 < q.num := by ...
      exact Rat.num_pos.mpr hqpos
    exact le_of_lt hnum_pos

  have hnumSqInt : IsSquare q.num :=
    int_isSquare_of_natAbs_isSquare_of_nonneg hnum_nonneg hnumSqNat

  exact Rat.isSquare_iff.mpr ⟨hnumSqInt, hdenSq⟩

/-- Existential square-root form used by the N12 squareclass extraction. -/
theorem rat_exists_sq_of_pos_even_padicValRat
    {q : ℚ}
    (hqpos : 0 < q)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    ∃ r : ℚ, r ≠ 0 ∧ q = r ^ 2 := by
  rcases rat_isSquare_of_pos_even_padicValRat hqpos hval with ⟨r, hr⟩
  refine ⟨r, ?_, ?_⟩
  · intro hr0
    subst r
    -- `hr : q = 0 * 0`, contradiction with q>0.
    have : q = 0 := by simpa using hr
    exact (ne_of_gt hqpos) this
  · simpa [pow_two] using hr
```

If your local `IsSquare` witness equation is oriented as `r * r = q` rather than `q = r * r`, swap the last two `simpa` uses. In current Mathlib, `IsSquare.zero` is proved with `(mul_zero _).symm`, so the orientation is `q = r * r`.

## Exact unknown API names to check first

```lean
#check Rat.isSquare_iff
#check Rat.num_pos
#check Rat.num_ne_zero
#check Rat.den_ne_zero
#check Rat.num_divInt_den
#check Nat.prod_pow_factorization_eq_self
#check Nat.prod_factorization_pow_eq_self
#check Nat.eq_of_factorization_eq
#check Nat.factorization_pow
#check Nat.factorization_def
#check Finsupp.mapRange_apply
#check Finsupp.prod_ne_zero_iff
#check Int.even_coe_nat
```

If `Rat.num_pos` is not present, add this helper:

```lean
theorem Rat.num_pos_of_pos {q : ℚ} (hq : 0 < q) : 0 < q.num := by
  -- Use `q = q.num /. q.den`, `q.den_pos`, and order properties of `Rat.divInt`.
  -- In many snapshots this is already available as `Rat.num_pos` or equivalent.
  -- This helper is independent of the valuation/factorization work.
  sorry
```

## Summary

The best landing sequence is:

1. `nat_isSquare_of_factorization_even` using `Nat.factorization` and half exponents.
2. `rat_num_den_factorization_even_of_even_padicValRat` using `q.reduced` and `padicValRat_def`.
3. `rat_isSquare_of_pos_even_padicValRat` using `Rat.isSquare_iff`.
4. `rat_exists_sq_of_pos_even_padicValRat` by unpacking `IsSquare` and using positivity for nonzero root.

The natural-square theorem is the key reusable kernel; the rational theorem is mostly numerator/denominator plumbing once that kernel is available.
```
