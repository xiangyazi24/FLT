# Q2283: Lean-facing plan for `quartic_B_split_two_squares_explicit`

Target file: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

Goal:

```lean
theorem quartic_B_split_two_squares_explicit
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hu : Odd u)
    (hv : Odd v)
    (hB : Z ^ 2 = (3*u^2 - v^2)*(u^2 + v^2)) :
    ∃ r s : ℤ,
      3*u^2 - v^2 = 2*r^2 ∧
      u^2 + v^2 = 2*s^2
```

The right formalization is elementary.  Do not make the whole theorem a curve-specific residual.  The only generic helper worth adding is the standard fact that positive coprime integer factors of a square are squares.

The extra downstream hypothesis `u^2 ≠ v^2` is not needed for this split lemma.

---

## A. Mathematical proof obligation

Let

```lean
A = 3*u^2 - v^2
B = u^2 + v^2
```

Oddness gives visible halves:

* `A = 2*a` with `Odd a`;
* `B = 2*b` with `Odd b`.

This is Lean-friendlier than working directly with `% 8`.  It implies the needed “one factor of two” information.  If desired, one can also prove the stronger `Int.ModEq` facts `A ≡ 2 [ZMOD 8]` and `B ≡ 2 [ZMOD 8]`, because odd squares are `1 mod 8`.

Positivity:

* `B > 0` follows from `u * v ≠ 0`.
* `Z^2 = A*B` and `B > 0` imply `A ≥ 0`.
* `A ≠ 0`: otherwise `v^2 = 3*u^2`; prime `3` divides `v`, then divides `u`, contradicting `Int.gcd u v = 1`.
* Hence `A > 0`, so the half `a` is positive.  Also `b > 0`.

Coprimality of halves:

* An odd prime dividing both `a` and `b` divides both `A` and `B`.
* It divides `A + B = 4*u^2` and `3*B - A = 4*v^2`.
* Since the prime is odd, it divides `u^2` and `v^2`, hence `u` and `v`, contradicting `hcop`.
* Prime `2` cannot divide either half because the halves are odd.
* Therefore `Int.gcd a b = 1`.

Then `(2*a)*(2*b) = Z^2`, so `Z` is even.  Write `Z = 2*z`; after cancellation, `a*b = z^2`.  The generic coprime-product-square helper gives `a = r^2` and `b = s^2`, hence `A = 2*r^2` and `B = 2*s^2`.

---

## B. Exact helper theorem interfaces

Add these as private/local lemmas near the quartic work.  The first four are short and can be proved immediately.  The last three are the focused arithmetic obligations.

```lean
-- short: odd witness + ring
private lemma quarticB_sum_factor_halves_odd
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    ∃ b : ℤ, u^2 + v^2 = 2*b ∧ Odd b

-- short: odd witness + ring
private lemma quarticB_twist_factor_halves_odd
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    ∃ a : ℤ, 3*u^2 - v^2 = 2*a ∧ Odd a

-- short: `mul_ne_zero`, `sq_pos_of_ne_zero`, `nlinarith`
private lemma quarticB_sum_sq_pos_of_mul_ne_zero
    {u v : ℤ} (huv0 : u * v ≠ 0) :
    0 < u^2 + v^2

-- short: square nonnegative and product with positive right factor
private lemma quarticB_left_factor_nonneg_of_square_product
    {A B Z : ℤ} (hBpos : 0 < B) (h : Z^2 = A * B) :
    0 ≤ A

-- elementary prime-3/natAbs lemma
private theorem quarticB_three_sq_sub_sq_ne_zero_of_coprime
    {u v : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu0 : u ≠ 0) :
    3*u^2 - v^2 ≠ 0

-- elementary common-prime argument for the two odd halves
private theorem quarticB_half_factors_coprime
    {u v a b : ℤ}
    (hcop : Int.gcd u v = 1)
    (haOdd : Odd a)
    (hbOdd : Odd b)
    (hA : 3*u^2 - v^2 = 2*a)
    (hB : u^2 + v^2 = 2*b) :
    Int.gcd a b = 1

-- generic helper; prove once by Nat.factorization or padic valuations
private theorem Int_coprime_mul_eq_sq_of_nonneg
    {a b z : ℤ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hcop : Int.gcd a b = 1)
    (h : a * b = z^2) :
    ∃ r s : ℤ, a = r^2 ∧ b = s^2

-- small parity helper
private theorem even_of_sq_eq_four_mul
    {Z t : ℤ}
    (h : Z^2 = 4*t) :
    Even Z
```

Useful `#check`s:

```lean
#check Int.gcd_def
#check Int.gcd_div
#check Int.gcd_greatest
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.coprime_of_dvd'
#check Nat.factorization_gcd
#check Nat.factorization_eq_of_coprime_left
#check Nat.factorization_eq_of_coprime_right
#check Nat.prod_primeFactors_pow_factorization
#check Nat.eq_iff_prime_padicValNat_eq
#check sq_nonneg
#check sq_pos_of_ne_zero
#check mul_ne_zero
```

If names like `Nat.prime_three` are unavailable, use:

```lean
have hp3 : Nat.Prime 3 := by norm_num
have hp2 : Nat.Prime 2 := by norm_num
```

---

## C. Lemmas that can be pasted/proved now

```lean
import Mathlib

private lemma quarticB_sum_factor_halves_odd
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    ∃ b : ℤ, u^2 + v^2 = 2*b ∧ Odd b := by
  rcases hu with ⟨m, hm⟩
  rcases hv with ⟨n, hn⟩
  subst u
  subst v
  refine ⟨2*m^2 + 2*m + 2*n^2 + 2*n + 1, ?_, ?_⟩
  · ring
  · refine ⟨m^2 + m + n^2 + n, ?_⟩
    ring

private lemma quarticB_twist_factor_halves_odd
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    ∃ a : ℤ, 3*u^2 - v^2 = 2*a ∧ Odd a := by
  rcases hu with ⟨m, hm⟩
  rcases hv with ⟨n, hn⟩
  subst u
  subst v
  refine ⟨6*m^2 + 6*m - 2*n^2 - 2*n + 1, ?_, ?_⟩
  · ring
  · refine ⟨3*m^2 + 3*m - n^2 - n, ?_⟩
    ring

private lemma quarticB_sum_sq_pos_of_mul_ne_zero
    {u v : ℤ} (huv0 : u * v ≠ 0) :
    0 < u^2 + v^2 := by
  have hu0 : u ≠ 0 := (mul_ne_zero.mp huv0).1
  have hv0 : v ≠ 0 := (mul_ne_zero.mp huv0).2
  have hu2 : 0 < u^2 := sq_pos_of_ne_zero u hu0
  have hv2 : 0 < v^2 := sq_pos_of_ne_zero v hv0
  nlinarith

private lemma quarticB_left_factor_nonneg_of_square_product
    {A B Z : ℤ} (hBpos : 0 < B) (h : Z^2 = A * B) :
    0 ≤ A := by
  have hprod : 0 ≤ A * B := by
    rw [← h]
    exact sq_nonneg Z
  by_contra hneg
  have hAlt : A < 0 := lt_of_not_ge hneg
  have hprodNeg : A * B < 0 := mul_neg_of_neg_of_pos hAlt hBpos
  nlinarith

private lemma half_sum_diff_sum_sq (u v : ℤ) :
    (u + v)^2 + (u - v)^2 = 2 * (u^2 + v^2) := by
  ring

private lemma half_sum_diff_twist_sq (u v : ℤ) :
    (u + v)^2 + 4*(u + v)*(u - v) + (u - v)^2 =
      2 * (3*u^2 - v^2) := by
  ring
```

The two `half_sum_diff_*` identities are useful when connecting this split back to the earlier Pythagorean parametrization bridge.

---

## D. How to prove the remaining arithmetic helpers

### D1. `quarticB_three_sq_sub_sq_ne_zero_of_coprime`

Proof plan:

1. Assume `3*u^2 - v^2 = 0`; derive `v^2 = 3*u^2` by `nlinarith`.
2. Apply `congrArg Int.natAbs` and simplify with natAbs multiplication/powers to get
   ```lean
   v.natAbs ^ 2 = 3 * u.natAbs ^ 2
   ```
3. Use `Nat.Prime.dvd_of_dvd_pow` with prime `3` to prove `3 ∣ v.natAbs`.
4. Substitute `v.natAbs = 3*k` back into the natural equality to prove `3 ∣ u.natAbs ^ 2`, hence `3 ∣ u.natAbs`.
5. Use `Nat.dvd_gcd` and `Int.gcd_def`:
   ```lean
   have hg : Nat.gcd u.natAbs v.natAbs = 1 := by
     simpa [Int.gcd_def] using hcop
   ```
6. Contradict `3 ∣ 1` by `norm_num`.

This avoids `ZMod` and is usually more stable in Lean.

### D2. `quarticB_half_factors_coprime`

Recommended proof:

1. Work over `a.natAbs.Coprime b.natAbs`; rewrite through `Int.gcd_def` at the end.
2. Use `Nat.coprime_of_dvd'` and introduce a prime `p` dividing both `a.natAbs` and `b.natAbs`.
3. Convert those divisibilities to `(p : ℤ) ∣ a` and `(p : ℤ) ∣ b`.
4. Since `a` and `b` are odd, prove `p ≠ 2`.
5. From `hA` and `hB`, get `(p : ℤ) ∣ A` and `(p : ℤ) ∣ B`.
6. Use the identities
   ```lean
   (3*u^2 - v^2) + (u^2 + v^2) = 4*u^2
   3*(u^2 + v^2) - (3*u^2 - v^2) = 4*v^2
   ```
   both closed by `ring`, to show `p ∣ 4*u^2` and `p ∣ 4*v^2`.
7. Because `p` is an odd prime, cancel the factor `4`, getting `p ∣ u^2` and `p ∣ v^2`.
8. Use `Nat.Prime.dvd_of_dvd_pow` to get `p ∣ u.natAbs` and `p ∣ v.natAbs`.
9. Contradict `hcop` via `Int.gcd_def`.

If you prefer proving exact gcd of the original factors, use this interface:

```lean
private theorem quarticB_factor_gcd_eq_two
    {u v : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u)
    (hv : Odd v) :
    Int.gcd (3*u^2 - v^2) (u^2 + v^2) = 2
```

Then derive half-coprime by `Int.gcd_div`.  In practice, the half-coprime theorem is usually easier because the odd halves remove the annoying factor `2` before the common-prime argument.

### D3. Generic square-product helper

Use this exact interface:

```lean
private theorem Nat_coprime_mul_eq_sq
    {a b z : ℕ}
    (hcop : a.Coprime b)
    (h : a * b = z^2) :
    ∃ r s : ℕ, a = r^2 ∧ b = s^2
```

Then wrap it over integers:

```lean
private theorem Int_coprime_mul_eq_sq_of_nonneg
    {a b z : ℤ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hcop : Int.gcd a b = 1)
    (h : a * b = z^2) :
    ∃ r s : ℤ, a = r^2 ∧ b = s^2
```

Proof of the natural theorem: use `Nat.factorization` or `Nat.padicValNat`.  For every prime `p`, coprimality says the exponent of `p` appears in at most one of `a` and `b`.  Since `a*b = z^2`, the exponent in `a*b` is even; therefore the exponent in `a` and the exponent in `b` are even.  Rebuild `a` and `b` from their prime factorizations with halved exponents.  The main API names to use are `Nat.factorization_eq_of_coprime_left`, `Nat.factorization_eq_of_coprime_right`, `Nat.prod_primeFactors_pow_factorization`, and `Nat.eq_iff_prime_padicValNat_eq`.

This is the only generic helper that may take real Lean effort, but it is standard arithmetic, not a curve-specific residual.

### D4. `even_of_sq_eq_four_mul`

Either prove by prime-`2` divisibility of a square or by parity cases:

```lean
private theorem even_of_sq_eq_four_mul
    {Z t : ℤ}
    (h : Z^2 = 4*t) :
    Even Z
```

Parity proof shape:

```lean
  rcases Int.even_or_odd Z with hEven | hOdd
  · exact hEven
  · exfalso
    have hOddSq : Odd (Z^2) := hOdd.pow _
    have hEvenSq : Even (Z^2) := by
      rw [h]
      exact ⟨2*t, by ring⟩
    exact hOddSq.not_even hEvenSq
```

If theorem names differ, grep `Int.even_or_odd`, `Odd.pow`, and `Odd.not_even`.

---

## E. Main theorem skeleton after helpers exist

```lean
private theorem quartic_B_split_two_squares_explicit
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hu : Odd u)
    (hv : Odd v)
    (hB : Z ^ 2 = (3*u^2 - v^2)*(u^2 + v^2)) :
    ∃ r s : ℤ,
      3*u^2 - v^2 = 2*r^2 ∧
      u^2 + v^2 = 2*s^2 := by
  obtain ⟨a, hA2, haOdd⟩ := quarticB_twist_factor_halves_odd hu hv
  obtain ⟨b, hB2, hbOdd⟩ := quarticB_sum_factor_halves_odd hu hv

  have hBpos : 0 < u^2 + v^2 := quarticB_sum_sq_pos_of_mul_ne_zero huv0
  have hAnonneg : 0 ≤ 3*u^2 - v^2 := by
    exact quarticB_left_factor_nonneg_of_square_product hBpos hB

  have hu0 : u ≠ 0 := (mul_ne_zero.mp huv0).1
  have hAne : 3*u^2 - v^2 ≠ 0 :=
    quarticB_three_sq_sub_sq_ne_zero_of_coprime hcop hu0
  have hApos : 0 < 3*u^2 - v^2 := by
    exact lt_of_le_of_ne hAnonneg (Ne.symm hAne)

  have haPos : 0 < a := by
    nlinarith [hA2, hApos]
  have hbPos : 0 < b := by
    nlinarith [hB2, hBpos]

  have habcop : Int.gcd a b = 1 :=
    quarticB_half_factors_coprime hcop haOdd hbOdd hA2 hB2

  have hZsq4 : Z^2 = 4 * (a*b) := by
    calc
      Z^2 = (2*a) * (2*b) := by
        simpa [hA2, hB2] using hB
      _ = 4 * (a*b) := by ring

  have hZeven : Even Z := even_of_sq_eq_four_mul hZsq4
  rcases hZeven with ⟨z, hz⟩
  subst Z

  have hab_sq : a*b = z^2 := by
    ring_nf at hZsq4
    nlinarith

  obtain ⟨r, s, hr, hs⟩ :=
    Int_coprime_mul_eq_sq_of_nonneg
      (le_of_lt haPos) (le_of_lt hbPos) habcop hab_sq

  refine ⟨r, s, ?_, ?_⟩
  · rw [hA2, hr]
    ring
  · rw [hB2, hs]
    ring
```

Potential local edits:

* If `simpa [hA2, hB2] using hB` does not rewrite both factors, do:
  ```lean
  have hB' := hB
  rw [hA2, hB2] at hB'
  simpa [mul_assoc, mul_left_comm, mul_comm] using hB'
  ```
* If `ring_nf at hZsq4; nlinarith` does not cancel `4`, use `have h4pos : (0:ℤ) < 4 := by norm_num` and `nlinarith [hZsq4, h4pos]`.

---

## F. Optional explicit mod-8 interfaces

These are optional; the half-witness lemmas above are easier to consume.

```lean
private theorem odd_sq_modEq_one_mod_eight
    {x : ℤ} (hx : Odd x) :
    x^2 ≡ 1 [ZMOD 8]

private theorem quarticB_sum_factor_modEq_two_mod_eight
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    u^2 + v^2 ≡ 2 [ZMOD 8]

private theorem quarticB_twist_factor_modEq_two_mod_eight
    {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    3*u^2 - v^2 ≡ 2 [ZMOD 8]
```

Proof idea: destruct `Odd x` as `x = 2*k + 1`; reduce `x^2 - 1` to `4*k*(k+1)`; use that `k*(k+1)` is even.  For this file, the witness lemmas `A = 2*a ∧ Odd a` and `B = 2*b ∧ Odd b` should be preferred.
