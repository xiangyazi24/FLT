# Q2614: residuals for `PrimitiveCenteredToEulerSquarePair`

This answers only the two residuals in the prompt.

The right split is:

* Residual A should be proved by a Nat theorem for coprime positive factors of `8*N^2`, then wrapped to `Int` using positivity.
* Residual B should be split into:
  1. an Euler cofactor coprimality lemma, and
  2. positive coprime-product square extraction.

I would **not** try to prove either residual inline in the AP-to-Euler assembly theorem.

---

## 1. Residual A: Nat theorem to isolate

The clean theorem is this Nat version.  It includes the exact parity conclusions needed by the `Int` residual.

```lean
import Mathlib.Tactic

/--
Coprime positive factors of `8*N^2`, with exactly one even factor.
The even factor is `8` times a square and the odd factor is a square.
The hypothesis `Even N` is used only to prove `Even A` after `N = A*D` and `Odd D`.
-/
theorem Nat.coprime_product_eq_eight_square_split
    {N m n : ℕ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (hparity : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
      N = A * D ∧
      ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
       (m = D ^ 2 ∧ n = 8 * A ^ 2))
```

### Proof route for the Nat theorem

Do the two parity cases separately.

### Case 1: `Even m`, `Odd n`

1. Prove `8 ∣ m`.

   Reason: `m*n = 8*N^2` and `n` is odd, so `n` is coprime to `8`; therefore `8 ∣ m*n` implies `8 ∣ m`.

   Useful local helper:

   ```lean
   theorem Nat.coprime_eight_of_odd {n : ℕ} (hn : Odd n) :
       Nat.Coprime 8 n
   ```

   Then use:

   ```lean
   (Nat.Coprime.dvd_of_dvd_mul_right ?hcop ?hdvd)
   ```

   Orientation pitfall: if `hcop : Nat.Coprime 8 n`, then to strip `n` from `8 ∣ m*n`, use the version returning `8 ∣ m`.  In many current snapshots this is:

   ```lean
   exact hcop.dvd_of_dvd_mul_right h8_dvd_mn
   ```

   If orientation fails, try:

   ```lean
   exact hcop.symm.dvd_of_dvd_mul_left h8_dvd_mn
   ```

2. Write `m = 8*m8`; cancel the `8` in

   ```text
   (8*m8)*n = 8*N^2
   ```

   to obtain

   ```lean
   m8 * n = N ^ 2
   ```

   Use `mul_left_cancel₀ (by norm_num : (8:ℕ) ≠ 0)` after normalizing associativity.

3. Prove `Nat.Coprime m8 n` from `Nat.Coprime m n` and `m = 8*m8`.

   Useful helper:

   ```lean
   theorem Nat.Coprime.of_dvd_left {a b c : ℕ}
       (hcop : Nat.Coprime a c) (hba : b ∣ a) : Nat.Coprime b c
   ```

   If this exact theorem is not present, the one-line prime-divisor proof is easier than API hunting.

4. Apply the standard square-product extraction theorem:

   ```lean
   /-- Local residual if Mathlib does not already have this exact statement. -/
   theorem Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
       {x y z : ℕ}
       (hcop : Nat.Coprime x y)
       (h : x * y = z ^ 2) :
       ∃ r s : ℕ, x = r ^ 2 ∧ y = s ^ 2
   ```

   This gives

   ```text
   m8 = A^2,
   n = D^2.
   ```

5. From

   ```text
   A^2 * D^2 = N^2
   ```

   and positivity, prove

   ```text
   N = A*D.
   ```

   Nat lemma to use/isolate:

   ```lean
   theorem Nat.eq_of_sq_eq_sq_of_pos {a b : ℕ}
       (ha : 0 < a) (hb : 0 < b) (h : a ^ 2 = b ^ 2) : a = b
   ```

   If not present, prove by `nlinarith [sq_lt_sq.mpr ...]` or use `Nat.sqrt` only locally.

6. Prove `Odd D` from `Odd n` and `n = D^2`.

   ```lean
   theorem Nat.odd_of_sq_odd {D : ℕ} (h : Odd (D ^ 2)) : Odd D
   ```

   This follows from `Odd.of_mul_left` after `pow_two`.

7. Prove `Even A` from `Even N`, `N = A*D`, and `Odd D`.

   If `D` is odd, it is coprime to `2`; from `2 ∣ A*D` strip `D` to get `2 ∣ A`.

8. Prove `Nat.Coprime A D` from `Nat.Coprime (A^2) (D^2)` or directly from `Nat.Coprime m8 n`.

   Useful helper:

   ```lean
   theorem Nat.coprime_of_coprime_sq_sq {A D : ℕ}
       (h : Nat.Coprime (A ^ 2) (D ^ 2)) : Nat.Coprime A D
   ```

### Case 2: `Odd m`, `Even n`

Same proof with `m,n` swapped.  The conclusion is the second disjunct:

```text
m = D^2,
n = 8*A^2.
```

---

## 2. Int wrapper for Residual A

The `Int` theorem in the prompt should be a wrapper around the Nat theorem above.  Use positivity to avoid sign ambiguity.

```lean
theorem coprime_product_eq_eight_square_split_int
    {N m n : Int}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Int.gcd m n = 1)
    (hparity : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) :
    ∃ A D : Int,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ IsCoprime A D ∧
      N = A * D ∧
      ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
       (m = D ^ 2 ∧ n = 8 * A ^ 2))
```

### Wrapper proof hints

Let

```lean
let NN : ℕ := N.natAbs
let mm : ℕ := m.natAbs
let nn : ℕ := n.natAbs
```

Because of positivity, you can rewrite back with:

```lean
Int.natAbs_of_nonneg (le_of_lt hNpos)
Int.natAbs_of_nonneg (le_of_lt hmpos)
Int.natAbs_of_nonneg (le_of_lt hnpos)
```

Convert the product equation using:

```lean
Int.natAbs_mul
Int.natAbs_pow
```

Convert the gcd hypothesis using the fact that `Int.gcd m n` is `Nat.gcd m.natAbs n.natAbs`.  In many Mathlib snapshots this is by simplification:

```lean
have hcopNat : Nat.Coprime mm nn := by
  simpa [Int.gcd, mm, nn, Nat.Coprime] using hmn_coprime
```

If `simp [Int.gcd]` does not unfold, use the project’s existing `Int.gcd_def`/`Int.gcd_eq_natAbs` lemma; this is exactly the kind of wrapper proof already appearing in the file.

Convert `m % 2 = 1` to `Odd mm` using `Int.odd_iff` and positivity.  Convert `m % 2 = 0` to `Even mm` using `Int.not_odd_iff_even` or a tiny local parity wrapper.

After applying `Nat.coprime_product_eq_eight_square_split`, lift `A,D : ℕ` back to `Int` by coercion.  Positivity of Nat witnesses gives positive Int witnesses.

---

## 3. Residual B: Euler cofactor coprimality

Define the two cofactors locally:

```lean
def eulerLeft (A D : ℤ) : ℤ := 16 * A ^ 2 + D ^ 2
def eulerRight (A D : ℤ) : ℤ := 4 * A ^ 2 + D ^ 2
```

The cofactor gcd lemma should be local and reusable.

```lean
/-- The two Euler cofactors are coprime. -/
theorem euler_cofactor_coprime
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2)
```

### Proof route for `euler_cofactor_coprime`

Use the factor-coprime transport style already present in the file.

Let

```text
F = 16*A^2 + D^2,
G = 4*A^2 + D^2.
```

Then

```text
F - G = 12*A^2,
G = F - 12*A^2.
```

So it suffices to prove

```text
IsCoprime F (12*A^2).
```

Break it into:

```lean
lemma euler_left_coprime_A
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) A

lemma euler_left_coprime_A_sq
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2)

lemma euler_left_odd
    {A D : ℤ} (hDodd : Odd D) :
    Odd (16 * A ^ 2 + D ^ 2)

lemma euler_left_coprime_four
    {A D : ℤ} (hDodd : Odd D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 : ℤ)

lemma euler_left_coprime_three
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ)
```

The only slightly annoying sublemma is `euler_left_coprime_three`.  Prove it by contradiction: if `3 ∣ F`, then in `ZMod 3`,

```text
0 = 16*A^2 + D^2 = A^2 + D^2.
```

Squares in `ZMod 3` are `0` or `1`; therefore both `A` and `D` are `0 mod 3`, contradicting `IsCoprime A D`.  If you want to avoid `ZMod`, use `% 3` case splitting on `A % 3` and `D % 3`; there are only nine cases and `omega`/`norm_num` closes them.

With those helpers:

```lean
/-- Odd plus not divisible by `3` gives coprime to `12`; then multiply by `A^2`. -/
theorem euler_left_coprime_twelve_mul_A_sq
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) := by
  have hA2 : IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2) :=
    euler_left_coprime_A_sq hAD
  have h4 : IsCoprime (16 * A ^ 2 + D ^ 2) (4 : ℤ) :=
    euler_left_coprime_four hDodd
  have h3 : IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ) :=
    euler_left_coprime_three hAD
  have h12 : IsCoprime (16 * A ^ 2 + D ^ 2) ((4 : ℤ) * 3) :=
    h4.mul_right h3
  have h12' : IsCoprime (16 * A ^ 2 + D ^ 2) (12 : ℤ) := by
    simpa using h12
  have h : IsCoprime (16 * A ^ 2 + D ^ 2) ((12 : ℤ) * (A ^ 2)) :=
    h12'.mul_right hA2
  simpa using h
```

Then the final cofactor lemma is:

```lean
theorem euler_cofactor_coprime
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
  have hF12A : IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) :=
    euler_left_coprime_twelve_mul_A_sq hDodd hAD
  -- `G = F + (-1) * (12*A^2)`.
  -- If the local file has `isCoprime_self_add_right_int`, use it:
  have h := isCoprime_self_add_right_int (x := 16 * A ^ 2 + D ^ 2)
    (z := -(12 * A ^ 2)) ?hneg
  · convert h using 1 <;> ring
  · -- `hneg : IsCoprime F (-(12*A^2))`
    simpa using hF12A.neg_right
```

If `neg_right` is not available for `IsCoprime`, avoid negatives by proving the transport lemma directly:

```lean
lemma isCoprime_self_sub_right_int {x z : ℤ}
    (h : IsCoprime x z) : IsCoprime x (x - z) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u + v, -v, ?_⟩
  calc
    (u + v) * x + (-v) * (x - z) = u * x + v * z := by ring
    _ = 1 := huv
```

Then:

```lean
theorem euler_cofactor_coprime
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
  have hF12A : IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) :=
    euler_left_coprime_twelve_mul_A_sq hDodd hAD
  have h := isCoprime_self_sub_right_int hF12A
  convert h using 1 <;> ring
```

This is the version I recommend.

---

## 4. Residual B: square extraction into `B,C`

Use the same positive coprime-product square extraction interface as in Q2603.

```lean
/-- Positive integer square extraction from a coprime product equal to a square. -/
theorem Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    {x y z : ℤ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy : IsCoprime x y)
    (h : z ^ 2 = x * y) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧
      r ^ 2 = x ∧ s ^ 2 = y
```

This can be proved by converting to Nat and using:

```lean
theorem Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
    {x y z : ℕ}
    (hcop : Nat.Coprime x y)
    (h : x * y = z ^ 2) :
    ∃ r s : ℕ, x = r ^ 2 ∧ y = s ^ 2
```

Now the target residual becomes straightforward.

```lean
theorem euler_cofactors_are_squares_of_center_square
    {A D X : Int}
    (hApos : 0 < A) (hDpos : 0 < D)
    (hDodd : Odd D)
    (hAD : IsCoprime A D)
    (hXsq : X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    ∃ B C : Int,
      0 < B ∧ 0 < C ∧
      B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
      C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  have hLpos : 0 < 16 * A ^ 2 + D ^ 2 := by
    nlinarith [sq_nonneg A, sq_pos_of_ne_zero (ne_of_gt hDpos)]
  have hRpos : 0 < 4 * A ^ 2 + D ^ 2 := by
    nlinarith [sq_nonneg A, sq_pos_of_ne_zero (ne_of_gt hDpos)]
  have hcop : IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) :=
    euler_cofactor_coprime hDodd hAD
  exact Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    hLpos hRpos hcop hXsq
```

This is the exact dependency shape I recommend.

---

## 5. Summary of what to prove locally versus residual

### Local in `N12FourSquaresAP.lean`

```lean
isCoprime_self_sub_right_int
euler_left_coprime_A
euler_left_coprime_A_sq
euler_left_odd
euler_left_coprime_four
euler_left_coprime_three
euler_left_coprime_twelve_mul_A_sq
euler_cofactor_coprime
euler_cofactors_are_squares_of_center_square
```

### Genuine reusable residuals

```lean
Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
Nat.coprime_product_eq_eight_square_split
coprime_product_eq_eight_square_split_int
```

If you already have the Nat square-product extraction theorem in another file, then Residual B is no longer hard; only the mod-3 cofactor coprimality lemma remains mildly tedious.
