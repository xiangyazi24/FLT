# Q1585 (dm1): the correct even-`B` descent chain

The even-`B` descent is **not** identical to the odd-`B` descent. Your re-derivation is right: after normalizing by `4`, the key identity loses the leading `4` on the left.

In the main orientation

```lean
M = a ^ 4,
N = 5 * b ^ 4,
B₁ = a * b,
M + N = r ^ 2 + 2 * B₁ ^ 2,
```

the identity is

```lean
r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4
```

not

```lean
4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4.
```

So the odd proof’s choice

```lean
h = (a ^ 2 - b ^ 2) / 2
```

is wrong in the even branch. The correct choice is

```lean
h = a ^ 2 - b ^ 2
```

Then

```lean
(r - h) * (r + h) = 4 * b ^ 4.
```

Because `r` is odd and, in the even case, exactly one of `a,b` is even, `h = a²-b²` is also odd. Therefore `r-h` and `r+h` are both even, and the real factorization is

```lean
((r - h) / 2) * ((r + h) / 2) = b ^ 4.
```

That is the point where the proof re-enters the old fourth-power descent pattern.

## Correct architecture

Extract the old odd descent below the point where it has

```lean
A * D = b ^ 4,
Int.gcd A D = 1,
0 < A,
0 < D.
```

Then the odd branch feeds it with

```lean
A = r - ((a ^ 2 - b ^ 2) / 2)
D = r + ((a ^ 2 - b ^ 2) / 2)
```

whereas the even branch feeds it with

```lean
A = (r - (a ^ 2 - b ^ 2)) / 2
D = (r + (a ^ 2 - b ^ 2)) / 2
```

This is the clean split:

```lean
factor pair M,N
  → fourth-power split B₁ = a*b
  → normalized identity r² = (a²-b²)² + 4b⁴
  → half-factor product ((r-h)/2)*((r+h)/2)=b⁴
  → old fourth-power extraction
  → new QuarticPlusZ β α a
```

## Shared post-factor helper

This is the helper you want. It is the even analogue of the odd branch after the factor split.

```lean
import Mathlib

/-- Even-`B` descent core after `M,N` have been split.

Input orientation:

* `C = x*y`
* `r² = (x²-y²)² + 4*y⁴`

Output:

* new solution `(β, α, x)`
* with `α < C`

The symmetric factor case is obtained by calling this with `(x,y) = (b,a)`.
-/
lemma even_descent_from_split
    {r B C x y : ℤ}
    (hr : 0 < r)
    (hB : 0 < B)
    (hCpos : 0 < C)
    (hB_eq : B = 2 * C)
    (hCeq : C = x * y)
    (hx : 0 < x)
    (hy : 0 < y)
    (hxy_cop : Int.gcd x y = 1)
    (hcop : Int.gcd r B = 1)
    (hr_odd : r % 2 = 1)
    (hnonbase : ¬ BaseZ r B)
    (hid : r ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + 4 * y ^ 4) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < C.natAbs := by
  let h : ℤ := x ^ 2 - y ^ 2
  let A : ℤ := (r - h) / 2
  let D : ℤ := (r + h) / 2

  have hr_sq : r ^ 2 = h ^ 2 + 4 * y ^ 4 := by
    simpa [h] using hid

  -- `y | C | B`, hence gcd(r,y)=1.
  have hy_dvd_B : y ∣ B := by
    refine ⟨2 * x, ?_⟩
    rw [hB_eq, hCeq]
    ring

  have hry_cop : Int.gcd r y = 1 := by
    -- Use the exact local divisor-of-coprime helper from the odd branch if it
    -- has a different name.
    exact gcd_of_gcd_mul_right_eq_one hcop hy_dvd_B

  -- Since C is even in the even-B branch and gcd(x,y)=1, exactly one of x,y is
  -- even.  Therefore x²-y² is odd.  Package this as a helper; it is the only
  -- parity fact absent from the odd-B branch.
  have hh_odd : h % 2 = 1 := by
    exact odd_sqdiff_of_coprime_product_even hCpos hCeq hxy_cop hB_eq hcop

  have h2_dvd_l : 2 ∣ r - h := by
    exact two_dvd_sub_of_odd_odd hr_odd hh_odd

  have h2_dvd_r : 2 ∣ r + h := by
    exact two_dvd_add_of_odd_odd hr_odd hh_odd

  have hA_mul_D : A * D = y ^ 4 := by
    have hprod : (r - h) * (r + h) = 4 * y ^ 4 := by
      nlinarith [hr_sq]
    have hl : 2 * A = r - h := by
      dsimp [A]
      exact (Int.ediv_mul_cancel h2_dvd_l).symm
    have hr' : 2 * D = r + h := by
      dsimp [D]
      exact (Int.ediv_mul_cancel h2_dvd_r).symm
    nlinarith [hprod, hl, hr']

  have hApos : 0 < A := by
    -- From r² = h² + 4*y⁴ and y>0, get |h| < r, hence r-h>0.
    exact half_factor_left_pos hr hy hr_sq

  have hDpos : 0 < D := by
    -- Same: |h| < r, hence r+h>0.
    exact half_factor_right_pos hr hy hr_sq

  have hAD_cop : Int.gcd A D = 1 := by
    -- Even analogue of `coprime_rh`.
    -- A common divisor of A and D divides A+D=r and D-A=h.  Since it also
    -- divides A*D=y⁴, every prime common divisor divides y; contradiction with
    -- gcd(r,y)=1.  The prime 2 is also excluded because r is odd.
    exact coprime_half_rh hr_odd hh_odd hry_cop hy hA_mul_D

  -- Split the coprime product `A*D = y^4`.
  -- Depending on your exact helper signature, this may be one or two calls to
  -- `pos_fourth_of_coprime_mul_fourth`.  The intended result is:
  obtain ⟨α, β, hαpos, hβpos, hA_eq, hD_eq, hy_eq⟩ :=
    coprime_product_eq_fourth_split hApos hDpos hAD_cop hA_mul_D hy

  -- hA_eq : A = α ^ 4
  -- hD_eq : D = β ^ 4
  -- hy_eq : y = α * β

  have hh_eq : h = β ^ 4 - α ^ 4 := by
    have hdiff : D - A = h := by
      dsimp [A, D]
      have hl : 2 * ((r - h) / 2) = r - h := (Int.ediv_mul_cancel h2_dvd_l).symm
      have hr' : 2 * ((r + h) / 2) = r + h := (Int.ediv_mul_cancel h2_dvd_r).symm
      nlinarith [hl, hr']
    nlinarith [hA_eq, hD_eq, hdiff]

  have hnew_eq : x ^ 2 = β ^ 4 + β ^ 2 * α ^ 2 - α ^ 4 := by
    have hy_sq : y ^ 2 = (α * β) ^ 2 := by
      rw [hy_eq]
    -- h = x²-y² and h = β⁴-α⁴.
    dsimp [h] at hh_eq
    nlinarith [hh_eq, hy_sq]

  refine ⟨β, α, x, ?hquartic, ?hnonbase_new, ?hsmall⟩

  · -- QuarticPlusZ β α x
    -- For the usual definition this is exactly `hnew_eq`.
    simpa [QuarticPlusZ, mul_comm, mul_left_comm, mul_assoc] using hnew_eq

  · -- New non-base.
    -- Same contradiction as in the odd branch, but now C = x*y and y=αβ.
    -- If β=1 and α=1, then y=1 and hnew_eq gives x=1, so C=1; but in the
    -- even branch C = B/2 and B is divisible by 4, hence C is even positive.
    exact even_nonbase_from_split
      hnonbase hB_eq hCeq hy_eq hnew_eq hx hy hαpos hβpos

  · -- α.natAbs < C.natAbs
    have hα_le_y : α ≤ y := by
      rw [hy_eq]
      nlinarith [hαpos, hβpos]

    have hy_le_C : y ≤ C := by
      rw [hCeq]
      nlinarith [hx, hy]

    have hα_le_C : α ≤ C := le_trans hα_le_y hy_le_C

    have hα_ne_C : α ≠ C := by
      intro hαC
      exact even_strictness_from_split
        hnonbase hB_eq hCeq hy_eq hnew_eq hαC hx hy hαpos hβpos

    have hα_lt_C : α < C := lt_of_le_of_ne hα_le_C hα_ne_C
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hαpos) hα_lt_C
```

The helper names in this block are the exact missing even-specific atoms:

```lean
odd_sqdiff_of_coprime_product_even
two_dvd_sub_of_odd_odd
two_dvd_add_of_odd_odd
half_factor_left_pos
half_factor_right_pos
coprime_half_rh
coprime_product_eq_fourth_split
even_nonbase_from_split
even_strictness_from_split
```

Most of these are tiny wrappers around arguments already present in the odd proof. The genuinely new one is `coprime_half_rh`, because the factors are `A=(r-h)/2` and `D=(r+h)/2`, not `r-h` and `r+h`.

## Main factor orientation

After

```lean
obtain ⟨a, b, ha, hb, hab_cop, hB₁_eq, hfactor⟩ :=
  coprime_factor_5_fourth hMN_prod hMN_cop
```

in the branch

```lean
hM_eq : M = a ^ 4
hN_eq : N = 5 * b ^ 4
```

use:

```lean
have hid : r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
  calc
    r ^ 2 = a ^ 4 + 5 * b ^ 4 - 2 * B₁ ^ 2 := by
      nlinarith [hMN_sum, hM_eq, hN_eq]
    _ = a ^ 4 + 5 * b ^ 4 - 2 * (a * b) ^ 2 := by
      rw [hB₁_eq]
    _ = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
      ring

obtain ⟨r', B', s', hq, hnb, hsmall_B₁⟩ :=
  even_descent_from_split
    (r := r) (B := B) (C := B₁) (x := a) (y := b)
    hr hB hB₁_pos hB_eq_two hB₁_eq
    ha hb hab_cop hcop hr_odd hnonbase hid

exact ⟨r', B', s', hq, hnb, lt_trans hsmall_B₁ hB₁_natAbs_lt_B⟩
```

Here `hB₁_natAbs_lt_B` is the easy inequality from `B = 2*B₁` and `0 < B₁`:

```lean
have hB₁_natAbs_lt_B : B₁.natAbs < B.natAbs := by
  have hlt : B₁ < B := by
    nlinarith [hB₁_pos, hB_eq_two]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hB₁_pos) hlt
```

## Symmetric factor orientation

In the branch

```lean
hM_eq : M = 5 * a ^ 4
hN_eq : N = b ^ 4
```

the identity is

```lean
r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4
```

so call the same helper with `(x,y)=(b,a)`:

```lean
have hid : r ^ 2 = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
  calc
    r ^ 2 = 5 * a ^ 4 + b ^ 4 - 2 * B₁ ^ 2 := by
      nlinarith [hMN_sum, hM_eq, hN_eq]
    _ = 5 * a ^ 4 + b ^ 4 - 2 * (a * b) ^ 2 := by
      rw [hB₁_eq]
    _ = (b ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 4 := by
      ring

have hB₁_ba : B₁ = b * a := by
  simpa [mul_comm] using hB₁_eq

have hba_cop : Int.gcd b a = 1 := by
  simpa [Int.gcd_comm] using hab_cop

obtain ⟨r', B', s', hq, hnb, hsmall_B₁⟩ :=
  even_descent_from_split
    (r := r) (B := B) (C := B₁) (x := b) (y := a)
    hr hB hB₁_pos hB_eq_two hB₁_ba
    hb ha hba_cop hcop hr_odd hnonbase hid

exact ⟨r', B', s', hq, hnb, lt_trans hsmall_B₁ hB₁_natAbs_lt_B⟩
```

## What to reuse from the odd proof

The reusable part is **not** the block that constructs

```lean
h = (a ^ 2 - b ^ 2) / 2
```

and proves

```lean
(r - h) * (r + h) = b ^ 4.
```

That block is odd-only.

The reusable part starts later, after you have a coprime product of the form

```lean
A * D = y ^ 4,
Int.gcd A D = 1,
0 < A,
0 < D.
```

For even `B`, use

```lean
h = x ^ 2 - y ^ 2
A = (r - h) / 2
D = (r + h) / 2
```

and then the rest of the fourth-power extraction is genuinely the same.

## Bottom line

Your corrected derivation is the right one:

```lean
r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4.
```

The decisive trick is not to factor `4*b^4` directly as coprime factors. Since `r` and `a²-b²` are both odd, first divide both factors by `2`:

```lean
((r - (a ^ 2 - b ^ 2)) / 2) *
((r + (a ^ 2 - b ^ 2)) / 2) = b ^ 4.
```

Then apply the same coprime fourth-power extraction as in the odd branch.
