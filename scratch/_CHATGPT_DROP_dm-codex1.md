# Q2678 (dm-codex1): divided-by-3 square-side branch

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`

## Verdict

The strong statement

```lean
DividedSquareBranch A N S m n  →  A = 1 ∧ N = 1 ∧ S = 1
```

is true for the positive primitive square-side quartic context, but not by a purely local gcd squeeze. The local algebra reduces the divided branch to four integer squares in arithmetic progression. The hard residual is exactly Fermat's four-squares-AP theorem, which this project already has as `fourRatSquaresAPConst_checked : FourRatSquaresAPConst` in `N12FourSquaresAP.lean`.

So the right implementation target is:

```lean
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12FourSquaresAP

namespace MazurProof.RationalPointsN12

/-- Integer wrapper around the checked rational no-four-squares-AP theorem. -/
def FourIntSquaresAPConst : Prop :=
  ∀ {a d b c : ℤ},
    a ^ 2 + b ^ 2 = 2 * d ^ 2 →
    c ^ 2 + d ^ 2 = 2 * b ^ 2 →
    a ^ 2 = d ^ 2 ∧ d ^ 2 = b ^ 2 ∧ b ^ 2 = c ^ 2

/-- This is the honest divided-sector residual if the AP theorem is not imported. -/
def DividedSquareBranchUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    0 < A → 0 < N →
    DividedSquareBranch A N S m n →
    A = 1 ∧ N = 1 ∧ S = 1

end MazurProof.RationalPointsN12
```

If `PositivePrimitiveEisensteinBadUnordered` already supplies `0 < A` and `0 < N`, the final wrapper should take that hypothesis instead of explicit positivity. If it only supplies `A ≠ 0`, `N ≠ 0`, prove the sign-free version first:

```lean
def DividedSquareBranchAbsUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
    A ^ 2 = 1 ∧ N ^ 2 = 1 ∧ S = 1
```

and derive `A = 1`, `N = 1` from positivity in the normalized bad wrapper.

## 1. Normalized assumptions

Use exactly these normalized assumptions for the divided branch proof:

```lean
-- Supplied by `DividedSquareBranch`:
--   0 < n
--   n < m
--   IsCoprime m n
--   (3 : ℤ) ∣ m + n
--   3 * A ^ 2 = (m - n) * (m + n)
--   3 * N ^ 2 = n * (2 * m - n)
--   3 * S = m ^ 2 - m * n + n ^ 2
--
-- Supplied by the positive normalized bad context:
--   0 < A
--   0 < N
-- Optional/unneeded here:
--   IsCoprime A N
--   A ^ 2 ≠ N ^ 2
--   quartic equation, since the branch equations already encode the conic parametrization.
```

No order between `A` and `N` is needed. The branch already has the needed parameter order `0 < n < m`.

The unit branch is represented by

```lean
m = 2,
n = 1,
A ^ 2 = 1,
N ^ 2 = 1,
S = 1,
```

and hence by `A = 1`, `N = 1`, `S = 1` under positivity.

## 2. Basic 3-divisibility facts

From `h3 : (3 : ℤ) ∣ m + n`:

```lean
lemma three_dvd_two_mul_sub_of_three_dvd_add {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ 2 * m - n := by
  -- 2*m - n = 2*(m+n) - 3*n
  rcases h3 with ⟨k, hk⟩
  refine ⟨2 * k - n, ?_⟩
  nlinarith
```

Useful non-divisibility facts, if needed for contradiction/debugging:

```lean
lemma not_three_dvd_m_of_coprime_of_three_dvd_add {m n : ℤ}
    (hmn : IsCoprime m n) (h3 : (3 : ℤ) ∣ m + n) :
    ¬ (3 : ℤ) ∣ m := by
  -- If 3∣m and 3∣m+n, then 3∣n, contradicting `IsCoprime m n`.
  -- Use `Int.Prime.dvd_of_dvd_mul_right`/Bezout form of `IsCoprime`.
  -- Grep: `isCoprime_iff_exists`, `Int.isCoprime_iff_gcd_eq_one`, `Int.Prime.not_unit`.
  omega

lemma not_three_dvd_n_of_coprime_of_three_dvd_add {m n : ℤ}
    (hmn : IsCoprime m n) (h3 : (3 : ℤ) ∣ m + n) :
    ¬ (3 : ℤ) ∣ n := by
  -- symmetric to the previous lemma
  omega

lemma not_three_dvd_m_sub_n_of_coprime_of_three_dvd_add {m n : ℤ}
    (hmn : IsCoprime m n) (h3 : (3 : ℤ) ∣ m + n) :
    ¬ (3 : ℤ) ∣ m - n := by
  -- If 3∣m-n and 3∣m+n, then 3∣2*m and 3∣2*n; since 3∤2, get 3∣m,n.
  omega
```

The `omega` bodies above are placeholders for the intended arithmetic proof shape; if `omega` does not close them over divisibility, use the Bezout form of `IsCoprime`.

## 3. Parity cases

### Case A: `m,n` both odd is impossible

Because `IsCoprime m n`, the only same-parity case is both odd. In that case:

* `m - n` and `m + n` are both even;
* `(m + n)` is divisible by `6` because it is even and divisible by `3`;
* from `3 * A^2 = (m-n)*(m+n)` one gets
  `m - n = 2 * a^2` and `m + n = 6 * b^2`;
* from `3 * N^2 = n*(2*m-n)`, since `n` is odd and `(3 : ℤ) ∣ 2*m-n`, one gets
  `n = c^2` and `2*m-n = 3*d^2`.

The contradiction is then immediate:

```lean
-- From the factorization:
--   m - n = 2 * a ^ 2
--   m + n = 6 * b ^ 2
--   n = c ^ 2
-- Hence:
--   2*n = (m+n) - (m-n) = 6*b^2 - 2*a^2
-- so:
--   c^2 = 3*b^2 - a^2
-- Since m and n are odd, m = a^2 + 3*b^2 is odd, so a,b have opposite parity.
-- Then 3*b^2 - a^2 ≡ 3 mod 4, impossible for a square.
```

Lean theorem boundary:

```lean
lemma dividedBranch_not_mn_both_odd
    {A N S m n : ℤ}
    (hB : DividedSquareBranch A N S m n)
    (hmOdd : ¬ (2 : ℤ) ∣ m) (hnOdd : ¬ (2 : ℤ) ∣ n) :
    False := by
  -- 1. extract `m - n = 2*a^2`, `m+n = 6*b^2` using a 2-and-3 square-factor lemma;
  -- 2. extract `n = c^2`, `(2*m-n)/3 = d^2` using the positive coprime square-factor lemma;
  -- 3. prove `a` and `b` have opposite parity from `m = a^2 + 3*b^2` odd;
  -- 4. reduce `c^2 = 3*b^2 - a^2` mod 4.
  -- Recommended local helper: `Int.square_mod_four` or a small parity lemma:
  --   sq_mod_four_eq_zero_or_one : x^2 % 4 = 0 ∨ x^2 % 4 = 1
  -- plus `omega`/`norm_num` on the two parity branches.
  contradiction
```

Do not skip this case by claiming `gcd(m-n,m+n)=1`; when `m,n` are both odd, that gcd is `2`.

### Case B: opposite parity; this is the only live case

In the opposite-parity case, local square extraction gives positive integers `a,b,c,d` with

```lean
m - n = a ^ 2
m + n = 3 * b ^ 2
n = c ^ 2
2 * m - n = 3 * d ^ 2
```

The parameter parity then automatically becomes

```lean
m ≡ 2 [ZMOD 4],  n ≡ 1 [ZMOD 4]
```

because `m ± n` are odd, so `a,b` are odd, and odd squares are `1 mod 8`:

```text
m = (a^2 + 3*b^2)/2 ≡ (1 + 3)/2 ≡ 2 mod 4,
n = (3*b^2 - a^2)/2 ≡ (3 - 1)/2 ≡ 1 mod 4.
```

Lean extraction helper:

```lean
lemma dividedBranch_oppositeParity_factorization
    {A N S m n : ℤ}
    (hB : DividedSquareBranch A N S m n)
    (hpar : ((2 : ℤ) ∣ m ∧ ¬ (2 : ℤ) ∣ n) ∨
            (¬ (2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ n)) :
    ∃ a b c d : ℤ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      m - n = a ^ 2 ∧
      m + n = 3 * b ^ 2 ∧
      n = c ^ 2 ∧
      2 * m - n = 3 * d ^ 2 := by
  -- Proof skeleton:
  --   hx₁ : 0 < m-n, hx₂ : 0 < (m+n)/3
  --   hcop₁ : IsCoprime (m-n) ((m+n)/3)
  --   hA' : A^2 = (m-n) * ((m+n)/3)
  --   apply `posSqOfCoprimeMulSq` to get `m-n=a^2`, `(m+n)/3=b^2`.
  --
  --   hy₁ : 0 < n, hy₂ : 0 < (2*m-n)/3
  --   hcop₂ : IsCoprime n ((2*m-n)/3)
  --   hN' : N^2 = n * ((2*m-n)/3)
  --   apply `posSqOfCoprimeMulSq` to get `n=c^2`, `(2*m-n)/3=d^2`.
  --
  --   The impossible subcase `m` odd, `n` even falls out after the first extraction:
  --   `a,b` are odd, hence `m` is even and `n` is odd.
  contradiction
```

The gcd helpers needed by that lemma are these:

```lean
lemma isCoprime_msubn_maddn_div_three
    {m n : ℤ}
    (hnm : n < m) (hposn : 0 < n)
    (hmn : IsCoprime m n) (h3 : (3 : ℤ) ∣ m + n)
    (hOpp : ((2 : ℤ) ∣ m ∧ ¬ (2 : ℤ) ∣ n) ∨
            (¬ (2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ n)) :
    IsCoprime (m - n) ((m + n) / 3) := by
  -- common divisor divides m-n and (m+n)/3, hence divides m+n;
  -- then it divides 2*m and 2*n;
  -- opposite parity removes a possible factor 2;
  -- `IsCoprime m n` removes every odd common prime.
  contradiction

lemma isCoprime_n_twom_sub_n_div_three
    {m n : ℤ}
    (hnm : n < m) (hposn : 0 < n)
    (hmn : IsCoprime m n) (h3 : (3 : ℤ) ∣ m + n)
    (hnOdd : ¬ (2 : ℤ) ∣ n) :
    IsCoprime n ((2 * m - n) / 3) := by
  -- common divisor divides n and (2*m-n)/3, hence divides 2*m-n;
  -- then it divides 2*m;
  -- `hnOdd` removes factor 2, and `IsCoprime m n` removes odd factors.
  contradiction
```

## 4. Algebra from the factorization to four squares in AP

Once the live factorization exists, the rest is one `nlinarith` block.

Given

```lean
hmn_a : m - n = a ^ 2
hmp_b : m + n = 3 * b ^ 2
hn_c  : n = c ^ 2
ht_d  : 2 * m - n = 3 * d ^ 2
```

derive:

```lean
lemma dividedBranch_factorization_four_sq_ap
    {m n a b c d : ℤ}
    (hmn_a : m - n = a ^ 2)
    (hmp_b : m + n = 3 * b ^ 2)
    (hn_c  : n = c ^ 2)
    (ht_d  : 2 * m - n = 3 * d ^ 2) :
    a ^ 2 + b ^ 2 = 2 * d ^ 2 ∧
    c ^ 2 + d ^ 2 = 2 * b ^ 2 := by
  constructor
  · -- From `2*(2*m-n) = 3*((m-n) + (m+n)/3)` after substituting.
    nlinarith
  · -- From `2*n = (m+n) - (m-n)` and the first AP equation.
    nlinarith
```

Interpretation:

```text
a^2, d^2, b^2, c^2
```

are four integer squares in arithmetic progression, because

```lean
a ^ 2 + b ^ 2 = 2 * d ^ 2   -- d^2 is the midpoint of a^2 and b^2
c ^ 2 + d ^ 2 = 2 * b ^ 2   -- b^2 is the midpoint of d^2 and c^2
```

Equivalently,

```lean
d ^ 2 - a ^ 2 = b ^ 2 - d ^ 2 ∧
b ^ 2 - d ^ 2 = c ^ 2 - b ^ 2
```

by `nlinarith`.

## 5. Unit conclusion from four-squares AP

Use the checked no-four-squares theorem through an integer wrapper.

```lean
lemma fourIntSquaresAPConst_checked : FourIntSquaresAPConst := by
  -- Cast `a d b c : ℤ` to `ℚ` and invoke
  -- `fourRatSquaresAPConst_checked : FourRatSquaresAPConst`.
  -- Exact argument order depends on the existing `FourRatSquaresAPConst` definition;
  -- grep that definition and make this a one-time adapter lemma.
  -- Expected proof shape:
  --   intro a d b c h1 h2
  --   have h1Q : (a:ℚ)^2 + (b:ℚ)^2 = 2 * (d:ℚ)^2 := by norm_num; exact_mod_cast h1
  --   have h2Q : (c:ℚ)^2 + (d:ℚ)^2 = 2 * (b:ℚ)^2 := by norm_num; exact_mod_cast h2
  --   have hconstQ := fourRatSquaresAPConst_checked h1Q h2Q
  --   exact_mod_cast hconstQ
  contradiction
```

Then:

```lean
lemma dividedBranch_unit_of_fourIntSquaresAPConst
    (h4 : FourIntSquaresAPConst)
    {A N S m n : ℤ}
    (hApos : 0 < A) (hNpos : 0 < N)
    (hB : DividedSquareBranch A N S m n) :
    A = 1 ∧ N = 1 ∧ S = 1 := by
  -- 1. Exclude both-odd parity using `dividedBranch_not_mn_both_odd`.
  -- 2. In the live opposite-parity case, obtain a,b,c,d by
  --    `dividedBranch_oppositeParity_factorization`.
  -- 3. Apply `dividedBranch_factorization_four_sq_ap`.
  -- 4. Apply `h4` to get:
  --      a^2 = d^2, d^2 = b^2, b^2 = c^2.
  -- 5. Since `m-n = a^2`, `m+n = 3*b^2`, and `a^2 = b^2`, get:
  --      n = b^2, m = 2*b^2.
  -- 6. From `IsCoprime m n`, get `b^2 = 1`; with `0 < b`, get `b = 1`.
  --      Hence `m = 2`, `n = 1`.
  -- 7. Substitute in the branch equations:
  --      3*A^2 = 3, so A^2=1, and `0<A` gives `A=1`.
  --      3*N^2 = 3, so N^2=1, and `0<N` gives `N=1`.
  --      3*S = 2^2 - 2*1 + 1^2 = 3, so `S=1`.
  contradiction
```

The final theorem for the residual can therefore be:

```lean
theorem dividedSquareBranchUnitOrDescends_of_fourIntSquaresAPConst
    (h4 : FourIntSquaresAPConst) :
    DividedSquareBranchUnitOrDescendsStatement := by
  intro A N S m n hBad hBranch
  left
  -- extract `0 < A`, `0 < N` from `PositivePrimitiveEisensteinBadUnordered`
  exact dividedBranch_unit_of_fourIntSquaresAPConst h4 hApos hNpos hBranch
```

If the existing `PositivePrimitiveEisensteinBadUnordered` excludes `A = 1 ∧ N = 1`, this theorem immediately gives contradiction for the divided branch. If it does not exclude it, the left branch is exactly the intended unit exception.

## 6. Why no smaller quartic formulas are needed here

In the divided branch, the corrected factorization does **not** naturally produce a smaller quartic solution `(A',N',S')`. It produces the four-squares-AP data

```lean
(a, d, b, c) : ℤ^4
```

with

```lean
a^2, d^2, b^2, c^2
```

in arithmetic progression. The non-unit case is killed by the AP theorem, not by an explicit quartic self-map. A claimed direct descent formula in `(A,N,S)` from this divided branch is therefore suspect unless it is just the classical four-squares-AP descent transported through the above variables.

Smallest honest residual boundary if you do not want to import `N12FourSquaresAP`:

```lean
def DividedBranchReducesToFourSquaresAPStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
    ∃ a d b c : ℤ,
      a ^ 2 + b ^ 2 = 2 * d ^ 2 ∧
      c ^ 2 + d ^ 2 = 2 * b ^ 2 ∧
      -- plus positivity/nonzero/gcd side conditions sufficient to recover unit from AP const
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
```

Then prove:

```lean
theorem dividedBranchUnit_of_reducesToAP
    (hRed : DividedBranchReducesToFourSquaresAPStatement)
    (hAP : FourIntSquaresAPConst) :
    DividedSquareBranchUnitStatement := by
  -- local reconstruction as above
  contradiction
```

But if `fourRatSquaresAPConst_checked` is already available, the shortest non-circular route is:

```lean
fourRatSquaresAPConst_checked
  → fourIntSquaresAPConst_checked
  → dividedBranch_unit_of_fourIntSquaresAPConst
  → dividedSquareBranchUnitOrDescendsStatement  -- left/unit branch
```

This route is independent of `RationalPointsN12`, `E1`, `E24`, and finite-point/full-cover residuals.

## 7. False steps to reject

1. **Do not assert `IsCoprime (m-n) (m+n)` unconditionally.**  
   It is false when `m,n` are both odd; the gcd is then `2` up to units.

2. **Do not apply `posSqOfCoprimeMulSq` directly to `(m-n)*(m+n)=3*A^2`.**  
   First divide the known factor of `3` out of `m+n`, and in the same-parity case also divide the common factor `2` correctly.

3. **Do not forget the second 3-divisible factor.**  
   From `3 ∣ m+n`, the factor divisible by `3` in the `N` equation is `2*m-n`, since
   `2*m-n = 2*(m+n) - 3*n`.

4. **Do not claim a direct quartic descent formula unless it is explicitly derived from the four-squares-AP descent.**  
   The actual local output of the divided branch is AP data, not an obvious smaller quartic triple.
