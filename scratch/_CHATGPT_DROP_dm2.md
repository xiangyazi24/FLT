# ChatGPT Drop File (dm2)

## Key correction

After the Pellian split

```text
A = 5m⁴,
B = n⁴,
mn = q,
```

the equation

```text
A+B = 2(2p²+q²)
```

gives

```text
5m⁴+n⁴ = 4p²+2m²n²,
```

hence

```text
(n²-m²)² + 4m⁴ = 4p².
```

So if

```text
r = (n²-m²)/2,
```

then

```text
p² = m⁴ + r².
```

This is a primitive Pythagorean triple with legs `m²` and `r`, and hypotenuse `p`.

The smaller denominator is **not** `m` directly.  One must first parametrize the Pythagorean triple.  Since `m²` is a square leg, the standard parametrization gives

```text
m² = u² - v² = (u-v)(u+v).
```

The two factors `u-v` and `u+v` are coprime, so each is a square:

```text
u-v = a²,
u+v = b²,
ab = m.
```

Then

```text
2r = n² - m²
```

and also

```text
2r = b⁴ - a⁴.
```

Therefore

```text
n² - a²b² = b⁴ - a⁴,
```

so

```text
n² = b⁴ + a²b² - a⁴.
```

This is exactly the same denominator quartic with

```text
p' = b,
q' = a,
t' = n.
```

Thus in the orientation

```text
A = 5m⁴,
B = n⁴,
```

the new smaller solution is

```text
(p', q', t') = (b, a, n).
```

In the opposite orientation

```text
A = m⁴,
B = 5n⁴,
```

the same argument is applied with the roles of `m` and `n` interchanged.  Then if the square-leg root `n` splits as `n = a*b`, the new solution is

```text
(p', q', t') = (b, a, m).
```

So the descent is:

```text
factor split → Pythagorean triple → split m = a*b → new quartic (b,a,n).
```

not simply

```text
q' = m.
```

The case `a = 1` is the base case `q' = 1`; then

```text
n² = b⁴ + b² - 1,
```

which is the `d=1` squeeze.  It forces `b = 1`, hence `m = 1`, `n = 1`, and `q = 1`, contradicting `q ≥ 2`.  Therefore in any genuine denominator descent, `2 ≤ a`, so the new denominator is valid.

## Lean code

The following code isolates the two standard ingredients:

1. `primitive_square_leg_param`: the primitive Pythagorean triple with square leg.
2. `d1_quartic_pos_only_unit`: the `d = 1` squeeze base case.

Everything after those two theorem boundaries is the exact algebraic construction of the smaller solution, including the explicit formulas

```text
p' = b,
q' = a,
t' = n.
```

```lean
import Mathlib

namespace DenominatorQuartic

/-- The positive denominator quartic. -/
def PosQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4

/-- The smaller-solution output used by the descent. -/
def SmallerSolution (p q t p' q' t' : ℤ) : Prop :=
  2 ≤ q' ∧
  Int.gcd p' q' = 1 ∧
  PosQuartic p' q' t' ∧
  q'.natAbs < q.natAbs

private lemma natAbs_lt_of_nonneg_of_lt {a q : ℤ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (h : a < q) :
    a.natAbs < q.natAbs := by
  omega

private lemma posQuartic_of_coeff_eq (a b n : ℤ)
    (h : n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4) :
    PosQuartic b a n := by
  unfold PosQuartic
  nlinarith

/--
Standard primitive Pythagorean triple with a square leg.

Input:

```text
p² = m⁴ + r²,
gcd(m,r)=1,
0 < m,
0 < r.
```

Output:

```text
m = a*b,
2r = b⁴ - a⁴,
gcd(a,b)=1,
```

after choosing the orientation with `b > a > 0`.

This packages the classical steps:

```text
m² = u²-v² = (u-v)(u+v),
u-v = a²,
u+v = b².
```
-/
axiom primitive_square_leg_param (p m r : ℤ)
    (hm : 1 ≤ m)
    (hr : 1 ≤ r)
    (hcop : Int.gcd m r = 1)
    (h : p ^ 2 = m ^ 4 + r ^ 2) :
    ∃ a b : ℤ,
      1 ≤ a ∧
      1 ≤ b ∧
      Int.gcd b a = 1 ∧
      m = a * b ∧
      2 * r = b ^ 4 - a ^ 4

/--
The `d = 1` squeeze base case:

```text
n² = b⁴ + b² - 1,  b ≥ 1  →  b = 1.
```

For `b ≥ 2`, this is the consecutive-square squeeze

```text
b⁴ < b⁴+b²-1 < (b²+1)².
```
-/
axiom d1_quartic_pos_only_unit (b n : ℤ)
    (hb : 1 ≤ b)
    (h : n ^ 2 = b ^ 4 + b ^ 2 - 1) :
    b = 1

/--
The exact smaller solution produced from one Pellian orientation.

This is the orientation

```text
A = 5m⁴,
B = n⁴,
mn = q,
r = (n²-m²)/2,
p² = m⁴+r².
```

After the square-leg parametrization splits `m = a*b`, the new solution is

```text
p' = b,
q' = a,
t' = n.
```
-/
theorem pythagorean_square_leg_descent_orientation (p q t m n r : ℤ)
    (hq : 2 ≤ q)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hm_lt_n : m < n)
    (hqmn : q = m * n)
    (hr : 1 ≤ r)
    (hrdef : 2 * r = n ^ 2 - m ^ 2)
    (hcop_mr : Int.gcd m r = 1)
    (hp : p ^ 2 = m ^ 4 + r ^ 2) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  obtain ⟨a, b, ha, hb, hcop_ba, hmab, hrab⟩ :=
    primitive_square_leg_param p m r hm hr hcop_mr hp

  -- Compare the two formulas for `2r`:
  --   2r = n² - m²
  --   2r = b⁴ - a⁴
  -- and use `m = a*b`.
  have hn_eq : n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 := by
    nlinarith

  -- Exclude the base case `a = 1` by the `d=1` squeeze.
  have ha2 : 2 ≤ a := by
    by_cases ha1 : a = 1
    · subst a
      have hb_eq_one : b = 1 := by
        apply d1_quartic_pos_only_unit b n hb
        simpa using hn_eq
      subst b
      have hm_eq_one : m = 1 := by nlinarith
      have hn_sq_one : n ^ 2 = 1 := by nlinarith
      have hn_eq_one : n = 1 := by nlinarith
      nlinarith
    · omega

  -- The new point is `(b,a,n)`.
  refine ⟨b, a, n, ?_⟩
  constructor
  · exact ha2
  constructor
  · exact hcop_ba
  constructor
  · exact posQuartic_of_coeff_eq a b n hn_eq
  · have hqpos : 0 ≤ q := by nlinarith
    have hapos : 0 ≤ a := by omega
    have hlt_a_q : a < q := by
      -- Since `m = a*b`, `b ≥ 1`, and `n > m ≥ a`, we have
      -- `q = m*n > a`.
      nlinarith
    exact natAbs_lt_of_nonneg_of_lt hapos hqpos hlt_a_q

/--
Opposite Pellian orientation.

If the split is

```text
A = m⁴,
B = 5n⁴,
```

then the square leg is `n²`, and the same theorem is used after swapping
`m` and `n`.  If `n = a*b`, the new solution is

```text
p' = b,
q' = a,
t' = m.
```
-/
theorem pythagorean_square_leg_descent_opposite_orientation (p q t m n r : ℤ)
    (hq : 2 ≤ q)
    (hm : 1 ≤ m)
    (hn : 1 ≤ n)
    (hn_lt_m : n < m)
    (hqmn : q = m * n)
    (hr : 1 ≤ r)
    (hrdef : 2 * r = m ^ 2 - n ^ 2)
    (hcop_nr : Int.gcd n r = 1)
    (hp : p ^ 2 = n ^ 4 + r ^ 2) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  -- Apply the previous orientation with `m` and `n` swapped, and with `m`
  -- as the new `t'` in the output.
  -- The theorem is syntactically repeated instead of using a complicated
  -- transport because the final formulas are clearer.
  obtain ⟨a, b, ha, hb, hcop_ba, hnab, hrab⟩ :=
    primitive_square_leg_param p n r hn hr hcop_nr hp

  have hm_eq : m ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 := by
    nlinarith

  have ha2 : 2 ≤ a := by
    by_cases ha1 : a = 1
    · subst a
      have hb_eq_one : b = 1 := by
        apply d1_quartic_pos_only_unit b m hb
        simpa using hm_eq
      subst b
      have hn_eq_one : n = 1 := by nlinarith
      have hm_sq_one : m ^ 2 = 1 := by nlinarith
      have hm_eq_one : m = 1 := by nlinarith
      nlinarith
    · omega

  refine ⟨b, a, m, ?_⟩
  constructor
  · exact ha2
  constructor
  · exact hcop_ba
  constructor
  · exact posQuartic_of_coeff_eq a b m hm_eq
  · have hqpos : 0 ≤ q := by nlinarith
    have hapos : 0 ≤ a := by omega
    have hlt_a_q : a < q := by
      nlinarith
    exact natAbs_lt_of_nonneg_of_lt hapos hqpos hlt_a_q

end DenominatorQuartic
```

## What remains to connect this to the Pellian split

The Pellian factor split must produce the hypotheses for one of the two orientation theorems above.

For the orientation

```text
A = 5m⁴,
B = n⁴,
```

one must supply:

```text
1 ≤ m,
1 ≤ n,
m < n,
q = mn,
r = (n²-m²)/2,
gcd(m,r)=1,
p² = m⁴+r².
```

The inequality `m < n` comes from ordering the Pellian factors so that

```text
5m⁴ = A ≤ B = n⁴.
```

For the opposite orientation, supply the swapped data.

Once those hypotheses are supplied, the exact new smaller solution is completely explicit:

```text
(p', q', t') = (b, a, n)
```

or in the opposite orientation

```text
(p', q', t') = (b, a, m).
```
