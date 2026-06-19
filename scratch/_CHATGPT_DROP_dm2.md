# ChatGPT Drop File (dm2)

## Question

Can one avoid the Pellian / `ℤ[φ]` denominator-quartic descent by using a direct height descent on the curve

```text
E : y² = x³ + x² - x?
```

The proposed idea is:

1. Take a rational point `P = (x,y)` with nonintegral squareclass coordinate

   ```text
   x = (s/q)²
   ```

   or

   ```text
   x = -(s/q)².
   ```

2. Compute the doubled point `2P`.
3. Show the denominator of `x(2P)` is strictly smaller than the denominator of `x(P)`.
4. Conclude by infinite descent.

## Doubling formula

For

```text
f(x) = x³ + x² - x,
```

the tangent slope is

```text
λ = f'(x)/(2y) = (3x² + 2x - 1)/(2y).
```

Since the Weierstrass equation is

```text
y² = x³ + a₂x² + a₄x + a₆
```

with `a₂ = 1`, the usual formula gives

```text
x(2P) = λ² - 1 - 2x.
```

Substituting `y² = x³+x²-x` and simplifying gives the important identity

```text
x(2P) = (x² + 1)² / (4x(x²+x-1)).
```

Indeed,

```text
x(2P)
 = (3x²+2x-1)² / (4(x³+x²-x)) - 1 - 2x
 = ((3x²+2x-1)² - 4(x³+x²-x)(1+2x)) / (4x(x²+x-1))
 = (x⁴ + 2x² + 1) / (4x(x²+x-1))
 = (x²+1)² / (4x(x²+x-1)).
```

## Positive squareclass substitution

Suppose

```text
x = s²/q²,
gcd(s,q)=1,
q ≥ 2.
```

Then the curve equation gives

```text
y² = (s²/q²) * (s⁴/q⁴ + s²/q² - 1)
   = s²(s⁴+s²q²-q⁴)/q⁶.
```

Thus, if `y` is rational, the denominator obstruction is exactly

```text
t² = s⁴ + s²q² - q⁴
```

with

```text
y = ± s*t/q³.
```

Now substitute into the doubling formula:

```text
x(2P)
 = (x²+1)² / (4x(x²+x-1))
 = (s⁴+q⁴)² / (4s²q²(s⁴+s²q²-q⁴))
 = (s⁴+q⁴)² / (4s²q²t²)
 = ((s⁴+q⁴)/(2sqt))².
```

So the doubled point again has positive squareclass, and an explicit square root is

```text
sqrt_x(2P) = (s⁴+q⁴)/(2sqt).
```

## Negative squareclass substitution

Suppose instead

```text
x = -s²/q².
```

Then

```text
y² = (-s²/q²) * (s⁴/q⁴ - s²/q² - 1)
   = s²(-s⁴+s²q²+q⁴)/q⁶.
```

So rationality gives the negative denominator quartic

```text
t² = -s⁴ + s²q² + q⁴.
```

Substituting into the same doubling formula again gives

```text
x(2P)
 = (s⁴+q⁴)² / (4s²q²(-s⁴+s²q²+q⁴))
 = ((s⁴+q⁴)/(2sqt))².
```

Thus both allowed squareclasses become positive-squareclass after doubling.

## Why the proposed denominator descent does not work directly

The formula is explicit, but it goes in the wrong direction for a naive denominator descent.

For the positive squareclass case, the square root of `x(2P)` is

```text
R = (s⁴+q⁴)/(2sqt).
```

After reducing this fraction, the new square-denominator is roughly

```text
|2sqt| / gcd(s⁴+q⁴, 2sqt).
```

There is no evident reason for this to be `< q`.  In fact the unreduced denominator contains the large factor `s*t*q`, so it is normally much larger than `q`.

The only way this could become smaller is through massive cancellation between

```text
s⁴+q⁴
```

and

```text
2sqt.
```

But the primitive hypotheses give the opposite kind of information:

```text
gcd(s⁴+q⁴, s) = 1,
gcd(s⁴+q⁴, q) = 1.
```

Any common divisor with `t` is highly restricted.  For an odd prime `ℓ` with

```text
ℓ ∣ t,
ℓ ∣ s⁴+q⁴,
ℓ ∤ sq,
```

using

```text
t² = s⁴+s²q²-q⁴
```

one obtains, modulo `ℓ`,

```text
q⁴ ≡ -s⁴,
0 ≡ s⁴+s²q²-q⁴ ≡ 2s⁴+s²q²,
```

so

```text
(q/s)² ≡ -2,
```

and also

```text
(q/s)^4 ≡ -1.
```

Hence

```text
4 ≡ -1 mod ℓ,
```

so `ℓ = 5`.  Thus the only systematic odd cancellation with `t` comes from `5`; powers of `2` require a separate parity check.  This is nowhere near enough to force the denominator of `x(2P)` below `q`.

This matches the general theory of heights: doubling should satisfy

```text
ĥ(2P) = 4 ĥ(P),
```

so one should not expect a naive denominator of `x(2P)` to decrease.  Height descent usually works by showing that a point is **divisible** and then passing to a preimage of smaller height, not by doubling the point.

## What the doubling formula does show

The formula gives a useful exact identity:

```text
x(2P) = square
```

whenever `x(P)` has squareclass `±1`.

This is consistent with the isogeny/descent picture:

```text
[2] = φ̂ ∘ φ,
```

and points in the allowed descent classes have doubles lying in the trivial positive squareclass.  But this is not by itself a denominator descent.

## Correct direction for a height descent

A viable height descent should go in the inverse direction:

```text
P is in the image of an isogeny or of [2]
    ⇒ choose Q with φ̂(Q)=P or 2Q=P
    ⇒ show height(Q) < height(P)
```

That requires an exactness/divisibility statement, for example:

```text
α(P)=1  ⇔  P ∈ φ̂(E'(Q)),
```

or the corresponding statement for `[2]`.  This is precisely the explicit exactness framework from the 2-isogeny descent.  It avoids Galois cohomology, but it does not avoid exactness.

So the direct doubling computation is useful algebra, but not a substitute for the denominator quartic or the isogeny-exactness argument.

## Lean code for the explicit computation

The following Lean code records the rational-function calculation.  It is intentionally limited to the part that is genuinely direct: the formula for `x(2P)` and the substitution for a square `x`.

```lean
import Mathlib

namespace Curve20a4

/-- The cubic defining `E : y² = x³+x²-x`. -/
def f (x : ℚ) : ℚ :=
  x ^ 3 + x ^ 2 - x

/-- The rational expression for the `x`-coordinate of `2P`. -/
def xDoubleRaw (x : ℚ) : ℚ :=
  ((3 * x ^ 2 + 2 * x - 1) ^ 2) / (4 * f x) - 1 - 2 * x

/-- The simplified doubling formula. -/
theorem xDouble_simplified (x : ℚ)
    (hx : x ≠ 0)
    (hxquad : x ^ 2 + x - 1 ≠ 0) :
    xDoubleRaw x = (x ^ 2 + 1) ^ 2 / (4 * x * (x ^ 2 + x - 1)) := by
  have hf : f x ≠ 0 := by
    unfold f
    have hmul : x * (x ^ 2 + x - 1) ≠ 0 := mul_ne_zero hx hxquad
    convert hmul using 1 <;> ring
  unfold xDoubleRaw f
  field_simp [hf, hx, hxquad]
  ring

/-- Positive squareclass substitution.

If `x=(s/q)²` and `t²=s⁴+s²q²-q⁴`, then

`x(2P)=((s⁴+q⁴)/(2sqt))²`.
-/
theorem xDouble_pos_square (s q t : ℚ)
    (hs : s ≠ 0) (hq : q ≠ 0) (ht : t ≠ 0)
    (hquartic : t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4) :
    xDoubleRaw ((s / q) ^ 2) =
      ((s ^ 4 + q ^ 4) / (2 * s * q * t)) ^ 2 := by
  have hx : (s / q) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (div_ne_zero hs hq)
  have hxquad : ((s / q) ^ 2) ^ 2 + (s / q) ^ 2 - 1 ≠ 0 := by
    intro hzero
    have : t ^ 2 = 0 := by
      field_simp [hq] at hzero
      nlinarith
    exact ht (sq_eq_zero_iff.mp this)
  rw [xDouble_simplified ((s / q) ^ 2) hx hxquad]
  field_simp [hs, hq, ht]
  nlinarith

/-- Negative squareclass substitution.

If `x=-(s/q)²` and `t²=-s⁴+s²q²+q⁴`, then again

`x(2P)=((s⁴+q⁴)/(2sqt))²`.
-/
theorem xDouble_neg_square (s q t : ℚ)
    (hs : s ≠ 0) (hq : q ≠ 0) (ht : t ≠ 0)
    (hquartic : t ^ 2 = -s ^ 4 + s ^ 2 * q ^ 2 + q ^ 4) :
    xDoubleRaw (-((s / q) ^ 2)) =
      ((s ^ 4 + q ^ 4) / (2 * s * q * t)) ^ 2 := by
  have hx : -((s / q) ^ 2) ≠ 0 := by
    exact neg_ne_zero.mpr (pow_ne_zero 2 (div_ne_zero hs hq))
  have hxquad : (-((s / q) ^ 2)) ^ 2 + (-((s / q) ^ 2)) - 1 ≠ 0 := by
    intro hzero
    have : t ^ 2 = 0 := by
      field_simp [hq] at hzero
      nlinarith
    exact ht (sq_eq_zero_iff.mp this)
  rw [xDouble_simplified (-((s / q) ^ 2)) hx hxquad]
  field_simp [hs, hq, ht]
  nlinarith

end Curve20a4
```

## Bottom line

The explicit computation is:

```text
x(2P)= (x²+1)² / (4x(x²+x-1)).
```

For both allowed squareclasses `x=±(s/q)²`, this becomes

```text
x(2P)=((s⁴+q⁴)/(2sqt))².
```

This does **not** give a natural denominator-decreasing descent.  The denominator after doubling normally grows, and any proof that it always shrinks would have to use hidden deep cancellation equivalent to the original quartic obstruction.

Therefore, the doubling formula alone is not a viable replacement for the Pellian/`ℤ[φ]` descent.  A height descent should instead use explicit divisibility/exactness to pass from `P` to a smaller preimage, not from `P` to `2P`.
