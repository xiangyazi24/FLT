# Q1257 (dm3): Elementary proof for `w^2 = u^3 + u^2 - u`

## Executive answer

The statement is true:

```text
w^2 = u^3 + u^2 - u,  u,w ∈ ℚ
```

has rational `u` only

```text
u ∈ {-1, 0, 1}.
```

But the important point is this:

```text
A one-shot prime-factorization argument gets you very close, but it does not finish the problem.
```

After clearing denominators correctly, the problem becomes two binary quartic equations. Those quartics are genus-one curves. Proving that they have only the trivial primitive solutions is essentially the same rank-zero content as the original elliptic curve. So there is no genuinely cheap local-prime-factorization proof hiding here.

There **is** a classical elementary route, in the old Fermat/descent sense:

```text
normalization over ℤ
  + coprime square-factor splitting
  + two explicit binary-quartic descent lemmas
```

or, equivalently and usually cleaner,

```text
explicit 2-isogeny descent on
E  : y^2 = x^3 + x^2 - x
E' : y^2 = x^3 - 2x^2 + 5x.
```

This uses no L-functions, no BSD, no modularity, no Selmer-group API, and no algebraic geometry. But it **is** descent. If “no descent machinery” means “do not import a general Mordell-Weil/descent library,” then yes, this is plausibly Lean-formalizable. If it means “no descent argument at all,” then I would not expect a short elementary proof: the obstruction is exactly a genus-one/rank-zero obstruction.

## Label note

The exact integral model

```text
[0, 1, 0, -1, 0]
```

i.e.

```text
y^2 = x^3 + x^2 - x
```

is currently listed by LMFDB as `20.a3` / Cremona `20a2`, with rank `0` and torsion `ℤ/6ℤ`:

```text
https://www.lmfdb.org/EllipticCurve/Q/?jinv=16384%2F5
```

The page `20.a4` is another curve in the same isogeny class; it also has rank `0` and torsion `ℤ/6ℤ`, but its displayed model is different:

```text
https://www.lmfdb.org/EllipticCurve/Q/20/a/4
```

This is only orientation. The proposed proof below does not depend on the database label.

## What the direct prime-factorization argument really gives

Start with

```text
w^2 = u^3 + u^2 - u.
```

Write `u = a / b` in lowest terms with `b > 0`. For every prime `p | b`, the numerator

```text
a(a^2 + ab - b^2)
```

is prime to `p`, because `p ∤ a` and

```text
a^2 + ab - b^2 ≡ a^2 mod p.
```

So

```text
v_p(u^3 + u^2 - u) = -3 v_p(b).
```

Since this valuation is the valuation of a square, `3 v_p(b)` is even. Hence `v_p(b)` is even for every `p`, so the denominator of `u` is a square. Thus write

```text
u = A / B^2,
w = C / B^3,
```

with

```text
A, B, C ∈ ℤ,
B > 0,
gcd(A, B) = 1.
```

Then

```text
C^2 = A^3 + A^2 B^2 - A B^4
    = A(A^2 + A B^2 - B^4).
```

The two factors on the right are coprime:

```text
gcd(A, A^2 + A B^2 - B^4)
  = gcd(A, B^4)
  = 1.
```

So if `A ≠ 0`, the two coprime factors must separately be signed squares.

If `A > 0`, then

```text
A = r^2
A^2 + A B^2 - B^4 = s^2
```

and therefore

```text
s^2 = r^4 + r^2 B^2 - B^4.        -- Q+
```

If `A < 0`, then

```text
A = -r^2
A^2 + A B^2 - B^4 = -s^2
```

and therefore

```text
s^2 = -r^4 + r^2 B^2 + B^4.        -- Q-
```

In both cases

```text
gcd(r, B) = 1,
B > 0.
```

Thus the whole problem reduces to the following two primitive binary-quartic lemmas.

```text
QuarticPlus:
  If gcd(r,B)=1, B>0, and s^2 = r^4 + r^2 B^2 - B^4,
  then r = 1 and B = 1.

QuarticMinus:
  If gcd(r,B)=1, B>0, and s^2 = -r^4 + r^2 B^2 + B^4,
  then r = 1 and B = 1.
```

Then:

```text
A = 0      -> u = 0,
A =  r^2  -> r = B = 1 -> u = 1,
A = -r^2  -> r = B = 1 -> u = -1.
```

This is the cleanest completely self-contained Diophantine reduction.

The catch is that `QuarticPlus` and `QuarticMinus` are not trivial congruence lemmas. They are the rank-zero statement in binary-quartic clothing. A proof of them by infinite descent is elementary, but it is still a descent proof.

## Why congruences alone are unlikely to finish it

The quartics

```text
s^2 =  r^4 + r^2 B^2 - B^4
s^2 = -r^4 + r^2 B^2 + B^4
```

have the same “shape” as elliptic-curve 2-coverings. Local congruence checks at small primes do not isolate only `r=B=1`; the obstruction is global.

For example, the first quartic can be rewritten as

```text
(2r^2 + B^2)^2 - (2s)^2 = 5B^4,
```

so a factorization in `ℤ[√5]` is natural. But after the factorization one still has to prove that any nontrivial primitive solution produces a strictly smaller primitive solution. That is infinite descent, not a local valuation contradiction.

Similarly, dividing by `B^4` gives

```text
(s/B^2)^2 = (r^2/B^2)^2 + (r^2/B^2) - 1,
```

which is a conic in the variable `r^2/B^2`; parametrizing the conic leaves the condition that this parameter is itself a rational square. That condition is again a genus-one condition, so the parametrization does not make the problem rational.

## The clean classical proof: explicit 2-isogeny descent

A very compact classical proof uses the rational 2-torsion point `(0,0)`.

Let

```text
E  : y^2 = x^3 + x^2 - x        = x(x^2 + x - 1),
E' : Y^2 = X^3 - 2X^2 + 5X     = X(X^2 - 2X + 5).
```

These are connected by a 2-isogeny

```text
φ : E -> E'
```

with kernel generated by `(0,0)`. For `x ≠ 0`, one explicit formula is

```text
φ(x,y) = ( y^2 / x^2,  y(-1 - x^2) / x^2 ).
```

The standard 2-isogeny descent map for a curve

```text
y^2 = x^3 + a x^2 + b x
```

is

```text
α(O)       = 1,
α((0,0))   = b mod ℚ*²,
α((x,y))   = x mod ℚ*²     if x ≠ 0.
```

For this curve, `b = -1`, so only the squareclasses

```text
1, -1
```

can occur. Both occur, for example from `O` and `(0,0)`, or from points with `x = ±1`. Thus

```text
#α(E(ℚ)) = 2.
```

For the isogenous curve `E'`, we have `a = -2`, `b = 5`, so the only possible squareclasses are

```text
±1, ±5.
```

The corresponding homogeneous spaces are

```text
R^2 = d S^4 - 2 S^2 T^2 + (5/d) T^4,
```

for squarefree `d | 5`, i.e. `d ∈ {1, 5, -1, -5}`.

For `d = -1`, the right-hand side is

```text
-S^4 - 2S^2T^2 - 5T^4,
```

which is negative unless `S = T = 0`, which is not a primitive point.

For `d = -5`, the right-hand side is

```text
-5S^4 - 2S^2T^2 - T^4,
```

again negative unless `S = T = 0`.

So only

```text
1, 5
```

occur, and

```text
#α'(E'(ℚ)) = 2.
```

The elementary 2-isogeny descent formula is

```text
2^rank(E(ℚ)) = #α(E(ℚ)) * #α'(E'(ℚ)) / 4.
```

Here this gives

```text
2^rank(E(ℚ)) = 2 * 2 / 4 = 1,
```

so

```text
rank E(ℚ) = 0.
```

This is the smallest classical proof I would trust. It is descent, but it is very small descent: squareclasses, explicit quartics, and a finite exact-sequence calculation.

## Torsion is elementary

The point

```text
P = (-1, 1)
```

has order `6`.

Indeed, using the group law on

```text
y^2 = x^3 + x^2 - x,
```

one checks

```text
2P = (1, -1),
3P = (0, 0),
6P = O.
```

So `E(ℚ)` has at least six torsion points:

```text
O,
(0,0),
(1,1),
(1,-1),
(-1,1),
(-1,-1).
```

To show there are no more torsion points, use reduction modulo good primes. The discriminant of this model is

```text
Δ = 80,
```

so `3` and `7` are good primes.

Counting directly:

```text
#E(𝔽_3) = 6,
#E(𝔽_7) = 6.
```

Reduction at good primes injects prime-to-`p` torsion into `E(𝔽_p)`. Using both `p=3` and `p=7`, every rational torsion prime-power is bounded by a group of order `6`. Hence

```text
#E(ℚ)_tors | 6.
```

Since we already have a point of order `6`,

```text
E(ℚ)_tors ≅ ℤ/6ℤ.
```

Together with rank `0`, this gives exactly

```text
E(ℚ) = { O, (0,0), (1,±1), (-1,±1) }.
```

Therefore the only rational `u`-coordinates are

```text
u ∈ {-1, 0, 1}.
```

## Lean-facing recommendation

For Lean, I would **not** formalize this by invoking a general elliptic-curve rank API. The smallest self-contained module is one of the following.

### Option A: direct Diophantine module

This avoids elliptic-curve group law almost entirely. It isolates the real work into two binary-quartic descent lemmas.

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace FLT.Diophantine20a3

/-- Positive binary-quartic obstruction.

Mathematical statement:
if `gcd r B = 1`, `B > 0`, and
`s^2 = r^4 + r^2 * B^2 - B^4`, then `r = 1` and `B = 1`.
-/
theorem quartic_plus_only_trivial
    (r B s : ℤ)
    (hB : 0 < B)
    (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s^2 = r^4 + r^2 * B^2 - B^4) :
    r = 1 ∧ B = 1 := by
  -- elementary infinite descent / Ljunggren-style binary quartic argument
  sorry

/-- Negative binary-quartic obstruction.

Mathematical statement:
if `gcd r B = 1`, `B > 0`, and
`s^2 = -r^4 + r^2 * B^2 + B^4`, then `r = 1` and `B = 1`.
-/
theorem quartic_minus_only_trivial
    (r B s : ℤ)
    (hB : 0 < B)
    (hr : 0 < r)
    (hcop : Int.gcd r B = 1)
    (h : s^2 = -r^4 + r^2 * B^2 + B^4) :
    r = 1 ∧ B = 1 := by
  -- elementary infinite descent / isogenous binary quartic argument
  sorry

/-- Main rational-coordinate conclusion. -/
theorem rational_u_only
    (u w : ℚ)
    (h : w^2 = u^3 + u^2 - u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  -- 1. write u = A / B^2, w = C / B^3 in normalized form;
  -- 2. prove C^2 = A(A^2 + A B^2 - B^4);
  -- 3. prove the two factors are coprime;
  -- 4. split A = 0, A > 0, A < 0;
  -- 5. apply quartic_plus_only_trivial or quartic_minus_only_trivial.
  sorry

end FLT.Diophantine20a3
```

This is probably the smallest theorem surface if the final FLT-side goal only needs the rational `u` values.

### Option B: explicit 2-isogeny-descent certificate

This is mathematically cleaner and avoids proving the two quartic lemmas separately, but it requires formalizing enough of the elliptic-curve group law and the descent exact sequence.

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace FLT.Diophantine20a3

/-- The concrete curve `E : y^2 = x^3 + x^2 - x`. -/
def E_rhs (x : ℚ) : ℚ := x^3 + x^2 - x

/-- The concrete 2-isogenous curve `E' : Y^2 = X^3 - 2X^2 + 5X`. -/
def Eprime_rhs (x : ℚ) : ℚ := x^3 - 2*x^2 + 5*x

/-- Concrete rank-zero certificate from 2-isogeny descent.

This should be proved by the squareclass calculations:
`α(E(ℚ)) = {1, -1}` and `α'(E'(ℚ)) = {1, 5}`.
-/
theorem rank_zero_certificate : True := by
  -- Replace `True` by the local statement that every rational point is torsion,
  -- or by the exact quotient statement used in the local development.
  trivial

/-- Torsion points on the concrete curve. -/
theorem rational_points_are_six
    (u w : ℚ)
    (h : w^2 = E_rhs u) :
    (u, w) = (-1, 1) ∨
    (u, w) = (-1, -1) ∨
    (u, w) = (0, 0) ∨
    (u, w) = (1, 1) ∨
    (u, w) = (1, -1) := by
  -- rank_zero_certificate + torsion by reduction mod 3 and 7
  sorry

/-- The projected `u`-coordinate statement. -/
theorem rational_u_only
    (u w : ℚ)
    (h : w^2 = E_rhs u) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  have hp := rational_points_are_six u w h
  rcases hp with h1 | h2 | h3 | h4 | h5
  · left; exact congrArg Prod.fst h1
  · left; exact congrArg Prod.fst h2
  · right; left; exact congrArg Prod.fst h3
  · right; right; exact congrArg Prod.fst h4
  · right; right; exact congrArg Prod.fst h5

end FLT.Diophantine20a3
```

The placeholder `rank_zero_certificate` should not remain as `True`; it is where the local 2-isogeny descent proof goes.

## Bottom line

A purely local prime-factorization proof is not enough. The denominator/gcd argument reduces the problem to two genus-one binary quartics, and those quartics are exactly where the rank-zero content lives.

The most Lean-plausible self-contained proof is therefore:

```text
Best if avoiding elliptic-curve APIs:
  prove QuarticPlus and QuarticMinus by explicit infinite descent,
  then finish by the denominator-square/gcd split.

Best if allowing minimal classical EC arithmetic:
  prove the concrete 2-isogeny descent certificate for E and E',
  prove torsion = ℤ/6ℤ by reduction mod 3 and 7,
  conclude the six rational points.
```

I would choose **Option A** if the target theorem only needs `u ∈ {-1,0,1}` and the Lean development wants to avoid elliptic-curve infrastructure. I would choose **Option B** if the development already has usable elliptic-curve group law and reduction modulo primes.
