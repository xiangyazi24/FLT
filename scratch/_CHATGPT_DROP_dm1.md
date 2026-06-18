# Can the denominator descent be reduced to `not_fermat_42`?

Short answer: not directly.  The intermediate equation

\[
p^2=m^4+r^2
\]

is **not** impossible by itself.  For example,

\[
5^2=2^4+3^2.
\]

So it cannot be reduced directly to Mathlib’s `not_fermat_42 : a^4+b^4\ne c^2`, because the second summand here is only a square, not a fourth power.  The missing information is the extra relation

\[
r=\frac{n^2-m^2}{2}
\]

coming from the Pellian factor split.  With that extra relation, the right route is not an immediate application of `not_fermat_42`; it is a **self-descent back to the same quartic equation**.

A tiny Lean sanity check for the obstruction to a direct route is:

```lean
import Mathlib

example : (5 : ℤ) ^ 2 = (2 : ℤ) ^ 4 + (3 : ℤ) ^ 2 := by
  norm_num
```

This shows that any proposed theorem of the form

```lean
-- false
-- theorem no_x4_plus_y2_eq_z2 (m r p : ℤ)
--     (hm : m ≠ 0) (hr : r ≠ 0) :
--     p ^ 2 = m ^ 4 + r ^ 2 → False
```

is simply false.

## 1. What the Pellian factor split really gives

Starting from

\[
t^2=p^4+p^2q^2-q^4,
\]

the factorization is

\[
(2p^2+q^2-2t)(2p^2+q^2+2t)=5q^4.
\]

In the odd-`q` coprime case, the expected factor split is, up to swapping the two factors,

\[
A=5m^4,\qquad B=n^4,\qquad q=mn.
\]

Using

\[
A+B=2(2p^2+q^2)
\]

we get

\[
5m^4+n^4=4p^2+2m^2n^2.
\]

Rearranging gives

\[
4p^2=(n^2-m^2)^2+4m^4.
\]

Since `m,n` are odd in this branch, `n²-m²` is even.  Put

\[
r=\frac{n^2-m^2}{2}.
\]

Then

\[
p^2=m^4+r^2. \tag{★}
\]

This is the equation that looked like a Fermat right-triangle obstruction.  But, as noted above, `(★)` alone has nontrivial solutions.

## 2. The extra relation gives a self-descent

The key is to use not only `(★)`, but also

\[
r=\frac{n^2-m^2}{2}.
\]

Assume the Pythagorean triple in `(★)` is primitive; this follows from the coprimality conditions in the factor split.  Since the square leg is `m²`, the usual primitive Pythagorean parametrization gives coprime integers `a,b` such that

\[
m^2=X^2-Y^2=(X-Y)(X+Y),
\]

and because `X-Y` and `X+Y` are coprime, both are squares:

\[
X+Y=a^2,\qquad X-Y=b^2.
\]

Thus

\[
m=ab,\qquad
X=\frac{a^2+b^2}{2},\qquad
Y=\frac{a^2-b^2}{2}.
\]

The even leg is

\[
r=2XY=\frac{a^4-b^4}{2}.
\]

But from the factor split we also have

\[
r=\frac{n^2-m^2}{2}=\frac{n^2-a^2b^2}{2}.
\]

Equating the two expressions for `r` gives

\[
n^2-a^2b^2=a^4-b^4.
\]

Therefore

\[
n^2=a^4+a^2b^2-b^4. \tag{†}
\]

This is exactly the **same denominator quartic** again, with a new solution

\[
(t',p',q')=(n,a,b).
\]

So the branch does not reduce to `a^4+b^4=c^2`; it reduces to a **smaller solution of the original quartic**.  This is the infinite descent.

In Lean-skeleton form, the descent step one wants is something like:

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

/-- Algebraic heart of the self-descent after the coprime factor split.
The variables here are schematic: `m,n` come from the factor split, and
`a,b` come from parametrizing the primitive Pythagorean triple
`p^2 = m^4 + ((n^2-m^2)/2)^2`. -/
lemma denominator_self_descent_identity (a b n : ℤ)
    (h : n ^ 2 - a ^ 2 * b ^ 2 = a ^ 4 - b ^ 4) :
    n ^ 2 = a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4 := by
  nlinarith

end Scratch.ChatGPTDropDM1
```

That identity is trivial; the hard part is producing `a,b` with the correct properties and proving that `|b|` is a strictly smaller positive denominator than the original `q=mn`.

## 3. Why `not_fermat_42` is the wrong endpoint

Mathlib’s `not_fermat_42` rules out

\[
a^4+b^4=c^2.
\]

That corresponds to a right triangle whose **two legs are both squares**: `a²` and `b²`.

Here, after the factor split, we only get a right triangle with one square leg:

\[
p^2=m^4+r^2.
\]

The other leg `r` is not a square in general.  Indeed the example

\[
5^2=2^4+3^2
\]

shows that such triangles exist.

The additional special form of `r` does not make `r` a square.  It makes the Pythagorean parametrization regenerate the original quartic with smaller denominator.  Thus the natural proof is a **minimal-denominator infinite descent**, not a one-shot appeal to `not_fermat_42`.

## 4. Possible indirect use of Mathlib’s FLT4 file

Although `not_fermat_42` itself does not directly solve this denominator step, the file `NumberTheory/FLT/Four.lean` may contain useful supporting lemmas around primitive Pythagorean triples or Fermat descent.  The relevant theorem to look for would not be `a^4+b^4≠c^2`, but rather a parametrization/descent lemma for a primitive right triangle with one square leg.

If Mathlib only exposes `not_fermat_42`, then it is probably not enough by itself.  One would still need to formalize the self-descent described above.

The useful abstract package would be:

```lean
namespace Scratch.ChatGPTDropDM1

/-- Desired descent step for the odd-denominator case.
Given a primitive odd-denominator solution with `q > 1`, construct another
primitive solution with strictly smaller positive denominator. -/
-- theorem denom_quartic_descent_step
--     (p q t : ℤ)
--     (hpq : IsCoprime p q)
--     (hq_pos : 2 ≤ q)
--     (hq_odd : ¬ (2 : ℤ) ∣ q)
--     (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
--     ∃ p' q' t' : ℤ,
--       1 ≤ q' ∧ q' < q ∧ IsCoprime p' q' ∧
--       t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4

/-- Once the descent step is available, the no-denominator theorem follows by
well-founded descent/minimal counterexample on positive `q`. -/
-- theorem no_denom_quartic_odd_q
--     (p q t : ℤ)
--     (hpq : IsCoprime p q)
--     (hq_pos : 2 ≤ q)
--     (hq_odd : ¬ (2 : ℤ) ∣ q)
--     (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
--     False := by
--   -- choose a minimal positive denominator counterexample and apply
--   -- `denom_quartic_descent_step` to contradict minimality
--   admit

end Scratch.ChatGPTDropDM1
```

## 5. Bottom line

I do not see a sound reduction from the Pellian factorization to Mathlib’s

```lean
not_fermat_42 : a^4 + b^4 ≠ c^2
```

because the intermediate right-triangle equation is `m^4 + r^2 = p^2`, and that equation has nontrivial solutions.

The promising route is instead:

1. perform the coprime factor split of
   `(2p²+q²-2t)(2p²+q²+2t)=5q⁴`;
2. derive `p²=m⁴+((n²-m²)/2)²`;
3. parametrize this primitive Pythagorean triple;
4. use the special relation `r=(n²-m²)/2` to produce a smaller solution
   `n²=a⁴+a²b²-b⁴`;
5. finish by infinite descent on the positive denominator.

This is a viable elementary route, but it is not a direct application of `not_fermat_42`.  It is the same descent mechanism reappearing in quartic form.
