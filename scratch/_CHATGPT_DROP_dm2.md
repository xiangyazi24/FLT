# Q1269 (dm2): `QuarticMinus` by descent, via `QuarticPlus` symmetry

## Statement

Let `r, B` be positive coprime integers and suppose

```text
s^2 = -r^4 + r^2 B^2 + B^4.
```

Equivalently,

```text
s^2 = B^4 + B^2 r^2 - r^4.
```

This is exactly the `QuarticPlus` equation with the two variables swapped.  If

```text
QuarticPlus(x,y,z) : z^2 = x^4 + x^2 y^2 - y^4,
```

and

```text
QuarticMinus(r,B,s) : s^2 = -r^4 + r^2 B^2 + B^4,
```

then

```text
QuarticMinus(r,B,s)  <->  QuarticPlus(B,r,s).
```

Therefore the `QuarticMinus` theorem is not a new descent theorem.  It is the existing `QuarticPlus` infinite descent applied to `(x,y) = (B,r)`.  The descent variable for `QuarticMinus` is `r`, because `r` is the second variable in the corresponding `QuarticPlus` solution.

The only positive coprime solution is

```text
r = B = 1,
```

with `s = ±1` if `s` is allowed to be signed.

## Lean-facing reduction

If the repository already has a theorem for `QuarticPlus`, the clean proof should be a one-line swap, not a duplicate factorization proof.

```lean
import Mathlib

namespace QuarticDescent

/-- Schematic predicate; use the repository's actual definition. -/
def QuarticPlus (x y z : ℤ) : Prop :=
  z ^ 2 = x ^ 4 + x ^ 2 * y ^ 2 - y ^ 4

/-- Schematic predicate; use the repository's actual definition. -/
def QuarticMinus (r B s : ℤ) : Prop :=
  s ^ 2 = -r ^ 4 + r ^ 2 * B ^ 2 + B ^ 4

lemma quarticMinus_iff_quarticPlus_swap (r B s : ℤ) :
    QuarticMinus r B s ↔ QuarticPlus B r s := by
  unfold QuarticMinus QuarticPlus
  ring_nf

end QuarticDescent
```

The final theorem should use the existing `QuarticPlus` result like this, modulo the repository's actual integer/natural conventions:

```lean
import Mathlib

namespace QuarticDescent

-- Schematic theorem name and hypotheses; replace by the existing QuarticPlus theorem.
axiom quarticPlus_only_one
    {x y z : ℤ}
    (hx : 0 < x) (hy : 0 < y)
    (hcop : Int.gcd x y = 1)
    (h : QuarticPlus x y z) :
    x = 1 ∧ y = 1

theorem quarticMinus_only_one
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hcop : Int.gcd r B = 1)
    (h : QuarticMinus r B s) :
    r = 1 ∧ B = 1 := by
  have hplus : QuarticPlus B r s := (quarticMinus_iff_quarticPlus_swap r B s).1 h
  have hcop' : Int.gcd B r = 1 := by
    simpa [Int.gcd_comm] using hcop
  rcases quarticPlus_only_one hB hr hcop' hplus with ⟨hB1, hr1⟩
  exact ⟨hr1, hB1⟩

end QuarticDescent
```

The `axiom` in this snippet is only a placeholder for the already-proved `QuarticPlus` theorem.  Do **not** add this axiom to the repository.

## Full descent, written directly for `QuarticMinus`

Here is the descent argument after performing the variable swap explicitly.

Assume a positive coprime solution

```text
s^2 = B^4 + B^2 r^2 - r^4.        (1)
```

Set

```text
X = 2B^2 + r^2.
```

Then

```text
X^2 - (2s)^2 = 5r^4,
```

so

```text
(X - 2s)(X + 2s) = 5r^4.          (2)
```

This is exactly the `QuarticPlus` factorization for the solution `(x,y,z) = (B,r,s)`.

### Factor-splitting lemma

Use the same factor-splitting lemma as in `QuarticPlus`, applied to `(B,r,s)`.

After possibly replacing `s` by `-s`, the two positive factors in (2) may be written

```text
X - 2s = a^4,
X + 2s = 5b^4,
r = ab,                             (3)
```

with

```text
a > 0,
b > 0,
gcd(a,b) = 1.
```

This is the point where the `QuarticPlus` parity/coprimality work is used.  In direct `QuarticMinus` language, it is the same argument with `r` playing the role of the second `QuarticPlus` variable.

For reference, once the parity lemma gives `r` odd, the coprimality check is short.  Both factors are odd.  If an odd prime `q` divides both factors, then `q | s` and `q | X`.  From

```text
X^2 - 4s^2 = 5r^4
```

we get `q | 5r^4`.  If `q | r`, then `q | X = 2B^2 + r^2` gives `q | B`, contradicting `gcd(r,B)=1`.  If `q = 5`, then `2B^2 + r^2 ≡ 0 mod 5`; when neither `r` nor `B` is divisible by `5`, this says `(r/B)^2 ≡ -2 ≡ 3 mod 5`, impossible because `3` is not a quadratic residue modulo `5`, and the cases `5 | r` or `5 | B` also contradict `gcd(r,B)=1` together with `X ≡ 0`.  Hence the two factors are coprime.  Since their product is `5r^4`, unique prime factorization gives (3), after choosing the sign of `s` so that the factor containing the single `5 mod 4` exponent is the larger factor.

### From the factorization to a Pythagorean triple

Add the two equations in (3):

```text
2X = a^4 + 5b^4.
```

Since `X = 2B^2 + r^2` and `r = ab`, this gives

```text
4B^2 + 2a^2b^2 = a^4 + 5b^4,
```

hence

```text
4B^2 = a^4 - 2a^2b^2 + 5b^4
     = (a^2 - b^2)^2 + 4b^4.
```

Dividing by `4`,

```text
B^2 = ((a^2 - b^2)/2)^2 + b^4.      (4)
```

The two legs in (4), namely

```text
u = |a^2 - b^2| / 2,
v = b^2,
```

are coprime, and `v` is odd.  Thus `(u,v,B)` is a primitive Pythagorean triple.  Therefore there are coprime positive integers `m > n`, of opposite parity, such that

```text
u = 2mn,
b^2 = m^2 - n^2,
B = m^2 + n^2.                     (5)
```

Now

```text
b^2 = (m-n)(m+n).
```

Because `m` and `n` are coprime and of opposite parity,

```text
gcd(m-n, m+n) = 1.
```

So both factors are squares:

```text
m - n = e^2,
m + n = f^2,
b = ef,                             (6)
```

with

```text
0 < e < f,
gcd(e,f) = 1.
```

Using (6),

```text
m = (e^2 + f^2)/2,
n = (f^2 - e^2)/2.
```

Since `u = |a^2 - b^2|/2 = 2mn`, we have

```text
|a^2 - b^2| = 4mn = f^4 - e^4.      (7)
```

Also `b^2 = e^2 f^2`.  There are two cases.

#### Case 1: `a^2 >= b^2`

Then (7) gives

```text
a^2 - b^2 = f^4 - e^4,
```

so

```text
a^2 = f^4 + e^2 f^2 - e^4.         (8)
```

Thus `(f,e,a)` is a new `QuarticPlus` solution, and equivalently `(e,f,a)` is a new `QuarticMinus` solution:

```text
a^2 = -e^4 + e^2 f^2 + f^4.
```

Its first `QuarticMinus` variable is `e`.

#### Case 2: `a^2 < b^2`

Then (7) gives

```text
b^2 - a^2 = f^4 - e^4,
```

so

```text
a^2 = e^4 + e^2 f^2 - f^4.         (9)
```

Thus `(e,f,a)` is a new `QuarticPlus` solution, and equivalently `(f,e,a)` is a new `QuarticMinus` solution:

```text
a^2 = -f^4 + f^2 e^2 + e^4.
```

Its first `QuarticMinus` variable is `f`.

### The descent is strict

The original first `QuarticMinus` variable was

```text
r = ab = aef.
```

In Case 1 the new first variable is `e`, and clearly

```text
0 < e < aef = r.
```

In Case 2 the new first variable is `f`.  Again

```text
0 < f < aef = r,
```

except possibly if `a = e = 1`; but in Case 2 that would force

```text
a^2 = e^4 + e^2 f^2 - f^4 = 1 + f^2 - f^4 < 0
```

for `f > 1`, impossible.  Since `f > e > 0`, this exception cannot occur.  Hence the descent is strict in all nontrivial cases.

Therefore any nontrivial positive coprime `QuarticMinus` solution produces a smaller positive coprime `QuarticMinus` solution, with smaller first coordinate `r`.  Infinite descent on the positive integer `r` is impossible.

## Base case

It remains to identify the bottom solution.  If `r = 1`, then (1) becomes

```text
s^2 = B^4 + B^2 - 1.
```

Equivalently,

```text
(2B^2 + 1)^2 - (2s)^2 = 5,
```

so

```text
(2B^2 + 1 - 2s)(2B^2 + 1 + 2s) = 5.
```

Both factors are positive integers.  Hence they are `1` and `5`, so their sum is `6`:

```text
2(2B^2 + 1) = 6.
```

Thus

```text
2B^2 + 1 = 3,
B^2 = 1,
B = 1.
```

Then the original equation gives `s^2 = 1`.

## Final conclusion

Every positive coprime solution of

```text
s^2 = -r^4 + r^2B^2 + B^4
```

is forced by infinite descent to the base case.  Hence

```text
r = B = 1,
```

and then

```text
s = ±1
```

if `s` is an integer.

The clean formal route is to avoid duplicating the descent: prove the swap lemma

```text
QuarticMinus(r,B,s) <-> QuarticPlus(B,r,s),
```

then apply the already-proved `QuarticPlus` theorem.
