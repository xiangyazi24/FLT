# `pythagorean_square_leg_self_descent_left5`

I analyzed the proposed step

\[
4p^2=(n^2-m^2)^2+4m^4,\qquad q=mn,
\]

with `q≥2`, `gcd(p,q)=1`, `m≥1`, `n≥1`.

The important point is that the suggested direct choice `q' = m` does **not** follow from the displayed equation.  The equation gives

\[
p^2=m^4+\left(\frac{n^2-m^2}{2}\right)^2,
\]

so it is a primitive Pythagorean triangle with one square leg.  But a triangle of the form

\[
p^2=m^4+r^2
\]

alone does not directly produce a new solution of

\[
t'^2=p'^4+p'^2q'^2-q'^4
\]

with `q'=m`.  In fact, `p²=m⁴+r²` has nontrivial solutions such as `5²=2⁴+3²`, so this is not an immediate contradiction or an immediate new quartic point.

The correct descent is:

1. Prove parity: in the odd-`q` branch, `m,n` are odd, so `r=(n²-m²)/2` is an integer.
2. Prove primitivity: `gcd(m,r)=1` from `gcd(p,mn)=1` and the coefficient identity.
3. Parametrize the primitive Pythagorean triple
   \[
   p^2=m^4+r^2.
   \]
   Since the square leg is `m²`, one gets coprime `a,b` with
   \[
   m=ab,\qquad r=\frac{a^4-b^4}{2}
   \]
   up to signs/swaps.
4. Compare with `r=(n²-m²)/2=(n²-a²b²)/2` and derive
   \[
   n^2=a^4+a^2b^2-b^4.
   \]
5. The new smaller quartic solution is therefore
   \[
   (p',q',t')=(a,b,n)
   \]
   or the swapped/sign-adjusted variant, **not** `(r,m,?)` and not directly `q'=m`.

So the theorem can be closed only after a formal primitive-Pythagorean-square-leg descent lemma is available.  The Lean skeleton below isolates exactly that lemma and proves the requested wrapper from it.

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

/--
The real arithmetic core: from the left-`5` factor branch coefficient identity,
perform the primitive Pythagorean parametrization and construct the smaller
solution of the same denominator quartic.

This is the step where one proves that from
`4p² = (n²-m²)² + 4m⁴`, `q=mn`, and the coprimality hypotheses, the
Pythagorean parametrization produces `a,b` with
`n² = a⁴ + a²b² - b⁴`, and with the new positive denominator strictly smaller
than `q`.
-/
private axiom pythagorean_square_leg_descent_core_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs

/--
Left-`5` Pythagorean self-descent wrapper.

This is the theorem requested at the wrapper level.  Its proof is immediate
once the primitive Pythagorean square-leg descent core is available.
-/
private theorem pythagorean_square_leg_self_descent_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  exact pythagorean_square_leg_descent_core_left5
    p q t m n hq hcop hmpos hnpos hqmn hcoeff

/--
A small algebraic identity used inside the real descent core.
If the Pythagorean parametrization gives
`n² - a²b² = a⁴ - b⁴`, then the new triple `(p',q',t')=(a,b,n)` satisfies
the denominator quartic.
-/
private lemma self_descent_new_solution_identity (a b n : ℤ)
    (h : n ^ 2 - a ^ 2 * b ^ 2 = a ^ 4 - b ^ 4) :
    n ^ 2 = a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4 := by
  nlinarith

/--
The false direct construction, recorded as a warning: from
`p²=m⁴+r²` alone one cannot build the desired new quartic solution with
`q'=m`.
-/
example : (5 : ℤ) ^ 2 = (2 : ℤ) ^ 4 + (3 : ℤ) ^ 2 := by
  norm_num

end Scratch.ChatGPTDropDM1
```

## Bottom line

The coefficient identity after the coprime split is correct, but the proposed direct construction with `q'=m` is missing the actual Pythagorean parametrization.  The smaller denominator arises from a factor of `m` produced by that parametrization, not from `m` itself.  Therefore the honest Lean proof needs a primitive Pythagorean square-leg descent lemma; once that lemma is formalized, the wrapper theorem above closes immediately.
