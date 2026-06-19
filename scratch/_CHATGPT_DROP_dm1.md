# `pythagorean_square_leg_descent_core_left5` via `PythagoreanTriple`

The target is to close the left-`5` branch after the coefficient comparison

\[
4p^2=(n^2-m^2)^2+4m^4,
\qquad q=mn,
\qquad 2\le q,
\qquad \gcd(p,q)=1,
\qquad 1\le m,n.
\]

The natural move is to set

\[
r=\frac{n^2-m^2}{2}.
\]

In the odd-`q` branch, `m` and `n` are odd, so `r` is integral.  Then the coefficient identity becomes

\[
p^2=m^4+r^2,
\]

so `(m²,r,p)` is a Pythagorean triple.

The important correction is that the new denominator is **not** obtained directly by setting `q'=m`.  The next step must use primitive Pythagorean parametrization.  From the primitive triple with square leg `m²`, one gets parameters `a,b` such that, up to signs and swaps,

\[
m=ab,\qquad r=\frac{b^4-a^4}{2}.
\]

Since also

\[
r=\frac{n^2-m^2}{2}=\frac{n^2-a^2b^2}{2},
\]

we obtain

\[
n^2=b^4+a^2b^2-a^4.
\]

Thus the new denominator-quartic solution is

\[
(p',q',t')=(b,a,n)
\]

or the swapped/sign-normalized equivalent.  The strict descent is `|a|<|q|`, not `|m|<|q|` directly.

Below is the best Lean structure for this step.  It explicitly uses `PythagoreanTriple` in the setup and isolates the exact primitive-parametrization theorem needed from Mathlib or from a local formalization.  The wrapper after that parametrization is purely algebraic.

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

#check PythagoreanTriple
#check PythagoreanTriple.even_odd_of_coprime

/--
Algebraic identity: if the Pythagorean parametrization yields
`n² = b⁴ + a²b² - a⁴`, then `(p',q',t') = (b,a,n)` satisfies the same
quartic denominator equation.
-/
private lemma new_solution_from_param_identity (a b n : ℤ)
    (h : n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4) :
    n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 := by
  exact h

/--
A packaging of the primitive Pythagorean square-leg descent needed here.

This is the theorem that must come either from Mathlib's `PythagoreanTriple`
API or from a local proof using it.  It says that from the primitive triple
`m², r, p`, together with the special relation `2r = n² - m²`, one obtains
parameters `a,b` producing a smaller denominator-quartic solution.
-/
private axiom primitive_square_leg_descent_from_pythagoreanTriple
    (p q m n r : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hr : 2 * r = n ^ 2 - m ^ 2)
    (htriple : PythagoreanTriple (m ^ 2) r p) :
    ∃ a b : ℤ,
      2 ≤ a ∧
      Int.gcd b a = 1 ∧
      n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4 ∧
      a.natAbs < q.natAbs

/--
The left-`5` Pythagorean self-descent core.

This is the wrapper around the `PythagoreanTriple` parametrization.  The only
substantive input is `primitive_square_leg_descent_from_pythagoreanTriple`;
once it supplies `a,b`, the final existential witness is `(b,a,n)` and the
quartic equation is algebraic.
-/
private theorem pythagorean_square_leg_descent_core_left5
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
  let r : ℤ := (n ^ 2 - m ^ 2) / 2
  have hr : 2 * r = n ^ 2 - m ^ 2 := by
    -- In the odd-`q` branch, `m,n` are odd, so `n²-m²` is divisible by `2`.
    -- This parity fact should be supplied from the odd-core context.
    -- Once available, `omega` closes this division identity.
    sorry
  have htriple : PythagoreanTriple (m ^ 2) r p := by
    -- `PythagoreanTriple x y z` is `x*x + y*y = z*z`.
    -- Use `hr` to rewrite `(n²-m²)² = (2r)²` in `hcoeff`.
    unfold PythagoreanTriple
    nlinarith
  obtain ⟨a, b, hapos, hcopba, hnew, hdrop⟩ :=
    primitive_square_leg_descent_from_pythagoreanTriple
      p q m n r hq hcop hmpos hnpos hqmn hr htriple
  refine ⟨b, a, n, hapos, hcopba, ?_, hdrop⟩
  exact new_solution_from_param_identity a b n hnew

end Scratch.ChatGPTDropDM1
```

## What remains for a true `0 sorry` proof

The line

```lean
primitive_square_leg_descent_from_pythagoreanTriple
```

is the exact missing theorem.  It is not merely the standard statement that every primitive Pythagorean triple is parametrized; it also has to combine that parametrization with the special relation

\[
2r=n^2-m^2
\]

and prove the strict denominator drop.

A fully expanded proof would need:

1. a parity lemma from the odd-`q` branch proving `2 ∣ n²-m²`;
2. a primitivity lemma proving the triple `(m²,r,p)` is primitive;
3. Mathlib's primitive Pythagorean parametrization theorem, or a local theorem derived from `PythagoreanTriple.even_odd_of_coprime` and its companion parametrization lemmas;
4. the coprime split `(a-b)(a+b)=m²`, giving `a-b=c²`, `a+b=d²`;
5. the algebraic identity producing `n²=d⁴+c²d²-c⁴` and the smaller denominator.

So the PythagoreanTriple route is correct, but the theorem needed is stronger than a single direct call to `PythagoreanTriple.even_odd_of_coprime`.  The code above isolates the exact API lemma that would make the left branch close cleanly.
