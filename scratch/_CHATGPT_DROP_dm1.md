# Odd-`q` denominator case for `s² = p⁴ + p²q² - q⁴`

This is a Lean-oriented mathematical analysis of the proposed Pellian factorization.  I do **not** have a complete `0 sorry` Lean proof of the requested theorem from the stated ingredients alone; the factorization reaches a genuine infinite-descent/factor-splitting step, not an immediate contradiction.

The intended theorem is:

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

/-- Intended odd-denominator statement. -/
theorem no_denom_quartic_odd_q
    (p q s : ℤ)
    (hpq : IsCoprime p q)
    (hq_pos : 2 ≤ q)
    (hq_odd : ¬ (2 : ℤ) ∣ q)
    (h : s ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    False := by
  -- The Pellian factorization below gives the correct route, but the final
  -- coprime factor split still requires a nontrivial infinite descent.
  -- I am not marking this with `sorry` in the repository because the present
  -- file is Markdown; this is the exact target that remains.
  admit

end Scratch.ChatGPTDropDM1
```

The `admit` above is intentionally not a claimed proof.  The rest of this note records the correct reduction and the precise missing lemma.

## 1. The Pellian factorization is correct

Starting from

\[
s^2=p^4+p^2q^2-q^4,
\]

we get

\[
(2p^2+q^2)^2-4s^2=5q^4.
\]

So, with

\[
A=2p^2+q^2-2s,\qquad B=2p^2+q^2+2s,
\]

we have

\[
AB=5q^4,\qquad A+B=2(2p^2+q^2),\qquad B-A=4s.
\]

The corresponding Lean identities are routine ring calculations:

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

lemma denom_pell_identity (p q s : ℤ)
    (h : s ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    (2 * p ^ 2 + q ^ 2 - 2 * s) * (2 * p ^ 2 + q ^ 2 + 2 * s) = 5 * q ^ 4 := by
  nlinarith

lemma denom_pell_sum (p q s : ℤ) :
    (2 * p ^ 2 + q ^ 2 - 2 * s) + (2 * p ^ 2 + q ^ 2 + 2 * s) =
      2 * (2 * p ^ 2 + q ^ 2) := by
  ring

lemma denom_pell_diff (p q s : ℤ) :
    (2 * p ^ 2 + q ^ 2 + 2 * s) - (2 * p ^ 2 + q ^ 2 - 2 * s) = 4 * s := by
  ring

end Scratch.ChatGPTDropDM1
```

## 2. The proposed coprimality claim is almost right, but it requires work

Assume

\[
\gcd(p,q)=1,\qquad q\ge 2,\qquad q\text{ odd}.
\]

First, any common divisor of `s` and `q` is also a divisor of `p⁴`, because the equation reduces modulo `q` to

\[
s^2\equiv p^4 \pmod q.
\]

Thus `gcd(s,q)=1`.

Second, if `p` is even, the equation is impossible modulo `8` because `q` is odd.  Therefore in the remaining case `p,q,s` are all odd.  Then `A` and `B` are odd.

Now if a prime `r` divides both `A` and `B`, then `r` divides both `A+B` and `B-A`, hence it divides both

\[
2(2p^2+q^2) \quad\text{and}\quad 4s.
\]

Since `A,B` are odd, such an `r` is odd, so `r | (2p²+q²)` and `r | s`.  Also `r | AB = 5q⁴`.  Because `gcd(s,q)=1`, this leaves only the possible common prime `r=5`.

But `r=5` is also impossible.  If `5 | q`, then `2p²+q² ≡ 2p² (mod 5)`, nonzero because `gcd(p,q)=1`.  If `5 ∤ q`, then from `5 | s` and the original equation, dividing by `q⁴` modulo `5` gives

\[
(p/q)^4+(p/q)^2-1\equiv 0\pmod 5.
\]

For a nonzero square `X` modulo `5`, `X ∈ {1,4}`, and `X²+X-1` is `1` or `4` modulo `5`, never `0`.  Thus `5` cannot divide both factors.

So the desired conclusion is:

\[
\gcd(A,B)=1.
\]

This is a reasonable Lean lemma, but it is not just `omega`; it needs explicit prime-divisor or gcd reasoning.

## 3. The coprime factor split does not itself finish the proof

Once `A` and `B` are coprime positive integers and

\[
AB=5q^4,
\]

one can split the factors.  Up to swapping `A` and `B`, the structure is:

\[
A=a^4,\quad B=5b^4,\quad q=ab,
\]

or

\[
A=5a^4,\quad B=b^4,\quad q=ab.
\]

Substituting into `A+B=2(2p²+q²)` gives, in the first case,

\[
a^4+5b^4=4p^2+2a^2b^2,
\]

hence

\[
4p^2=a^4-2a^2b^2+5b^4. \tag{1}
\]

In the second case one obtains the symmetric equation

\[
4p^2=5a^4-2a^2b^2+b^4. \tag{2}
\]

These equations are not immediate contradictions.  They are the beginning of an infinite descent.  For example, in case `(1)`,

\[
4p^2=(a^2-b^2)^2+4b^4,
\]

so

\[
p^2=\left(\frac{a^2-b^2}{2}\right)^2+b^4,
\]

because `a,b` are odd.  This is a primitive Pythagorean-triple situation and must be parametrized.  The parametrization should then produce a smaller primitive solution, contradicting minimality of `q`.  That is exactly the missing descent step.

In other words, the proposed route is viable, but the proof is not finished after proving `A,B` coprime.  The nontrivial theorem needed is something like:

```lean
/-- Missing infinite-descent core for the odd-denominator case. -/
-- theorem odd_q_factor_split_descent
--     (p q s : ℤ)
--     (hpq : IsCoprime p q)
--     (hq_pos : 2 ≤ q)
--     (hq_odd : ¬ (2 : ℤ) ∣ q)
--     (h : s ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) : False
```

Proving this core requires the factor split plus Pythagorean parametrization or an equivalent squareclass descent.

## 4. Why this is essentially the dual descent again

The equations `(1)` and `(2)` are not accidental.  They are the hand-unrolled squareclass bookkeeping of the dual `2`-isogeny descent.  The split of `5q⁴` into coprime fourth-power parts records exactly which primes of `q` go into which descent factor, and the possible extra factor of `5` is the same special squareclass that appears in the dual Selmer set `{1,5}`.

So the odd-`q` denominator proof is likely best formalized in one of two ways:

1. **Explicit infinite descent from the factor split.**  This avoids elliptic-curve language, but it requires a full Pythagorean parametrization and a minimal-counterexample argument.
2. **Dual isogeny descent.**  This packages the same squareclass bookkeeping in the natural framework.  It is conceptually cleaner if the rest of the Selmer computation is already present.

## 5. Recommendation

For a Lean development, I would not try to close `no_denom_quartic_odd_q` from the Pellian factorization alone unless you are prepared to formalize the full infinite descent after the coprime factor split.  The factorization gets you to the right place, but not to the end.

The clean next theorem to prove is the coprime factor-split/descent core.  Once that is available, the intended theorem should be a short wrapper:

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

-- After proving the descent core, this wrapper should be immediate.
-- theorem no_denom_quartic_odd_q
--     (p q s : ℤ)
--     (hpq : IsCoprime p q)
--     (hq_pos : 2 ≤ q)
--     (hq_odd : ¬ (2 : ℤ) ∣ q)
--     (h : s ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
--     False :=
--   odd_q_factor_split_descent p q s hpq hq_pos hq_odd h

end Scratch.ChatGPTDropDM1
```

I would not mark the requested theorem as proved with a fake `0 sorry` proof: the missing step is mathematically substantive, not a Lean syntax issue.
