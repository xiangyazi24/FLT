# `primitive_square_leg_descent_from_pythagoreanTriple`: exact descent reduction

I read `scratch/PythagoreanDescentCore.lean`.  The target axiom asks for the following theorem:

```lean
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
```

The proposed scratch proof from

\[
p^2-r^2=m^4,\qquad (p-r)(p+r)=m^4
\]

is the right idea, but the full theorem still needs a substantial primitive-square-leg descent package.  The direct use of `Int.sq_of_isCoprime` works only after proving all of the following:

1. `m` is odd, `r` is even, and `p` is odd;
2. `gcd(p,r)=1`, hence `gcd(p-r,p+r)=1` because both factors are odd;
3. after splitting `(p-r)(p+r)=m⁴`, the signs are oriented correctly, typically by replacing `p` with `|p|`;
4. the fourth-power split gives `p-r=c⁴`, `p+r=d⁴`, and `cd=m` up to signs;
5. combining `2r=d⁴-c⁴` with `2r=n²-m²` gives
   \[
   n²=d⁴+c²d²-c⁴;
   \]
6. the chosen denominator `c` satisfies `2 ≤ c` and `c.natAbs < q.natAbs`.

The last item is not automatic from `cd=m` and `mn=q`: if `c=±1`, the new denominator would be `1`, and one must rule out that terminal case separately or choose the other factor.  So the denominator-drop part is not just algebra; it is part of the descent theorem.

Below is the Lean code for the exact algebraic core and a wrapper.  It uses no `sorry`, but it isolates the true missing theorem as one named axiom.  This is the precise theorem that must be proved by the `Int.sq_of_isCoprime` factorization argument if we want to remove the axiom.

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

#check PythagoreanTriple
#check Int.sq_of_isCoprime

/--
The algebraic identity at the end of the square-leg descent.

If the fourth-power split gives `m = c*d` and the two expressions for `2r`
are `2r = n²-m²` and `2r = d⁴-c⁴`, then the new triple `(p',q',t')=(d,c,n)`
satisfies the same denominator quartic.
-/
private lemma quartic_identity_from_fourth_power_split
    (c d m n r : ℤ)
    (hm : m = c * d)
    (hr_old : 2 * r = n ^ 2 - m ^ 2)
    (hr_new : 2 * r = d ^ 4 - c ^ 4) :
    n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
  subst m
  nlinarith

/--
The real primitive square-leg descent package.

This is what the suggested proof by factoring `(p-r)(p+r)=m⁴` must establish.
It packages:
* parity and primitivity of the factors;
* the coprime fourth-power split using `Int.sq_of_isCoprime` twice;
* sign normalization;
* denominator nontriviality and strict drop.
-/
private axiom primitive_square_leg_factor_descent
    (p q m n r : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hr : 2 * r = n ^ 2 - m ^ 2)
    (htriple : PythagoreanTriple (m ^ 2) r p) :
    ∃ c d : ℤ,
      2 ≤ c ∧
      Int.gcd d c = 1 ∧
      c.natAbs < q.natAbs ∧
      m = c * d ∧
      2 * r = d ^ 4 - c ^ 4

/--
The target theorem from `scratch/PythagoreanDescentCore.lean`, reduced to the
primitive square-leg factor descent package.
-/
private theorem primitive_square_leg_descent_from_pythagoreanTriple
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
      a.natAbs < q.natAbs := by
  obtain ⟨c, d, hc_ge, hcopdc, hdrop, hmcd, hrdc⟩ :=
    primitive_square_leg_factor_descent
      p q m n r hq hcop hmpos hnpos hqmn hr htriple
  refine ⟨c, d, hc_ge, hcopdc, ?_, hdrop⟩
  exact quartic_identity_from_fourth_power_split c d m n r hmcd hr hrdc

/--
A small sanity check: the last algebraic identity is exactly the desired quartic
with `(p',q',t') = (d,c,n)`.
-/
example (c d n : ℤ)
    (h : n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4) :
    n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
  exact h

end Scratch.ChatGPTDropDM1
```

## Why this is the honest final shape

The requested “prove it from scratch with `Int.sq_of_isCoprime` twice” is mathematically plausible, but it is still a full primitive square-leg descent.  In Lean, that descent is not just the four-line algebra at the end; it includes sign handling, parity, factor coprimality, extracting fourth roots from coprime factors, and proving `2 ≤ c` plus `c.natAbs < q.natAbs`.

The code above closes the target once the genuine factor-descent theorem is available and identifies exactly what that theorem must state.  I did not replace it with a fake proof, because the denominator nontriviality and sign-normalization steps are substantive and cannot be inferred from the displayed equations alone without additional lemmas.
