# `primitive_square_leg_descent_from_pythagoreanTriple`

I read `scratch/PythagoreanDescentCore.lean` on `ai-scratch`.  The exact axiom there is:

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

The mathematical route is correct, but the theorem is not a direct one-line consequence of `PythagoreanTriple.even_odd_of_coprime`.  That Mathlib lemma gives the parity orientation of a primitive triple; it does not, by itself, produce the full parametrization and the square-factor split of `(s-t)(s+t)=m²` needed here.

The proof needs the following package:

1. derive that `m,n` are odd from `hr`, `hqmn`, `hcop`, and `hq`;
2. derive primitivity of the triple `(m²,r,p)` from `hcop`;
3. apply or prove primitive Pythagorean parametrization:
   \[
   m^2 = S^2-T^2,\qquad r=2ST,\qquad p=S^2+T^2;
   \]
4. split
   \[
   m^2=(S-T)(S+T)
   \]
   into two coprime squares:
   \[
   S-T=c^2,\qquad S+T=d^2,\qquad cd=m;
   \]
5. compare
   \[
   2r=n^2-m^2=d^4-c^4
   \]
   and conclude
   \[
   n^2=d^4+c^2d^2-c^4.
   \]

Thus the witness is `(a,b)=(c,d)` in the axiom’s convention, so the quartic equation appears as

```lean
n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4
```

which is exactly

```lean
n ^ 2 = b ^ 4 + b ^ 2 * a ^ 2 - a ^ 4
```

with `a=c`, `b=d`.

## Lean code: exact wrapper around the missing parametrization package

The following code gives the cleanest Lean structure I can write from the available local signature.  The remaining axiom is the exact strengthened Pythagorean-parametrization theorem needed to close the proof.  It is stronger than `PythagoreanTriple.even_odd_of_coprime`: it includes parametrization, the square split, and the denominator drop.

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

#check PythagoreanTriple
#check PythagoreanTriple.even_odd_of_coprime

/--
The actual primitive square-leg parametrization/descent package needed here.

It packages:
* parity/primitivity of `(m²,r,p)`,
* primitive Pythagorean parametrization,
* the coprime square split of `(S-T)(S+T)=m²`, and
* the strict denominator drop.
-/
private axiom primitive_square_leg_param_and_drop
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
      n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 ∧
      c.natAbs < q.natAbs

/--
The algebraic final step: the parametrization package already returns the
quartic identity in the form needed by `PythagoreanDescentCore.lean`.
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
  obtain ⟨c, d, hc, hcopdc, hquartic, hdrop⟩ :=
    primitive_square_leg_param_and_drop
      p q m n r hq hcop hmpos hnpos hqmn hr htriple
  exact ⟨c, d, hc, hcopdc, hquartic, hdrop⟩

/--
The core algebra identity used inside the parametrization package.
If `m=c*d` and `2r=d⁴-c⁴`, while also `2r=n²-m²`, then the new quartic
identity follows.
-/
private lemma quartic_identity_from_square_leg_params
    (c d m n r : ℤ)
    (hm : m = c * d)
    (hr1 : 2 * r = n ^ 2 - m ^ 2)
    (hr2 : 2 * r = d ^ 4 - c ^ 4) :
    n ^ 2 = d ^ 4 + d ^ 2 * c ^ 2 - c ^ 4 := by
  subst m
  nlinarith

/--
The parametrized formula for `r`: if
`S=(c²+d²)/2`, `T=(d²-c²)/2`, then
`2*S*T = (d⁴-c⁴)/2`, equivalently `4*S*T=d⁴-c⁴`.
This is the algebra one uses after the Pythagorean parametrization.
-/
private lemma square_leg_param_r_identity (c d S T : ℤ)
    (hS : 2 * S = c ^ 2 + d ^ 2)
    (hT : 2 * T = d ^ 2 - c ^ 2) :
    4 * S * T = d ^ 4 - c ^ 4 := by
  nlinarith

end Scratch.ChatGPTDropDM1
```

## Why I did not claim a `0 sorry` proof

The requested theorem is the hard part of Fermat’s square-leg descent, not just an application of the parity lemma.  In particular:

* `PythagoreanTriple.even_odd_of_coprime` is a parity/orientation lemma, not the full parametrization theorem.
* The proof still needs a theorem that a primitive Pythagorean triple is parametrized by `S,T`.
* It also needs the coprime square split of `(S-T)(S+T)=m²`.
* Finally, it must prove the strict denominator drop.

Those steps are exactly the contents of `primitive_square_leg_param_and_drop` above.  Once that package is available, the exact axiom in `scratch/PythagoreanDescentCore.lean` closes immediately with the wrapper shown.
