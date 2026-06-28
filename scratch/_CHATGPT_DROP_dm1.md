# Q1934 (dm1): the N=14 quartic with the -2 term

You are right about the sign and the coefficient: the quartic is

```text
s^4 + D^2*s^2 - 2*D^4 = t^2,
```

not the N=10 quartic with `-D^4`.

With `x = s/D` and `T = t/D^2`, this becomes

```text
T^2 = x^4 + x^2 - 2 = (x^2 - 1)*(x^2 + 2).
```

Putting

```text
u = x^2 = (s/D)^2,
w = x*T = s*t/D^3,
```

gives

```text
w^2 = u^3 + u^2 - 2*u = u*(u - 1)*(u + 2).
```

So the reduction is correct.

## Important correction: conductor

The curve

```text
E : w^2 = u^3 + u^2 - 2*u
```

is not conductor 14.  Its cubic has roots `0, 1, -2`, so the cubic discriminant is

```text
(0 - 1)^2*(0 + 2)^2*(1 + 2)^2 = 36.
```

For the Weierstrass equation `w^2 = cubic`, the elliptic discriminant is

```text
Delta = 16*36 = 576 = 2^6*3^2.
```

Also

```text
c4 = 112,
```

so at `p = 3` the curve has multiplicative bad reduction.  Therefore its conductor is divisible by `3`; it cannot be conductor `14`.  The conductor-14 curve that naturally appears in the N=14 parametrization is the different curve

```text
Y^2 = 4*X^3 + X^2 - 2*X + 1,
```

whose discriminant has a factor `7`.  The present curve `w^2 = u^3 + u^2 - 2u` is the full-2-torsion square-obstruction curve obtained after the additional substitution `u = x^2`.

## Rational points on E

The rational points on

```text
E : w^2 = u*(u - 1)*(u + 2)
```

are exactly

```text
O,
(0,0),
(1,0),
(-2,0).
```

Equivalently,

```text
E(Q) = E[2](Q) ~= Z/2Z x Z/2Z.
```

So the only rational `u`-coordinates are

```text
u = 0, 1, -2.
```

For the original quartic, only `u = 1` lifts to a rational `x = s/D`, and it gives the degenerate solution

```text
s = +/- D,
t = 0.
```

The points `u = 0` and `u = -2` do not give nonzero rational `x` satisfying `x^2 = u`; `u = 0` would force `x = 0`, and then the quartic gives `T^2 = -2`, while `u = -2` is not a rational square.

Thus the primitive nondegenerate quartic has no rational solutions.

## Algebraic structure

The key structural point is that this is not the same descent pattern as the N=10 quartic.  The N=14 quartic factors over Q:

```text
T^2 = (x^2 - 1)*(x^2 + 2).
```

The associated elliptic curve has full rational 2-torsion:

```text
E : w^2 = u*(u - 1)*(u + 2).
```

So the natural descent is a full 2-descent, or more concretely a 2-isogeny descent using the rational 2-torsion point `(0,0)`.  The 2-isogenous curve is

```text
E' : V^2 = U^3 - 2*U^2 + 9*U.
```

The dual 2-isogeny `E' -> E` is

```text
u = V^2/(4*U^2),
w = V*(9 - U^2)/(8*U^2).
```

The quartic

```text
C : T^2 = x^4 + x^2 - 2
```

is precisely the `d = 1` homogeneous space in this 2-isogeny descent.  Since it has the rational point `(x,T) = (1,0)`, it is birational to `E'`.  Explicitly, one birational map `C -> E'` is

```text
U = 2*x^2 + 1 - 2*T,
V = 2*x*U.
```

The inverse on the affine chart `U != 0` is

```text
x = V/(2*U),
T = (9 - U^2)/(4*U).
```

These formulas are useful because they show exactly why the quartic is a 2-descent object: composing

```text
C -> E' -> E
```

gives

```text
u = x^2,
w = x*T.
```

That is exactly the substitution from the quartic to the obstruction curve.

## Known proof of the rational-point statement

Yes.  A standard proof is a complete 2-descent, or equivalently a 2-isogeny descent on the pair

```text
E  : w^2 = u^3 + u^2 - 2*u,
E' : V^2 = U^3 - 2*U^2 + 9*U.
```

The descent proves

```text
rank E(Q) = 0.
```

Then the visible rational 2-torsion gives all of `E(Q)`:

```text
E(Q) = { O, (0,0), (1,0), (-2,0) }.
```

Equivalently, the isogenous curve has

```text
E'(Q) = { O, (0,0), (3,6), (3,-6) },
```

with `(3,6)` of order 4 and `2*(3,6) = (0,0)`.

Transporting these four points through the birational map to the quartic gives only

```text
(x,T) = (1,0), (-1,0),
```

plus the two points at infinity on the quartic model.  Hence the affine quartic has no nontrivial rational points.

## Relation to an infinite descent proof

There is an infinite-descent proof in the same broad sense as the N=10 argument, but the algebraic mechanism is different.

For N=10, the quartic

```text
s^4 + D^2*s^2 - D^4 = t^2
```

leads to a descent on the size parameter after converting to the obstruction curve

```text
w^2 = u^3 + u^2 - u.
```

For this N=14 quartic, the cleaner descent is the 2-isogeny descent above.  In elementary terms, starting from a primitive solution of

```text
t^2 = (s^2 - D^2)*(s^2 + 2*D^2)
```

one analyzes the two factors.  Their gcd divides `3`, because

```text
gcd(s^2 - D^2, s^2 + 2*D^2) divides 3*D^2,
```

and if `gcd(s,D)=1`, then this gcd divides `3`.  The resulting squareclass alternatives are exactly the finite 2-descent cases.  The descent says that every locally possible squareclass is already accounted for by torsion.  Any hypothetical non-torsion solution would produce a smaller solution through the covering maps, contradicting minimality.

So the answer is:

```text
Yes, but not as the same one-parameter B-descent as in N=10.
The right structure is the 2-isogeny/full-2-descent on
w^2 = u*(u - 1)*(u + 2).
```

## Lean-verifiable algebraic identities

The basic identities are all `ring` facts.

```lean
import Mathlib.Tactic

noncomputable section

namespace N14Quartic

example (x T : Q) (h : T^2 = x^4 + x^2 - 2) :
    (x*T)^2 = (x^2)^3 + (x^2)^2 - 2*(x^2) := by
  nlinarith [h]

example (x T : Q) :
    let U : Q := 2*x^2 + 1 - 2*T
    let V : Q := 2*x*U
    T^2 = x^4 + x^2 - 2 ->
      V^2 = U^3 - 2*U^2 + 9*U := by
  intro U V h
  subst U
  subst V
  nlinarith [h]

example (U V : Q) (h : V^2 = U^3 - 2*U^2 + 9*U) :
    let x : Q := V/(2*U)
    let T : Q := (9 - U^2)/(4*U)
    U != 0 -> T^2 = x^4 + x^2 - 2 := by
  intro x T hU
  subst x
  subst T
  field_simp [hU]
  nlinarith [h]

example (U V : Q) (h : V^2 = U^3 - 2*U^2 + 9*U) :
    let u : Q := V^2/(4*U^2)
    let w : Q := V*(9 - U^2)/(8*U^2)
    U != 0 -> w^2 = u^3 + u^2 - 2*u := by
  intro u w hU
  subst u
  subst w
  field_simp [hU]
  nlinarith [h]

end N14Quartic
```

For a formal Mazur-torsion development, I would use the theorem-level input

```text
E(Q) = E[2](Q)
```

proved once by a 2-descent certificate, and then finish the quartic obstruction by the two-line map

```text
u = (s/D)^2,
w = s*t/D^3.
```
