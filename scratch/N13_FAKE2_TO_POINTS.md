# N13 fake-2 descent: structural route to rational points

Design audit, 2026-07-27.

## Logical output of the descent

A trivial fake-2 Selmer computation should give

```text
J(Q) / 2 J(Q) = 0,
```

or, in the concrete Picard model,

```text
forall D, exists Q, D = 2 Q.
```

This does not by itself prove that `J(Q)` is finite.  An abstract nonzero
uniquely 2-divisible group is a counterexample.  The missing closure is a
2-adic separated reduction kernel, not Mordell--Weil finite generation.

The residue characteristic must match the descent prime.  A 3-adic formal
kernel cannot force an infinitely 2-divisible element to vanish:
multiplication by two is a 3-adic unit.

## Minimal structural chain

Let `G` be `N13MumfordAbelJacobi.ConcretePic Q`.
`N13MumfordAbelJacobi.abelJacobi_injective` is already unconditional on this
point-sized Picard model.

The remaining packages should have the following interfaces.

### 1. Fake Kummer soundness and triviality

```text
two_surjective : forall D : G, exists Q : G, D = 2 Q
```

The formal quotient and the collapse of the apparent second survivor are now
available in `FakeSquareClass.lean` and `N13SexticSquareclass.lean`.
Still missing are the actual Kummer map, its kernel modulo `2G`, completeness
of the global envelope, and the local-image theorems.

### 2. Good reduction at two

Construct the reduction homomorphism

```text
red2 : G -> J2(F2)
```

and prove

```text
red2_exponent : forall r, 19 r = 0
ker2_separated : NSeparated red2.ker 2
```

The second statement should come from a strict formal-parameter filtration
for multiplication by two.  This is the pattern already abstracted by
`N18RouteC_Separated.StrictNSmulFiltration`.

### 3. Exponent 19 without finite generation

Instantiate
`N18RouteC.Separated.annihilated_of_weakDescent_and_separated` with

```text
loc = id, n = 2, a = 1, b = 19.
```

The weak-descent error is zero and hence killed by one.  The result is

```text
forall D : G, 19 D = 0.
```

No theorem asserting that `J(Q)` is finite is needed.

### 4. Exact group and rational points

Multiplication by 19 is an automorphism on the 2-adic formal kernel.  Hence
the reduction map is injective on the exponent-19 group from the previous
step.  If

```text
#J2(F2) = 19
```

and the known cuspidal class has exact order 19, then `G` is cyclic of order
19 without enumerating 19 Mumford representatives.

Make reduction commute with Abel--Jacobi.  The six rational cusps reduce
bijectively to the six special-fibre points.  If a rational point and a cusp
have the same reduction, reduction injectivity gives equality of their
Abel--Jacobi classes, and the proved direct Abel--Jacobi injection gives
equality of the points.

## Good generalized model

Do not reduce the completed-square even sextic modulo two.  That plane model
is singular there.  Use

```text
y^2 + (x^3+x+1)y = x^5+x^4.
```

Its weighted projective equation is

```text
Y^2 + (X^3+X Z^2+Z^3)Y = X^5 Z+X^4 Z^2.
```

On the affine chart `Z=1` this is the displayed generalized equation.  On
the chart `X=1`, with `t=Z/X` and `v=Y/X^3`, it is

```text
v^2 + (1+t^2+t^3)v = t+t^2.
```

At infinity `t=0`, so `v^2+v=0`; there are two infinity points.  In
characteristic two the derivative with respect to the second coordinate is
one at every point on both charts.  This is the structural smoothness check.

Over `F2`, Frobenius makes the affine equation `y^2+y=0` for both possible
values of `x`, giving four affine points and two infinity points.

Over `F4`, every element satisfies `x^4=x`.  Any solution forces
`x^2=x` and `y^2=y`: if instead `x^2+x=1`, then `x^3=1`, and after scaling
`y` the equation would say `t^2+t=x`.  But every Artin--Schreier value
`t^2+t` is fixed by squaring, whereas this `x` is not.  Thus the same six
points occur over `F4`, without enumerating field elements.

The resulting genus-two trace data are

```text
N1 = 6, N2 = 6,
P2(T) = 1 + 3T + 5T^2 + 6T^3 + 4T^4,
P2(1) = 19.
```

Mathlib currently has no ready theorem connecting these point counts to the
Jacobian cardinality; that standard genus-two zeta interface remains a
separate geometry seam.

## Recommended file layering

```text
N13GoodModelTwo
  generalized model, completion-square bridge, smooth F2 charts,
  six F2/F4 points

N13WeilTwo
  trace identities and P2(1)=19

N13FakeTwoDescent
  Kummer kernel and local-image theorems
  -> two_surjective

N13TwoAdicKernel
  reduction, Abel--Jacobi compatibility, strict [2] filtration
  -> exponent 19 and injective reduction

N13RationalPointsByReduction
  six cusp reductions plus Abel--Jacobi injection
  -> C13Sextic_affine_x_is_cuspidal
```
