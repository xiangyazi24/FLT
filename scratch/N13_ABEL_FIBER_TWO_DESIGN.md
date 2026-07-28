# N13 characteristic-two Abel fibres: structural design

## 1. Verdict

The finite fibre calculation does not need a nineteen-element Jacobian table.
Over `F₂`, the six points of the good generalized model have the structural
form

```text
C(F₂) ≃ P¹(F₂) × F₂.
```

The second factor is the two-sheeted hyperelliptic fibre.  The
hyperelliptic involution adds one to that factor.  Hence there are exactly
three invariant degree-two divisors, one over each point of `P¹(F₂)`.

For a genus-two curve, the degree-two Abel map has the exact equality
criterion

```text
AJ(D) = AJ(E)
  ↔ D = E
    ∨ (D and E are both fibres of the hyperelliptic map).
```

This immediately gives one fibre of size three and all other fibres of size
one.  The proof is Riemann--Roch/linear-system structure, not finite
enumeration.

An axiom-free Lean prototype now verifies the whole finite combinatorial
argument:

```text
scratch/N13AbelFiberTwoPrototype.lean
```

It compiles with

```bash
lake env lean scratch/N13AbelFiberTwoPrototype.lean
```

The prototype deliberately does **not** call its quotient the geometric
Jacobian.  The remaining task is to prove that the actual special-fibre
Picard target realizes the displayed equality criterion.

## 2. The six points as three free involution orbits

Write

```text
h(x) = x³ + x + 1,
r(x) = x⁵ + x⁴,
C : y² + h(x)y = r(x).
```

`N13GoodModelTwo.affineEquation_iff_fixed` proves that every affine point
over `F₂` or `F₄` has both coordinates fixed by Frobenius.  Thus over `F₂`
the affine points are exactly

```text
(x,y),  x ∈ F₂, y ∈ F₂.
```

The two points at infinity are similarly parametrized by `v ∈ F₂`.
Consequently the prototype constructs an explicit equivalence

```lean
curvePointEquiv :
  N13GoodModelTwo.CompletedPoint F₂ ≃ (F₂ ⊕ Unit) × F₂
```

where `F₂ ⊕ Unit` is the three-point hyperelliptic base.

For the generalized equation, conjugation is

```text
(x,y) ↦ (x, -h(x)-y).
```

In characteristic two this is `(x,y) ↦ (x,y+h(x))`.  On all four affine
`F₂`-points, `h(x)=1`; on the infinity chart the same involution is
`v ↦ v+1`.  In the product coordinates it is simply

```lean
hyperelliptic P =
  curvePointEquiv.symm
    ((curvePointEquiv P).1, (curvePointEquiv P).2 + 1).
```

The prototype proves:

```lean
hyperelliptic_involutive
hyperelliptic_ne_self
baseProjection_hyperelliptic
```

For each base point `b`, define

```lean
canonicalDivisor b =
  s(curvePointEquiv.symm (b,0), curvePointEquiv.symm (b,1)).
```

Then:

```lean
point_hyperelliptic_eq_canonical
canonicalDivisor_injective
basePoint_card : Nat.card BasePoint = 3
```

prove structurally that the canonical divisors are exactly the three free
involution orbits.

## 3. The genus-two fibre theorem

Let `K_C` be a canonical divisor.  For an effective divisor `D` of degree
two on a genus-two curve, Riemann--Roch gives

```text
l(D) = deg(D) + 1 - g + l(K_C-D)
     = 1 + l(K_C-D).
```

The divisor `K_C-D` has degree zero.

* If `D` is not linearly equivalent to `K_C`, then
  `l(K_C-D)=0`, so `l(D)=1`.  Its complete linear system has only one
  effective divisor.  The Abel fibre is therefore a singleton.
* If `D` is linearly equivalent to `K_C`, then `l(D)=2`.  Its effective
  divisors are the points of
  `P(H⁰(C,K_C)) = P¹`.  Over `F₂`, this projective line has exactly three
  points.

For this model one can see the three canonical sections directly.  Taking
the fibre above infinity as `K_C`, the two-dimensional section space is
spanned by `1` and `x`.  Its three `F₂`-lines are represented by

```text
1, x, x+1,
```

whose effective divisors are respectively the fibres above infinity,
zero, and one.

The same Riemann--Roch equation also gives surjectivity

```text
Sym²(C)(F₂) → Pic²(C)(F₂):
```

every degree-two rational divisor class has a nonzero rational section.

Thus the exact semantic input needed by `N13SymmetricSquareTwo` is:

```lean
structure GeometricAbelCriterion (J : Type*) where
  abel : EffectiveDivisorTwo → J
  canonicalClass : J
  canonical_eq :
    ∀ b, abel (canonicalDivisor b) = canonicalClass
  surjective : Function.Surjective abel
  eq_iff :
    ∀ D E,
      abel D = abel E ↔
        D = E ∨ IsCanonical D ∧ IsCanonical E
```

The prototype proves, without any assumptions beyond this interface, that it
produces `N13SymmetricSquareTwo.AbelFiberData J`.

## 4. Important source-type seam: `Sym²(C)(F₂)` is not generally
`Sym2 (C(F₂))`

The formal type currently used by `N13SymmetricSquareTwo` is

```lean
Sym2 (N13GoodModelTwo.CompletedPoint F₂).
```

In general this omits rational degree-two divisors supported on a
Frobenius-conjugate pair of non-rational points.  Such a pair is an
`F₂`-point of the scheme `Sym²(C)` but is not an unordered pair of
`C(F₂)`-points.

For N13 the omission is harmless, but it needs a theorem:

* a non-split rational effective divisor of degree two would give a
  Frobenius orbit of size two in `C(F₄)`;
* `N13GoodModelTwo.affineEquation_iff_fixed` and its infinity analogue show
  that every `F₄`-point is already Frobenius-fixed;
* hence there are no degree-two closed points, and every rational effective
  divisor of degree two splits over `F₂`.

Mathlib currently has no ready-made closed-point/symmetric-power bridge for
this custom curve type.  A small project-local type for rational effective
degree-two divisors should therefore be introduced, together with an
equivalence to `Sym2 CurvePoint` in this fixed case.  Merely citing the two
equal point counts is mathematically suggestive but is not yet the formal
identification.

## 5. What the prototype proves

The prototype defines

```lean
AbelRel D E :=
  D = E ∨ IsCanonical D ∧ IsCanonical E
```

and proves that it is an equivalence relation.  It then forms the quotient

```lean
PicTwoSetModel := Quotient abelSetoid.
```

For the quotient map `abel` it proves:

```lean
canonical_fiber_card :
  Nat.card {D // abel D = canonicalClass} = 3

regular_fiber_card :
  c ≠ canonicalClass →
  Nat.card {D // abel D = c} = 1

picTwoSetModel_card :
  Nat.card PicTwoSetModel = 19
```

This is a useful formal model of the degree-two linear-system quotient, and
it contains no `sorry`, `axiom`, `native_decide`, or representative table.

It is not yet a replacement for the special-fibre Jacobian:

* it has no geometrically justified group law;
* no reduction homomorphism from the rational Jacobian lands in it;
* its equivalence relation has been defined to be the desired theorem,
  rather than derived from principal divisors.

Transporting an arbitrary cyclic group law onto this nineteen-element set
would not repair those semantic gaps.

## 6. Mathlib API audit

### 6.1 Projective divisors and Picard varieties

There is no usable Mathlib API for the needed theorem.

* `Mathlib.AlgebraicGeometry.FunctionField` constructs function fields of
  integral schemes through germs.  It does not define closed-point
  valuations, Weil divisors, principal divisors, divisor degree, complete
  linear systems, or Riemann--Roch.
* `Mathlib.NumberTheory.FunctionField` defines a function field as a finite
  extension of `F(X)` and defines its affine ring of integers as an integral
  closure of `F[X]`.  It supplies Dedekind/class-group infrastructure, not
  the Picard group of a smooth projective curve with its degree map.
* `Mathlib.RingTheory.PicardGroup` defines `CommRing.Pic R`, the Picard group
  of the affine scheme `Spec R` via invertible modules.  Its
  `ClassGroup.equivPic` is an affine-ring result.  It is not
  `Pic⁰(C)(F₂)` or `Pic²(C)(F₂)`.
* `Mathlib.Analysis.Meromorphic.Divisor` concerns analytic meromorphic
  functions and is unrelated to this algebraic curve over a finite field.

In particular, there is no general theorem in the current dependency tree
from the genus-two Abel map to the asserted fibre sizes.

### 6.2 What can be reused from the project

`SexticOrientedPic` has the correct **architecture**:

```text
invertible fractional ideals
× one integer orientation
/ principal oriented ideals.
```

The following parts are conceptually reusable after factoring them away
from the completed-square model:

* `InvFrac`, `OrientedFrac`, and the quotient-group construction;
* `principalOriented` and `orientedMk`;
* the quotient equality proof used by `classOf_eq_iff`;
* the `AdjoinRoot` two-term basis/evaluation-kernel pattern;
* group transport once a genuine normal-form equivalence is proved.

It cannot be instantiated directly at `F₂`.

* `SexticMumford.Model` requires `two_ne_zero`.
* Its equation is hard-coded as `Y²=f(X)`.
* Its conjugation is `Y ↦ -Y`.
* `SexticMumfordUnit` uses the smoothness tuple
  `(u,2v,(f-v²)/u)`.
* `N13Infinity` constructs the branches with the binomial series of exponent
  `1/2`.

All of those are invalid for the characteristic-two generalized model.

## 7. Recommended genuine special-fibre Picard model

The shortest semantically correct project-local route is a generalized
oriented fractional-ideal model.

### 7.1 Generalized affine coordinate ring

Define

```text
A = F₂[X,Y] / (Y² + h(X)Y - r(X)),
F = Frac(A).
```

Using `AdjoinRoot`, take the outer polynomial

```lean
Y^2 + C h * Y - C r.
```

It is monic quadratic.  Its irreducibility can be proved without a search
table.  A polynomial root `q` would satisfy

```text
q² + hq = r.
```

Degree forces `deg q ≤ 3`.  The transformation `q ↦ q+h` preserves this
equation, so a degree-three root reduces to degree at most two.  Writing
`q=X²+aX+b` then gives a contradiction already in the `X²` coefficient
after the leading coefficients are forced.  This is a fixed short
coefficient proof, not enumeration.

### 7.2 Generalized conjugation and point ideals

Conjugation is

```text
Y ↦ -h-Y.
```

For Mumford data use

```text
u ∣ r-v²-hv,
I(u,v) = (u,Y-v).
```

The conjugate ideal is `I(u,-h-v)`, and the key product is

```text
I(u,v) I(u,-h-v) = (u).
```

The smoothness/Bezout tuple becomes

```text
(u, 2v+h, (r-v²-hv)/u),
```

which remains meaningful in characteristic two because `2v+h=h`.
For the six rational point ideals, `h(a)=1`, so invertibility is especially
short: the middle entry is already a unit modulo `X-a`.

The existing `SexticMumfordIdeal` evaluation-kernel proof adapts almost
verbatim after changing the root relation.

### 7.3 Infinity orientation

The affine chart omits both infinity points, so an orientation is still
needed.  On the infinity chart the equation is

```text
v² + (1+t²+t³)v = t+t².
```

At `t=0` the two roots are `v=0,1`, and the derivative in `v` is one.
Thus each root has a unique formal-power-series lift.  These lifts give the
two Laurent embeddings and the integer order at the chosen infinity.

This part must be new.  The characteristic-zero binomial-square-root code
cannot be reduced modulo two.  A fixed coefficient recursion or the
`X`-adic Henselian API is the appropriate construction.

### 7.4 Abel map

Choose one infinity point `O`.  Send a point `P` to the oriented ideal class
of `P-O`.  Define the degree-two map by the universal property of `Sym2`:

```lean
abel₂ :=
  Sym2.lift ⟨fun P Q => pointClass P + pointClass Q,
    add_comm⟩.
```

The product identity above proves that

```text
[P-O] + [ι(P)-O]
```

is independent of `P`; this is the canonical class.

### 7.5 Exact equality criterion, without a table

Prove one fixed low-degree linear-system theorem:

```lean
abel₂ D = abel₂ E ↔ AbelRel D E.
```

There are two acceptable structural proofs.

1. Build the minimal degree-two Riemann--Roch lemma for this function field.
   Show that the canonical section space is exactly `span{1,x}` and that a
   noncanonical degree-two divisor has a one-dimensional section space.
2. Use the oriented ideal equality to obtain a principal function, write it
   in the two-term basis `a(x)+b(x)y`, and use the two infinity orders plus
   the point-ideal constraints to show that a nonconstant function with at
   most two poles is a fractional linear function of `x`.  Its zero and pole
   divisors are therefore hyperelliptic fibres.

The second route is closer to the already successful structural
`N13FactorRigidity` argument and avoids developing general algebraic
geometry.

Surjectivity of `abel₂` is the remaining normal-form statement.  For this
fixed genus-two group it can be proved simultaneously: every oriented
invertible ideal class admits an effective representative of degree at most
two.  This is the fixed-function-field form of Riemann--Roch.

## 8. Implementation order

1. Promote the six-point product decomposition, involution, and canonical
   divisors from the prototype.
2. Introduce a rational effective-degree-two type and prove that the absence
   of nontrivial `F₄/F₂` point orbits identifies it with `Sym2 CurvePoint`.
3. Factor the model-independent oriented fractional-ideal quotient out of
   `SexticOrientedPic`.
4. Implement the generalized characteristic-two coordinate ring,
   conjugation, point ideals, and their explicit inverses.
5. Construct the chosen infinity order from the formal branch with
   constant term zero.
6. Define the genuine point-class and degree-two Abel maps.
7. Prove the fixed low-pole/Riemann--Roch criterion and surjectivity.
8. Instantiate `GeometricAbelCriterion`, then obtain
   `N13SymmetricSquareTwo.AbelFiberData` automatically.

The finite counting layer is already complete.  The irreducible mathematical
seam is now sharply isolated: generalized characteristic-two oriented
Picard semantics plus one fixed low-degree linear-system theorem.
