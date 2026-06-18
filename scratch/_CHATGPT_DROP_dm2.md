# ChatGPT Drop File (dm2)

## Question

For the curve

```text
E : y² = x³ + x² - x = x(x² + x - 1)
```

with the 2-isogeny

```text
φ : E  → E'    with kernel {(O), (0,0)}
φ̂ : E' → E    with kernel {(O), (0,0)},
```

we want to connect the explicit 2-isogeny descent computation

```text
Sel^φ    = {1, -1}
Sel^φ̂   = {1, 5}
```

to a Lean proof that rational points on `E` have integer `x`-coordinate, and ultimately to `rank(E)=0`.

The practical question is whether one must formalize abstract Galois cohomology

```text
H¹(Q, E[φ])
```

or whether a direct construction from rational points to explicit homogeneous spaces is enough.

## Short answer

Yes: for the rational-point/integrality part, you can avoid formalizing Galois cohomology entirely.

The minimal useful formal interface is not the abstract statement

```text
Sel^φ has size 2.
```

Instead, formalize the explicit descent map and the explicit covering curves directly:

```text
rational point P on E
        ↓ explicit algebra
squareclass d = x(P) in Q*/Q*²
        ↓ explicit algebra
rational point on the φ-cover C_d
        ↓ local obstruction / finite Selmer enumeration
allowed squareclass d ∈ {1, -1}
        ↓ denominator obstruction
x(P) is integral.
```

This is a completely concrete replacement for the cohomological connecting map.  It proves the same fact needed for point classification, but it does not require defining `H¹`, torsors, cocycles, or Galois actions.

## Important caveat

The statement

```text
Sel^φ = {1, -1}
```

by itself does **not** imply that every rational point has integral `x`-coordinate.

It only implies that the squareclass of `x(P)` is one of the allowed classes, namely `1` or `-1`, after the descent map is constructed.  A rational number can have squareclass `1` and still be nonintegral, for example

```text
x = (s/q)²,    q ≥ 2.
```

So after the Selmer image has been reduced to `{1,-1}`, one still needs a separate denominator argument.  In this curve, that denominator argument is exactly the quartic obstruction that has been appearing in the drop-file tasks.

## The direct descent map

For a curve with rational 2-torsion

```text
E : y² = x³ + a*x² + b*x = x(x² + a*x + b),
```

the explicit 2-isogeny descent map on `E(Q)` may be written concretely as

```text
α_E(O)       = 1,
α_E((0,0))   = b,
α_E((x,y))   = x mod Q*²     for x ≠ 0.
```

For the curve

```text
E : y² = x³ + x² - x,
```

we have `a = 1`, `b = -1`, so

```text
α_E((0,0)) = -1,
α_E((x,y)) = x mod Q*².
```

This map is the concrete version of the cohomological connecting map.  In Lean, it is enough to define it as a squareclass-valued function, or even more minimally as a predicate saying that `x(P)` has one of finitely many squareclasses.

## The explicit cover attached to a squareclass

Suppose `x = d*u²`, where `d` represents the squareclass of `x`.  Substitute into

```text
y² = x³ + x² - x.
```

Then

```text
y² = d*u² * (d²*u⁴ + d*u² - 1).
```

Writing `y = d*u*v` gives the homogeneous space

```text
C_d : d*v² = d²*u⁴ + d*u² - 1.
```

Thus the key direct-construction theorem is:

```text
point_to_cover_E :
  If P ∈ E(Q), P ≠ O, P ≠ (0,0), and α_E(P) = d,
  then C_d has a rational point.
```

This theorem is just algebra.  It does not need cohomology.

Conversely, for the parts of the descent where one needs exactness, one can also prove the reverse algebraic construction:

```text
cover_to_point_E :
  A rational point on C_d produces a rational point on E
  whose x-coordinate has squareclass d.
```

For proving integrality, usually only `point_to_cover_E` is needed.

## Minimal formal statements I would use

The cleanest Lean architecture is the following.

### 1. Define the concrete covers

For `d : ℚ` or for integer representatives `d : ℤ`, define:

```text
HasPointC(d) : Prop :=
  ∃ u v : ℚ, d*v² = d²*u⁴ + d*u² - 1
```

with the expected nontriviality conditions if needed, for example `u ≠ 0` and `d ≠ 0`.

If you are avoiding rational-heavy algebra, use integer-cleared versions of the same curves.

### 2. Prove the direct descent construction

A minimal theorem is:

```text
point_to_C_squareclass :
  ∀ P ∈ E(Q),
    P ≠ O → P ≠ (0,0) →
    ∀ d, x(P) = d*u² for some u : ℚ →
      HasPointC(d).
```

Equivalently, if you introduce a squareclass type:

```text
point_to_C_alpha :
  ∀ P ∈ E(Q), P ≠ O → P ≠ (0,0) → HasPointC(α_E(P)).
```

This is the direct replacement for the cohomological connecting map.

### 3. Encode the Selmer computation concretely

Instead of defining an abstract Selmer group, define a finite squareclass universe.  For this curve, after the usual local restrictions, the candidates are represented by

```text
{1, -1, 2, -2, 5, -5, 10, -10}.
```

Then prove:

```text
bad_C_empty :
  ∀ d ∈ {2, -2, 5, -5, 10, -10}, ¬ HasPointC(d).
```

Together with `point_to_C_alpha`, this yields:

```text
alpha_E_image_small :
  ∀ P ∈ E(Q), α_E(P) = 1 ∨ α_E(P) = -1.
```

This is the concrete meaning of

```text
Sel^φ = {1, -1}
```

for the purpose of rational points.

### 4. Add the denominator obstruction

Now take a rational point on `E` and write its `x`-coordinate in normalized form

```text
x = p / q²,
q ≥ 1,
gcd(p,q) = 1.
```

The descent result says `p` has squareclass `1` or `-1`.

#### Positive squareclass

If `p = s²`, then

```text
x = s² / q².
```

Writing `y = s*t/q³`, the curve equation becomes

```text
t² = s⁴ + s²*q² - q⁴.
```

So a nonintegral point with `q ≥ 2` gives an integer solution of

```text
s⁴ + s²*d² - d⁴ = t²,
gcd(s,d) = 1,
d = q ≥ 2.
```

This is the quartic obstruction already being formalized.

#### Negative squareclass

If `p = -s²`, then

```text
x = -s² / q².
```

The same substitution gives the companion quartic

```text
t² = -s⁴ + s²*q² + q⁴.
```

For a complete integrality theorem, this negative-squareclass denominator case should also be ruled out, unless it has already been eliminated by another descent branch or by a separate real/inequality argument.

The integral point `x = -1` corresponds to the allowed class `-1`, so the class `-1` itself cannot be discarded.  What must be discarded is the nonintegral case `x = -(s/q)²` with `q ≥ 2`.

Thus the minimal denominator theorem is something like:

```text
no_nonintegral_pm_square_x :
  If P ∈ E(Q), x(P) = ±(s/q)² with q ≥ 2 and gcd(s,q)=1,
  then False.
```

Or, split into two lemmas:

```text
no_positive_squareclass_denominator :
  ¬ ∃ s q t : ℤ,
    2 ≤ q ∧ gcd(s,q)=1 ∧ t² = s⁴ + s²*q² - q⁴.

no_negative_squareclass_denominator :
  ¬ ∃ s q t : ℤ,
    2 ≤ q ∧ gcd(s,q)=1 ∧ t² = -s⁴ + s²*q² + q⁴.
```

Then you get:

```text
rational_points_have_integer_x :
  ∀ P ∈ E(Q), ∃ n : ℤ, x(P) = n.
```

## About the proposed statement with `d ∈ {±2, ±5, ±10}`

The proposed direct statement was:

```text
If x = p/q² with q ≥ 2, then a bad cover C_d for some
 d ∈ {±2, ±5, ±10} has a nontrivial solution.
```

I would not make this the primary formal statement.

The reason is that a nonintegral rational number may still have squareclass `1` or `-1`, for example

```text
x = (s/q)²
or
x = -(s/q)².
```

Those cases do not naturally produce a bad squareclass `±2`, `±5`, or `±10`; they produce the allowed squareclasses `1` and `-1`.  They are killed only after using the denominator quartic obstruction.

So the robust structure is:

```text
nonintegral point
  → squareclass d has a cover C_d
  → d ∈ {1,-1} by local obstructions to the bad covers
  → denominator quartic contradiction for the allowed classes
```

rather than:

```text
nonintegral point
  → bad cover directly.
```

The latter might be true only after smuggling in the denominator contradiction, in which case it is less transparent and less modular.

## How this relates to rank zero

There are two possible routes.

### Route A: avoid cohomology and avoid the rank formula

For the goal `rank(E)=0`, the most Lean-friendly route may be:

1. Prove every rational point has integer `x`.
2. Use the existing integer-point theorem, for example the `Descent20a4.lean` style result, to classify integral points.
3. Conclude that `E(Q)` is finite.
4. Conclude that the Mordell-Weil rank is zero.

This avoids Galois cohomology entirely and also avoids formalizing the full isogeny Selmer exact sequence.

The final finite list should be the torsion points:

```text
O,
(0,0),
(1,1),
(1,-1),
(-1,1),
(-1,-1).
```

Once this finite list is proved, rank zero is immediate mathematically.  In Lean, the exact final statement depends on how `rank(E)` is represented, but the arithmetic content is just finiteness of `E(Q)`.

### Route B: use the 2-isogeny rank formula without H¹

If you specifically want the rank formula

```text
rank(E)
  = dim_F2 Sel^φ + dim_F2 Sel^φ̂
    - dim_F2 E[φ] - dim_F2 E'[φ̂],
```

then some exact-sequence formalization is unavoidable.  But it still does not need to mention Galois cohomology.

You can instead formalize the explicit finite quotients:

```text
E'(Q) / φ(E(Q))
E(Q)  / φ̂(E'(Q))
```

and prove explicit injections into your concrete Selmer sets via the direct descent maps.  Since each Selmer set has two elements and each quotient has a visible nontrivial kernel point, both quotients have dimension exactly `1`.  Then use the elementary isogeny exact sequence relating these two quotients to `E(Q)/2E(Q)`.

This is still more work than Route A, but it avoids `H¹`.

## Recommended minimal theorem package

For the current project, I would aim for the following theorem package.

### Concrete descent-image theorem

```text
alpha_E_image_subset_pm_one :
  ∀ P ∈ E(Q), α_E(P) = 1 ∨ α_E(P) = -1.
```

This theorem is proved from:

```text
point_to_C_alpha
bad_C_empty for d ∈ {±2, ±5, ±10}
```

No cohomology is needed.

### Denominator theorem

```text
pm_square_squareclass_has_integral_x :
  ∀ P ∈ E(Q),
    (α_E(P) = 1 ∨ α_E(P) = -1) →
    ∃ n : ℤ, x(P) = n.
```

This is where the quartic obstruction enters.

### Rational integrality theorem

```text
E_rational_x_integral :
  ∀ P ∈ E(Q), ∃ n : ℤ, x(P) = n.
```

### Integral classification theorem

Use the existing integer descent/squeeze theorem to prove:

```text
E_integral_points_classified :
  ∀ P ∈ E(Q), x(P) ∈ {-1, 0, 1}.
```

Then finish the point list by checking `y² = x³ + x² - x` for `x = -1,0,1`.

## Bottom line

You can absolutely formalize the descent as a direct construction

```text
rational point → explicit homogeneous-space solution
```

and avoid `H¹(Q,E[φ])` entirely for the rational-point and integrality theorem.

However, the minimal statement should not be phrased as “nonintegral point directly gives a bad class `±2, ±5, ±10`.”  The cleaner and more reliable statement is:

```text
Every rational point maps by the explicit descent map to an allowed squareclass.
The only allowed squareclasses are 1 and -1.
Nonintegral points in those allowed squareclasses are ruled out by the denominator quartic obstruction.
```

That is the smallest formal bridge from the concrete Selmer computation to “every rational point on `E` has integer `x`,” without formalizing cohomology.
