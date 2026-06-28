# Q2047 (dm3): Weil pairing coding convention and Miller formula

Date: 2026-06-28.

Question: For `P,Q ∈ E[m]`, is the computable shortcut

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P)
```

correct, and what convention should we standardize on for a nondegenerate alternating Weil pairing?

## Short answer

Yes, this is the standard **point-evaluation shortcut** for the Weil pairing **provided** the Miller functions are normalized in the usual way:

```text
div(f_{m,P}) = m[P] - [mP] - (m-1)[O],
```

so for `P ∈ E[m]`,

```text
div(f_{m,P}) = m[P] - m[O],
```

and `f_{m,P}` is **monic at O**.  With this normalization, the standard convention is

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P),
```

for generic `P,Q` where the displayed evaluations make sense, and extended to all of `E[m] × E[m]` by the divisor definition / alternating-bilinear continuation.

Do **not** treat the shortcut as the primary mathematical definition in Lean.  The primary definition should be the divisor/disjoint-support one.  The shortcut should be a theorem or a partial/generic computational formula under support hypotheses.

## The standard convention

The clean divisor convention is:

1. Choose degree-zero divisors

   ```text
   D_P ~ [P] - [O],
   D_Q ~ [Q] - [O]
   ```

   with disjoint support.

2. Choose functions

   ```text
   div(f_P) = m D_P,
   div(f_Q) = m D_Q.
   ```

3. Define

   ```text
   e_m(P,Q) = f_P(D_Q) / f_Q(D_P).
   ```

This is the canonical divisor definition.  It is independent of the choices and gives the nondegenerate alternating bilinear pairing

```text
E[m] × E[m] → μ_m.
```

For actual computation, one often uses Miller functions with

```text
div(f_{n,P}) = n[P] - [nP] - (n-1)[O]
```

and a monic-at-`O` normalization.  For `P,Q ∈ E[m]`, and away from zero/pole collisions, this divisor definition reduces to

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P).
```

The `(-1)^m` is not cosmetic.  It compensates for the shared pole at `O` when replacing divisor evaluation by direct point evaluation at `P` and `Q`.  Omitting it changes the convention and, for odd `m`, usually does not even land in `μ_m` with the same monic Miller normalization.

## Compatibility with the Q2027 Miller core

The Q2027 core used:

```text
ell(P,Q) = Y - y_P - λ(X - x_P),
v(R)     = X - x_R,
g(P,Q)  = ell(P,Q) / v(P+Q).
```

This is the right convention for the recurrence

```text
f_{a+b,P} = f_{a,P} * f_{b,P} * g(aP,bP),
```

with invariant

```text
div(f_{n,P}) = n[P] - [nP] - (n-1)[O].
```

Under the usual local parameter at `O`, the line and vertical functions are monic at `O`, so this recurrence keeps the Miller functions monic at `O`.  With exactly this `ell/v` convention, the Weil pairing shortcut should include the factor `(-1)^m`:

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P).
```

If instead the code uses the opposite line sign

```text
λ(X-x_P)+y_P-Y
```

or the inverse Miller quotient

```text
v(P+Q)/ell(P,Q),
```

then the resulting formula changes by a predictable sign and/or inversion.  So the safest Lean policy is:

```text
Fix Q2027 convention = ell/v, monic at O.
Then fix Weil convention = (-1)^m * fP(Q) / fQ(P).
```

## Domain caveat: direct evaluation is not total

The formula

```text
(-1)^m * f_{m,P}(Q) / f_{m,Q}(P)
```

is not a robust total definition on all pairs.

Problems:

* if `P = O` or `Q = O`, one should define `e_m(P,Q)=1`;
* if `P = Q`, the displayed expression has zero/zero behavior, but alternation says `e_m(P,P)=1`;
* if `Q` is a zero or pole of `f_{m,P}`, or `P` is a zero or pole of `f_{m,Q}`, direct evaluation fails;
* divisor definitions handle this by replacing `[P]-[O]` and `[Q]-[O]` with linearly equivalent divisors of disjoint support.

Therefore in Lean, define the total pairing abstractly or via displaced divisors.  Then prove the point-evaluation formula under generic hypotheses.

## Good Lean-facing split

### 1. Mathematical interface

Use the Q2012 abstract interface:

```lean
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  pairing : T → T → rootsOfUnity m K
  pairing_add_left  : ∀ P P' Q, pairing (P + P') Q = pairing P Q * pairing P' Q
  pairing_add_right : ∀ P Q Q', pairing P (Q + Q') = pairing P Q * pairing P Q'
  alternating : ∀ P, pairing P P = 1
  left_kernel  : ∀ P, (∀ Q, pairing P Q = 1) → P = 0
  right_kernel : ∀ Q, (∀ P, pairing P Q = 1) → Q = 0
```

This is what Mazur downstream proofs should depend on.

### 2. Miller computational layer

Introduce an evaluator only under a definedness predicate:

```lean
-- schematic names
structure MillerEvalOK (f : W.FunctionField) (P : W.Point) : Prop where
  noPole : True

noncomputable def evalFFAt
    (W : WeierstrassCurve.Affine K)
    (f : W.FunctionField) (P : W.Point)
    (_h : MillerEvalOK f P) : K :=
  sorry
```

Then state, not define blindly:

```lean
-- schematic theorem statement
 theorem weilPairing_eq_miller_generic
    {m : ℕ} {P Q : W.Point}
    (hP : m • P = 0) (hQ : m • Q = 0)
    (hPQ : P ≠ Q) (hPO : P ≠ 0) (hQO : Q ≠ 0)
    (h1 : MillerEvalOK (millerFunction W P m) Q)
    (h2 : MillerEvalOK (millerFunction W Q m) P) :
    rootValue (weilPairing W m P Q) =
      (-1 : K)^m *
        evalFFAt W (millerFunction W P m) Q h1 /
        evalFFAt W (millerFunction W Q m) P h2 := by
  sorry
```

For actual finite-field computation, one can define a separate partial/computable routine returning an `Option K`:

```lean
-- schematic
noncomputable def weilPairingMillerUnchecked
    (W : WeierstrassCurve.Affine K) (m : ℕ) (P Q : W.Point) : Option K :=
  if hPO : P = 0 then some 1
  else if hQO : Q = 0 then some 1
  else if hPQ : P = Q then some 1
  else
    -- evaluate f_{m,P}(Q), f_{m,Q}(P), return the signed ratio if both are defined
    none
```

But this unchecked computational function should not be the foundational pairing used in proofs.

## Correctness tests for the chosen convention

Once an evaluator exists, the convention should be tested against these properties:

```text
e_m(P,O) = 1,
e_m(O,Q) = 1,
e_m(P,P) = 1,
e_m(P,Q) * e_m(Q,P) = 1,
e_m(aP,bQ) = e_m(P,Q)^(a*b),
e_m(P,Q)^m = 1,
```

and if `P,Q` are a `ZMod m` basis of `E[m]`, then

```text
e_m(P,Q)
```

should be a primitive `m`-th root of unity.  In the Q2012 interface this is exactly the `IsPrimitiveRoot`/nondegeneracy condition.

## Final decision for this project

Use this convention:

```text
line:      ell(P,Q) = Y - y_P - λ(X - x_P)
vertical:  v(R)     = X - x_R
Miller:    g(P,Q)  = ell(P,Q) / v(P+Q)
Invariant: div(f_{n,P}) = n[P] - [nP] - (n-1)[O]
Normalize: f_{n,P} monic at O
Weil:      e_m(P,Q) = (-1)^m f_{m,P}(Q) / f_{m,Q}(P)
```

with the warning that the final line is a generic-support computation theorem, not the primary total definition.

## References checked

* Andreas Enge, *Bilinear pairings on elliptic curves*, arXiv:1301.5520.  The abstract explicitly says the paper states the three definitions of the Weil pairing correctly and proves their equivalence using Weil reciprocity.
* The same paper states the standard divisor and function-field setup for elliptic-curve pairings, including the coordinate ring/function field, vertical line `v_R = X-x_R`, line function `ell_{P,Q} = (Y-y_P)-lambda_{P,Q}(X-x_P)`, the divisor formula for `ell/v`, monic-at-`O` normalization, and Weil-pairing properties.
* The usual divisor definition is also summarized in public references as `f_P(D_Q)/f_Q(D_P)` after moving divisors to disjoint support.
