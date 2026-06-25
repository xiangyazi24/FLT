# Q439 / dm2 — Round 4 stress test for `W.formalGroup`

Construction under test:

```text
u(t) iteration → P(t) representative → addXYZ → normalize → F(t₁,t₂).
```

The key distinction is **raw projective addition formula** versus **normalized formal-neighborhood addition**.  The former may be polynomial over a `CommRing`; the latter is what is needed to define a `FormalGroup` power series.

## (a) Associativity

Do not assume associativity follows merely because `addXYZ` is a polynomial formula over `CommRing`.

The safe statement is:

```text
If the normalized formal addition really represents the Weierstrass group law,
then associativity follows from the elliptic-curve group law.
```

But if the available curve group law theorem is only over fields, that theorem cannot be applied directly to

```text
MvPowerSeries σ K
```

because this ring is not a field.  The way around this is a **generic-field → polynomial identity → specialization** argument.

Recommended associativity route:

1. Work over the universal coefficient ring with variables

   ```text
   a₁,a₂,a₃,a₄,a₆,t₁,t₂,t₃.
   ```

2. Construct the normalized formal sums on both sides:

   ```text
   L = F(F(t₁,t₂),t₃),
   R = F(t₁,F(t₂,t₃)).
   ```

3. Over the fraction field of the universal polynomial/power-series coefficient ring, interpret the same formulas as the usual elliptic-curve group law.  There, associativity is available.

4. Convert the resulting equality into cleared polynomial identities for the normalized local parameter.  Since the denominators being inverted in the formal chart have constant coefficient `±1`, they are units; no discriminant hypothesis is needed for the formal neighborhood calculation.

5. Specialize the polynomial identities back to any coefficient ring `K` and use `PowerSeries.ext` / `MvPowerSeries.ext`.

So associativity is not a pure consequence of `addXYZ : CommRing → ...` unless one has already proved the relevant universal associator polynomial identities.  In Lean terms, I would not try to prove

```lean
F.subst ![F.subst ![X,Y], Z] = F.subst ![X, F.subst ![Y,Z]]
```

by expanding the raw formulas.  I would prove a named theorem:

```lean
formalAdd_assoc_universal
```

using a generic-field proof plus clearing denominators, and then use it as the `assoc` field of `FormalGroup`.

A weaker but practical intermediate milestone is to prove associativity modulo total degree `N` for small `N` by CAS/reflection.  That helps debug the normalization, but it is not enough for the final `FormalGroup` instance.

## (b) Convergence of `u(t)` iteration

There is no analytic convergence issue.  This is formal power series, so the correct proof is coefficientwise.

For

```text
u = 1 + a₁t u + a₂t²u + a₃t³u² + a₄t⁴u² + a₆t⁶u³,
```

the coefficient of `t^n` on the right depends only on coefficients of `u` in degrees `< n`.  Therefore the recursion is triangular.

I would not depend on a general fixed-point theorem in Mathlib.  Even if one exists, using it will likely introduce topological-completion overhead that is unnecessary here.

Recommended Lean construction:

```text
1. Define coeff_u : ℕ → K by well-founded recursion.
2. Define u : PowerSeries K via PowerSeries.mk coeff_u.
3. Prove coeff_u 0 = 1.
4. Prove the defining equation by coefficient extensionality.
5. Prove uniqueness by induction on coefficients.
```

Key lemmas:

```lean
lemma u_coeff_zero : coeff K 0 W.u = 1
lemma u_eq :
  W.u = 1 + C a₁ * X * W.u
          + C a₂ * X^2 * W.u
          + C a₃ * X^3 * W.u^2
          + C a₄ * X^4 * W.u^2
          + C a₆ * X^6 * W.u^3
lemma u_unique :
  v = 1 + C a₁ * X * v + ... → v = W.u
lemma u_isUnit : IsUnit W.u
```

The iteration

```text
u₀ = 0,
ν_{n+1} = 1 + a₁tν_n + ...
```

is useful as a proof/debug device:

```text
ν_n agrees with ν through degree < n.
```

But the final definition should probably be the recursive coefficient definition, not a limit of iterates.  This is the shortest Lean path.

## (c) Normalization and the `Y`-coordinate

This is the most dangerous point.

With the pole-free Jacobian representative

```text
P(t) = [u(t), -u(t)^2, t u(t)]
```

we have

```text
P(0) = [1,-1,0],
```

which is a valid infinity representative in Jacobian-style coordinates, with local parameter

```text
t = -X Z / Y.
```

However, the raw `addXYZ(P(t₁),P(t₂))` formula may still be an exceptional/projectively scaled representative at `(t₁,t₂)=(0,0)`.  In particular, for generic secant-style addition formulas, the raw coordinates often acquire common vanishing factors at `O+O`.  Then the raw `Y` coordinate can have constant term `0`, so it is **not** invertible as a power series.

Therefore the construction must not be:

```text
F = -X_raw * Z_raw / Y_raw
```

unless one first proves `Y_raw` is a unit.  The stress-test answer is: **do not assume this.**  The raw `addXYZ` output may be undefined for formal-group normalization even though it is a correct projective formula generically.

What is needed is a normalized addition theorem of the form:

```text
addXYZ(P(t₁),P(t₂))  ~  [U₁₂, -U₁₂², F(t₁,t₂)·U₁₂]
```

where

```text
U₁₂(0,0) = 1.
```

Then the local parameter is read from the normalized representative:

```text
F(t₁,t₂) = -X_norm Z_norm / Y_norm = F(t₁,t₂).
```

Equivalent acceptable routes:

1. **Normalize raw coordinates explicitly.**  Prove the raw output has a known common factor/scaling and divide it out to get a coordinate with `Y_norm(0,0) = -1` or `1`.

2. **Define `F` by a pre-cancelled formula.**  Use the standard formal-group rational expression where the denominator has constant term `1`.  This is usually how the formal group law is written in texts.

3. **Use uniqueness of the local point.**  Define `F` as the unique power series with constant term `0` such that the normalized point `P(F)` is projectively equivalent to `addXYZ(P(t₁),P(t₂))`.  This avoids naming all cancelled factors, but it requires a strong uniqueness lemma for the chart.

The CAS computation from the previous round is a good sanity check:

```text
F(t₁,t₂) = t₁ + t₂ - a₁t₁t₂ - a₂t₁t₂(t₁+t₂) + O(deg 4),
```

so the normalized denominator must be a unit.  If raw `addXYZ` gives `Y(0,0)=0`, that is not a contradiction; it just means raw `addXYZ` has not yet been normalized.

## (d) Single biggest derail risk

The single biggest risk is **normalization of `addXYZ` at `(O,O)`**, not the `u(t)` iteration.

Reason:

* The `u(t)` recursion is triangular and should be routine.
* The linear coefficients of `F` are easy once a normalized `F` exists.
* Associativity can plausibly be imported from a universal generic-field identity after clearing denominators.
* But if raw `addXYZ(P(t₁),P(t₂))` has a vanishing `Y` coordinate and no clean proven cancellation/normalization lemma, then `F` cannot even be defined as a `PowerSeries` by division.

So the next design checkpoint should be a concrete CAS/Lean lemma:

```text
There exist power series U₁₂ and F₁₂ with U₁₂(0,0)=1 and F₁₂(0,0)=0 such that
addXYZ(P(t₁),P(t₂)) is projectively equivalent to [U₁₂, -U₁₂², F₁₂ U₁₂],
and F₁₂ = t₁ + t₂ + O(deg≥2).
```

If this normalization lemma is landed, the rest of the formal group construction becomes a controlled API/associativity problem.  If it is not landed, the construction can fail at the definition stage.

## Practical recommendation for Round 5

Before committing to the full `FormalGroup` instance, run one decisive CAS test against Mathlib's exact `addXYZ` formulas:

```text
Input:  P₁ = [u(t₁), -u(t₁)^2, t₁u(t₁)]
        P₂ = [u(t₂), -u(t₂)^2, t₂u(t₂)]
Output: raw addXYZ(P₁,P₂)
Task:   factor common powers / common factors through total degree 4 or 5
Check:  normalized output has Y constant ±1 and t = -XZ/Y = t₁+t₂-a₁t₁t₂+...
```

This directly answers whether the proposed `addXYZ → normalize → F` route is viable with the exact formulas available in the repository.
