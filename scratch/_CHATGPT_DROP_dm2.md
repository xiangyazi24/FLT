# Q371 / dm2 — division polynomials, local parameters, and the multiplier `(n : K)`

## Verdict

Not in the literal form

```text
coeffε (t ([n] Pε)) = (n : K) * coeffε (t Pε)
```

with the same unshifted affine rational function `t = -x / y` on both sides.
That statement is false at a generic affine point, and at a smooth `2`-torsion point it is not even the right first-order test: a deformation

```text
Pε = (x + ε, y + ε s)
```

with `dx = 1` is not tangent to the curve when `y = 0`.

What *can* be proved directly from the division-polynomial/projective formula, without importing a `FormalGroup` API, is the corrected invariant-differential statement

```text
[n]^* η = (n : K) • η,
```

where, for a short Weierstrass curve `y^2 = x^3 + A x + B`,

```text
η = dx / (2 y).
```

Then the desired coefficient `n` follows after using a local parameter whose differential is normalized by `η`.  At `O`, the projective local parameter

```text
t = -X Z / Y
```

has `dt / η = 1` at `O`.  At a nonzero `n`-torsion point `P`, the source parameter must be translated/normalized, e.g. morally

```text
τ_P(Q) = t(Q - P),
```

not the same global function `-x/y` evaluated at `Q`.

So the answer is:

* **Yes**, a proof avoiding `FormalGroup` is possible if it proves the rational differential identity coming from the division polynomials and then does a small local-chart computation at `O`.
* **No**, the coefficient cannot be obtained by differentiating the affine `x`-chart formula at a generic point and specializing through `ψ_n(P) = 0`; the affine `x`-chart has a pole at `O`, and the unshifted `t = -x/y` is not a normalized local parameter at a general point.

## Why the literal identity is wrong

Let `t = -x/y`.  For any morphism `[n]`,

```text
d(t ∘ [n])_P = (dt/η)_[n]P · ([n]^* η)_P
             = (n : K) · (dt/η)_[n]P · η_P.
```

On the other hand,

```text
(n : K) · dt_P = (n : K) · (dt/η)_P · η_P.
```

Thus the literal identity `d(t ∘ [n]) = n dt` would require

```text
(dt/η)_[n]P = (dt/η)_P,
```

which is not true in general.  The true globally meaningful statement is about the invariant differential `η`, not about the rational function `t` away from the chart where it is a normalized local parameter.

For a short Weierstrass curve,

```text
t = -x/y,
η = dx/(2y),
```

and along the curve

```text
dt/η = x(3x^2 + A)/y^2 - 2.
```

This is visibly not constant.

## Concrete generic counterexample for `n = 2`

Take

```text
E : y^2 = x^3 + x + 1
P = (0, 1).
```

The tangent condition for a dual deformation with `dx = 1` is

```text
2 y s = 3 x^2 + A,
```

so here `s = 1/2`, and

```text
Pε = (ε, 1 + ε/2)
```

is curve-valued modulo `ε^2`.

Using the usual doubling formulas

```text
λ  = (3x^2 + A)/(2y),
x₂ = λ^2 - 2x,
y₂ = λ(x - x₂) - y,
t₂ = -x₂/y₂,
```

one gets

```text
d/dε [ t([2]Pε) ] at ε = 0 = -143/81,
d/dε [ t(Pε)   ] at ε = 0 = -1.
```

Therefore

```text
d/dε [ t([2]Pε) ] - 2 d/dε [ t(Pε) ] = 19/81 ≠ 0.
```

So `d(t ∘ [2]) = 2 dt` is false even at an ordinary affine point where the deformation is perfectly valid.

## The `2`-torsion CAS test, corrected

Let

```text
E : y^2 = f(x) = x^3 + A x + B
T = (r, 0)
```

be a smooth `2`-torsion point, so

```text
f(r) = 0,
D := f'(r) = 3r^2 + A ≠ 0.
```

The proposed deformation

```text
(r + ε, ε s)
```

with `dx = 1` is not tangent to `E`, because the first-order tangent equation gives

```text
2y dy = f'(x) dx,
```

hence at `T`

```text
0 = D,
```

contradicting smoothness.  Thus there is no curve-valued dual-number deformation of this form at a smooth `2`-torsion point.

Use the correct local branch parameter `u = y`.  Solving the curve equation gives

```text
x = r + u^2/D - 3r u^4/D^3 + O(u^6).
```

Now apply the doubling formula.  Since

```text
λ = (3x^2 + A)/(2u) = D/(2u) + O(u),
```

we get

```text
x([2](x,u)) = D^2/(4u^2) + O(1),
y([2](x,u)) = -D^3/(8u^3) + O(u^-1).
```

Therefore the target projective local parameter at `O` satisfies

```text
t([2](x,u)) = -x([2](x,u)) / y([2](x,u))
            = 2u/D + O(u^3).
```

Meanwhile

```text
η = dx/(2y) = du/D + O(u^2) du.
```

So if the normalized source local parameter `τ_T` is chosen with

```text
dτ_T = η at T,
```

then

```text
τ_T = u/D + O(u^3),
```

and the corrected coefficient statement is

```text
t([2]Q) = 2 τ_T(Q) + higher-order terms.
```

This is the concrete `n = 2` verification that the tangent multiplier is `2`.  It verifies the translated/normalized local-parameter statement, not the literal statement with `t(Pε) = -x(Pε)/y(Pε)`.

## What a direct division-polynomial proof should prove

For a short Weierstrass model, write the multiplication formulas in the usual affine form on the generic open set:

```text
x_n = φ_n / ψ_n^2,
y_n = ω_n / ψ_n^3.
```

Let `δ` be the derivation on the function field determined by

```text
δ x = 1,
δ y = (3x^2 + A)/(2y).
```

The direct algebraic target is

```text
δ x_n / (2 y_n) = (n : K) / (2 y),
```

or equivalently, after clearing denominators,

```text
y · δ(x_n) = (n : K) · y_n.
```

Substituting `x_n = φ_n / ψ_n^2` and `y_n = ω_n / ψ_n^3` gives the polynomial/rational identity

```text
y · (ψ_n · δφ_n - 2 φ_n · δψ_n) = (n : K) · ω_n.
```

Depending on the exact convention for `ω_n` and the projective triple `[φ_n : ω_n : ψ_n]`, the displayed clearing factor may change, but the invariant content is exactly

```text
[n]^* η = (n : K) • η.
```

This is the correct place to do the division-polynomial computation.  Once it is proved as an identity of rational differentials on the function field, it extends across the zeros of `ψ_n`; one should not do L'Hôpital in the affine `x`-chart at those points.

## Lean guidance

For Lean, I would avoid trying to prove the originally stated dual-number lemma with the global `t = -x/y`.  A robust route is:

1. Define or use the invariant differential `η`.
2. Prove, possibly by direct division-polynomial calculation, that the multiplication map satisfies

   ```lean
   [n]^* η = (n : K) • η
   ```

   as a rational differential/function-field identity.
3. Prove in the projective chart at `O` that the local parameter

   ```text
   t = -X Z / Y
   ```

   satisfies `dt/η = 1` at `O`.
4. For a point `P` with `[n]P = O`, compare against a translated source local parameter `τ_P`, not the unshifted affine function `-x/y`.

The theorem statement should therefore look morally like

```text
coeffε (t_O ([n] Pε)) = (n : K) * coeffε (τ_P Pε),
```

where `τ_P` is a local parameter at `P` normalized by the invariant differential.  If `P = O`, then `τ_P` can be the usual `t`; if `P` is nonzero torsion, it must be translated or otherwise locally normalized.

## Bottom line

The projective division-polynomial formula is enough to rederive the multiplier `(n : K)`, but only through the invariant differential or an equivalent local-chart computation.  Trying to read `d[n]|_O = n` from the affine derivative of

```text
x([n]P) = φ_n(P) / ψ_n(P)^2
```

at `ψ_n(P) = 0` is the wrong chart.  The affine `x`-coordinate has a pole at `O`; the projective parameter `t = -XZ/Y` fixes the target chart, and a translated/normalized local parameter fixes the source chart.
