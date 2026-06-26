# Q823 (dm1): the `n = 5` odd base case for separability of `preΨ'`

## Executive summary

The recurrence shortcut is real, but it is **not enough by itself** to prove separability of `preΨ'(5)` from separability of `Ψ₃`.

The identity

```text
preΨ'(5) = preΨ₄ * Ψ₂Sq^2 - Ψ₃^3
```

is the right way to avoid expanding the degree-12 polynomial.  It gives a compact expression for the polynomial and for its derivative.  It also immediately disposes of the special strata `Ψ₃(x) = 0` and `Ψ₂Sq(x) = 0` under `Δ ≠ 0`.

But the hard case is the generic stratum

```text
Ψ₂Sq(x) ≠ 0,   Ψ₃(x) ≠ 0,   preΨ₄(x) ≠ 0.
```

On that stratum, a double root of

```text
preΨ₄ * Ψ₂Sq^2 - Ψ₃^3
```

is a logarithmic-derivative condition.  It does not force `Ψ₃(x) = 0` or `Ψ₃'(x) = 0`, so the already-proved separability of `Ψ₃` does not close the case.

So the answer is:

* **yes**, use the recurrence identity to keep the algebra small;
* **no**, it does not eliminate the need for a real `n = 5` argument;
* the cleanest shortcut is geometric/differential: `[5]` is étale when `(5 : K) ≠ 0`, hence the 5-torsion kernel is reduced, hence the odd 5-division polynomial is squarefree away from the `x`-map ramification locus, and a 5-torsion point is not 2-torsion.

If you want a purely polynomial proof, the recurrence identity lets you replace one huge expanded degree-12 Bézout certificate by a much more structured certificate using a few small auxiliary identities.  But some certificate/resultant for the remaining generic stratum is still needed.

## First correction: the Mathlib recurrence index

For the `ℕ`-indexed Mathlib theorem

```lean
W.preΨ'_odd (m : ℕ)
```

the statement is shifted:

```lean
W.preΨ' (2 * (m + 2) + 1) =
  W.preΨ' (m + 4) * W.preΨ' (m + 2)^3 *
      (if Even m then W.Ψ₂Sq^2 else 1)
    - W.preΨ' (m + 1) * W.preΨ' (m + 3)^3 *
      (if Even m then 1 else W.Ψ₂Sq^2)
```

So for `n = 5`, use `m = 0`, not `m = 2`.  The `ℤ`-indexed recurrence has the unshifted shape where `2*m+1 = 5` means `m = 2`.

A useful local lemma is:

```lean
lemma preΨ'_five {K : Type*} [CommRing K] (W : WeierstrassCurve K) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show 5 = 2 * (0 + 2) + 1 by norm_num, W.preΨ'_odd 0]
  simp
```

This is the right normal form for the `n = 5` base case.

## Do not call it a factorization

The expression

```text
preΨ₄ * Ψ₂Sq^2 - Ψ₃^3
```

is not a multiplicative factorization of `preΨ'(5)`.  It is a structured difference of products.  This matters: squarefreeness of the pieces does not imply squarefreeness of the difference.

The derivative is

```text
(preΨ₄ * Ψ₂Sq^2 - Ψ₃^3)'
  = preΨ₄' * Ψ₂Sq^2
      + 2 preΨ₄ * Ψ₂Sq * Ψ₂Sq'
      - 3 Ψ₃^2 * Ψ₃'.
```

At a root, this is a relation among three nonzero terms in the generic stratum.  It is not simply saying that one of the known lower polynomials has a multiple root.

## The small identities that make the algebra manageable

Use the following abbreviations:

```text
S := Ψ₂Sq
C := Ψ₃
D := preΨ₄
L := 6X^2 + b₂X + b₄
M := 12X + b₂        -- so M = L'
P₅ := D*S^2 - C^3
```

There are three very useful identities.

### 1. `C' = 3S`

```text
(Ψ₃)' = 3 Ψ₂Sq.
```

This is immediate from the definitions:

```text
Ψ₃ = 3X^4 + b₂X^3 + 3b₄X^2 + 3b₆X + b₈
Ψ₂Sq = 4X^3 + b₂X^2 + 2b₄X + b₆.
```

### 2. `S' = 2L`

```text
(Ψ₂Sq)' = 2 * (6X^2 + b₂X + b₄).
```

### 3. `D + S^2 = L*C`

The key identity, already useful in the `Ψ₃ = 0` stratum, is

```text
preΨ₄ + Ψ₂Sq^2 = (6X^2 + b₂X + b₄) * Ψ₃.
```

In Lean this is a small `ring1` proof after unfolding `preΨ₄`, `Ψ₂Sq`, `Ψ₃`, and the `bᵢ` definitions:

```lean
lemma preΨ₄_add_Ψ₂Sq_sq {K : Type*} [CommRing K] (W : WeierstrassCurve K) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      (C (6 : K) * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃, b₂, b₄, b₆, b₈]
  ring1
```

Differentiating this identity and using `C' = 3S`, `S' = 2L` gives

```text
D' = M*C - L*S.
```

Then the derivative of `P₅` has the compact form

```text
P₅' = S * (M*C*S + 4*L^2*C - 5*L*S^2 - 9*C^2).
```

This formula is far better than expanding the derivative of the degree-12 polynomial.

## What the recurrence identity proves immediately

Assume `x` is a root of `P₅`.

### Stratum `S(x) = 0`

If

```text
S(x) = Ψ₂Sq(x) = 0,
```

then

```text
0 = P₅(x) = D(x)*S(x)^2 - C(x)^3 = -C(x)^3,
```

so `C(x) = 0`.

Thus `x` is a common root of `Ψ₂Sq` and `Ψ₃`.  The small resultant is

```text
Res(Ψ₂Sq, Ψ₃) = -Δ^2.
```

So under `Δ ≠ 0`, this stratum is impossible.

This is a much smaller certificate than the degree-12 resultant: it is only a cubic/quartic resultant.

### Stratum `C(x) = 0`

If

```text
C(x) = Ψ₃(x) = 0,
```

then the identity

```text
D + S^2 = L*C
```

specializes to

```text
D(x) = -S(x)^2.
```

Therefore

```text
P₅(x) = D(x)*S(x)^2 - C(x)^3 = -S(x)^4.
```

So `P₅(x) = 0` implies `S(x) = 0`, again contradicting `Res(S,C) = -Δ^2` and `Δ ≠ 0`.

Thus every root of `P₅` lies in the generic stratum

```text
S(x) ≠ 0,   C(x) ≠ 0,   D(x) ≠ 0.
```

This is the useful payoff of the recurrence identity.

## Why this still does not prove separability

Now suppose `x` is a double root.  In the generic stratum, the two equations are

```text
P₅(x) = 0,
P₅'(x) = 0.
```

Using the compact formulas, these become

```text
D*S^2 = C^3,
M*C*S + 4*L^2*C - 5*L*S^2 - 9*C^2 = 0,
```

with `S,C,D ≠ 0`, all evaluated at `x`.

Using `D = L*C - S^2`, the first equation can also be written as

```text
C^3 = L*C*S^2 - S^4.
```

This does **not** imply

```text
C = 0
```

or

```text
C' = 0.
```

So separability of `Ψ₃` does not contradict these equations.  The derivative equation is a logarithmic-derivative relation

```text
D'/D + 2*S'/S = 3*C'/C,
```

not a multiple-root condition for one of `D`, `S`, or `C` individually.

This is the obstruction to the proposed shortcut.

There is also a characteristic issue: if your theorem only assumes `(5 : K) ≠ 0`, then `char K` may be `3`.  In characteristic `3`, `Ψ₃` is not the right separability input anyway.  The robust lower-level fact is not “`Ψ₃` is separable”, but rather the coprimality/no-common-root statement

```text
gcd(Ψ₂Sq, Ψ₃) = 1
```

under `Δ ≠ 0`, witnessed by `Res(Ψ₂Sq, Ψ₃) = -Δ^2`.

## Best shortcut: use étaleness of `[5]`

The conceptual proof of the `n = 5` base case is not a polynomial Bézout proof.  It is this:

1. Since `5` is odd, `preΨ'(5)` is the x-polynomial representing the full `5`-division polynomial; there is no `ψ₂`/`Y` factor.

2. A root `x₀` of `preΨ'(5)` gives points `P = (x₀, y₀)` with `[5]P = O` over an algebraic closure.

3. The previous stratum analysis shows `Ψ₂Sq(x₀) ≠ 0`, so `P` is not a 2-torsion/ramification point of the `x`-map.  Equivalently, `x - x₀` is a local parameter at `P`.

4. If `preΨ'(5)` had a multiple root at `x₀`, then the corresponding function `ψ₅` would vanish to order at least `2` at `P`.

5. But `[5]` is étale when `(5 : K) ≠ 0`.  Equivalently, on the formal group the tangent map is multiplication by `5`, hence a unit.  Therefore the kernel of `[5]` is reduced, so `ψ₅` vanishes simply at each nonzero 5-torsion point.

6. Contradiction.

This avoids the degree-12 Bézout certificate completely.

This route matches the “dual-number tangent” bridge you have been developing: a double root should produce a nontrivial dual-number lift of a 5-torsion point in the kernel of `[5]`; the tangent calculation `[5]' = 5` rules this out when `(5 : K) ≠ 0`.

## If you stay purely algebraic

Then the recurrence identity should still be used, but the proof shape should be:

1. Prove the compact identity

   ```lean
   W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3
   ```

2. Prove the small auxiliary identities

   ```text
   Ψ₃' = 3 Ψ₂Sq
   Ψ₂Sq' = 2L
   preΨ₄ + Ψ₂Sq^2 = L Ψ₃
   preΨ₄' = M Ψ₃ - L Ψ₂Sq
   ```

3. Prove the compact derivative formula

   ```text
   (preΨ'(5))' =
     Ψ₂Sq * (M*Ψ₃*Ψ₂Sq + 4*L^2*Ψ₃ - 5*L*Ψ₂Sq^2 - 9*Ψ₃^2).
   ```

4. Use `Res(Ψ₂Sq, Ψ₃) = -Δ^2` to eliminate the `S = 0` and `C = 0` strata.

5. For the remaining generic stratum, either:

   * use the geometric/dual-number `[5]' = 5` argument; or
   * use a structured resultant/certificate for the two compact equations

     ```text
     C^3 = L*C*S^2 - S^4,
     M*C*S + 4*L^2*C - 5*L*S^2 - 9*C^2 = 0.
     ```

The direct resultant for the fully expanded polynomial should be, with Mathlib's normalization,

```text
Res(preΨ'(5), (preΨ'(5))') = 5^12 * Δ^22
```

(up to the conventional sign of `Polynomial.resultant`; for degree `12` the usual sign is harmless).  But proving that directly in Lean is exactly the large certificate you are trying to avoid.

## Bottom line

The recurrence formula is the right normalization lemma:

```text
preΨ'(5) = preΨ₄ * Ψ₂Sq^2 - Ψ₃^3.
```

Use it.  It makes the `Ψ₃ = 0` and `Ψ₂Sq = 0` strata easy and gives a compact derivative formula.

But it does **not** reduce separability of `preΨ'(5)` to separability of `Ψ₃`.  The remaining generic case is genuinely the statement that `[5]` is étale, or equivalently that the degree-12 resultant is a unit under `Δ ≠ 0` and `(5 : K) ≠ 0`.

So the cleanest non-certificate shortcut is the dual-number/formal-group proof of étaleness of `[5]`.  If you want to remain purely inside polynomial algebra, keep the recurrence normal form and prove a structured resultant, not the fully expanded degree-12 Bézout identity.
