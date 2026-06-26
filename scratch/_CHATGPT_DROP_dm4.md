# Q764 (dm4): separability of `preΨ'(n)` from the differential of `[n]`

## Bottom line

Yes: there is a clean identity, but I would **not** use the raw total derivative of the `x`-coordinate as the main separability certificate.  The better identity comes from the local parameter at infinity.

I will write

```text
ψ  = ψ_n        -- the x-polynomial `preΨ'(n)` in the odd case
Φ  = Φ_n        -- x-coordinate numerator
Ω  = Ω_n        -- y-coordinate numerator, not the invariant differential
v  = 2y + a₁x + a₃
```

so that on the affine coordinate ring of

```text
F = y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆
```

we have

```text
[n](P) = (Φ/ψ², Ω/ψ³).
```

The useful root-level identity is the congruence

```text
v · Φ · ∂xψ + n · Ω ≡ 0    mod ψ.        (★)
```

Depending on the sign convention for the local parameter, this may appear as

```text
v · Φ · ∂xψ - n · Ω ≡ 0    mod ψ.
```

The sign is irrelevant for separability.  What matters is that the identity has **no factor of 2** in front of `∂xψ`, so it works in characteristic `2` as long as `(n : K) ≠ 0`.

Equivalently, in the coordinate ring `R = K[x,y]/(F)`, the statement can be packaged as

```text
∃ H_n : R,
  v · Φ_n · ∂xψ_n + (n : K) · Ω_n = ψ_n · H_n.
```

This is the polynomial identity I would target.

## Why the direct `x`-coordinate derivative is weaker

The invariant differential is

```text
ω_E = dx / v.
```

Also

```text
v([n]P) = 2(Ω/ψ³) + a₁(Φ/ψ²) + a₃
        = (2Ω + a₁Φψ + a₃ψ³) / ψ³.
```

Since

```text
d(Φ/ψ²) = (Φ'ψ - 2Φψ') / ψ³ · dx,
```

the identity `[n]^*ω_E = n · ω_E` gives the correct global Wronskian identity

```text
v · (Φ'ψ - 2Φψ') = n · (2Ω + a₁Φψ + a₃ψ³).      (x-W)
```

Modulo `ψ`, this becomes

```text
-2 · v · Φ · ψ' = 2 · n · Ω.                      (x-W mod ψ)
```

This proves the desired root statement in characteristics different from `2`, after proving the relevant numerator terms are nonzero.  But it loses all information in characteristic `2`.  That is the main reason to avoid making `(x-W)` the primary proof of separability.

## Derivation of the clean congruence `(★)`

Use the standard local parameter at infinity

```text
t = -x/y.
```

At the identity `O`, `dt` and the invariant differential differ by a unit whose value at `O` is `1`.  Hence, at points mapping to `O`, the differential of `t ∘ [n]` has leading coefficient `n`:

```text
d(t ∘ [n]) = n · ω_E          on the kernel, up to a unit evaluating to 1.
```

Now compute `t ∘ [n]` using the division-polynomial coordinates:

```text
t([n]P) = - x([n]P) / y([n]P)
        = - (Φ/ψ²) / (Ω/ψ³)
        = - Φψ / Ω.
```

Reducing the differential modulo `ψ`, all terms containing an explicit factor of `ψ` vanish, so

```text
d(-Φψ/Ω) ≡ - (Φ/Ω) · dψ    mod ψ.
```

Since `ψ = ψ(x)`,

```text
dψ = ψ'(x) · dx = ψ'(x) · v · ω_E.
```

Therefore, modulo `ψ`,

```text
- (Φ/Ω) · ψ' · v · ω_E = n · ω_E.
```

Multiplying by `Ω` gives

```text
v · Φ · ψ' + n · Ω = 0       mod ψ,
```

up to the harmless sign convention mentioned above.

This is the clean identity that directly relates `n`, `ψ_n`, `ψ_n'`, and the other division-polynomial numerators.

## How `(★)` proves separability

Let `P = (x₀,y₀)` be an affine geometric point with

```text
ψ_n(x₀) = 0.
```

Assume `(n : K) ≠ 0`.  If also

```text
ψ_n'(x₀) = 0,
```

then evaluating `(★)` at `P` gives

```text
n · Ω_n(P) = 0.
```

Since `(n : K) ≠ 0`, this forces

```text
Ω_n(P) = 0.
```

But `Ω_n(P)` is nonzero at a nonzero `n`-torsion point.  Here is the elementary proof.

First,

```text
Φ_n = xψ_n² - ψ_{n+1}ψ_{n-1},
```

so modulo `ψ_n`,

```text
Φ_n ≡ -ψ_{n+1}ψ_{n-1}.                         (1)
```

At a point with `ψ_n(P)=0`, the factors `ψ_{n-1}(P)` and `ψ_{n+1}(P)` are nonzero: otherwise `P` would be simultaneously killed by `n` and by `n-1` or `n+1`, hence killed by `gcd(n,n±1)=1`, forcing `P=O`, impossible for an affine root.  In a purely EDS proof this is exactly the easy coprimality lemma

```text
gcd(ψ_n, ψ_{n-1}) = gcd(ψ_n, ψ_{n+1}) = 1.
```

Thus

```text
Φ_n(P) ≠ 0.                                      (2)
```

Next use the cleared curve equation for the image coordinates.  Since

```text
x([n]P) = Φ/ψ²,
y([n]P) = Ω/ψ³,
```

substitution into the Weierstrass equation and multiplication by `ψ⁶` gives

```text
Ω² + a₁ΦΩψ + a₃Ωψ³
  = Φ³ + a₂Φ²ψ² + a₄Φψ⁴ + a₆ψ⁶.                (3)
```

Modulo `ψ`, this reduces to

```text
Ω² ≡ Φ³    mod ψ.                                (4)
```

Evaluating at `P`, equations `(2)` and `(4)` imply

```text
Ω_n(P)² = Φ_n(P)³ ≠ 0,
```

so

```text
Ω_n(P) ≠ 0.
```

This contradicts the consequence of `(★)` and `ψ_n'(x₀)=0`.  Therefore

```text
ψ_n'(x₀) ≠ 0.
```

Since every geometric root has nonzero derivative, `ψ_n` is squarefree, equivalently

```text
gcd(ψ_n, ψ_n') = 1.
```

This is the characteristic-free separability proof for `(n : K) ≠ 0`.

## Even `n`

For even `n`, the usual division polynomial has the extra factor

```text
ψ₂ = 2y + a₁x + a₃.
```

If `preΨ'(n)` is the x-polynomial factor with the `ψ₂`/vertical factor removed, apply the same argument to roots with `ψ₂(P) ≠ 0`.  The removed `2`-torsion part is handled separately: when `(n : K) ≠ 0` and `n` is even, the characteristic is not `2`, and nonsingularity of the Weierstrass cubic gives the separability of the `2`-torsion x-polynomial.  The two factors are coprime because a point in the non-`2` part and in the `2`-torsion part would have order dividing both `2` and the odd quotient, hence would be trivial.

So the implementation split should be:

```text
odd n:
  use the congruence (★) directly for ψ_n = preΨ'(n)

even n:
  remove the ψ₂ factor;
  use (★) on the non-2 roots;
  prove the ψ₂/x-cubic part squarefree from nonsingularity;
  prove the two factors coprime by torsion-order/copairing.
```

## Can this be proved by Somos/EDS recurrence plus resultants?

In principle, yes, but it is not the route I would mechanize first.

The recurrence is good for the **reduced** facts:

```text
gcd(ψ_n, ψ_{n-1}) = 1,
gcd(ψ_n, ψ_{n+1}) = 1,
Φ_n ≡ -ψ_{n+1}ψ_{n-1} mod ψ_n,
Ω_n² ≡ Φ_n³ mod ψ_n.
```

These are exactly the facts needed to show `Φ_n` and `Ω_n` are units at roots of `ψ_n`.

But multiplicity is infinitesimal.  To prove

```text
gcd(ψ_n, ψ_n') = 1,
```

a recurrence-only proof eventually has to reintroduce either a differential argument or a discriminant/resultant theorem.  The classical resultant certificate is a universal formula of the shape

```text
Disc(preψ_n) = unit · n^A · Δ^B
```

with exponents depending on the normalization and parity.  Since the curve is nonsingular (`Δ ≠ 0`) and `(n : K) ≠ 0`, the discriminant is nonzero, so the polynomial is squarefree.

That is a valid mathematical proof, but in Lean it is likely much heavier than the differential congruence: it requires setting up the universal division polynomials, proving the resultant/discriminant formula through the recursive definitions, tracking normalizations and the even factor, and then specializing.  The differential/local-parameter proof instead needs only the coordinate formulas for `[n]`, the invariant differential identity `[n]^*ω_E = nω_E`, and the small coprimality/unit lemmas above.

## Suggested Lean target lemmas

I would aim for these lemmas, using the repository's actual names for `preΨ'`, `Φ`, and `Ω`.

```lean
-- Schematic, not exact repo syntax.

/-- The clean root congruence coming from `t = -x/y`. -/
theorem divpoly_derivative_congr_mod_psi
    (n : ℕ) (hn : (n : K) ≠ 0) :
    v * Φ n * (Polynomial.derivative (preΨ' n)).aeval x + (n : R) * Ω n
      ∈ Ideal.span ({preΨ' n} : Set R) := by
  -- derive from `t ∘ [n] = -Φψ/Ω` and `[n]^*ω = nω`
  -- after reducing modulo `ψ`.
  sorry

/-- At a root of `ψ_n`, the y-coordinate numerator is nonzero. -/
theorem Omega_ne_zero_of_psi_eq_zero
    {P : E(Kbar)} (hP : preΨ' n P.x = 0) (hPaff : P ≠ O) :
    Ω n P ≠ 0 := by
  -- `Φ ≡ -ψ_{n+1}ψ_{n-1} mod ψ`, consecutive gcd/torsion coprime,
  -- and the cleared curve equation gives `Ω² ≡ Φ³ mod ψ`.
  sorry

/-- Root-level derivative nonvanishing. -/
theorem derivative_preΨ'_ne_zero_at_root
    {P : E(Kbar)} (hn : (n : K) ≠ 0)
    (hroot : preΨ' n P.x = 0) (hPaff : P ≠ O) :
    (Polynomial.derivative (preΨ' n)).eval P.x ≠ 0 := by
  intro hder
  have hcongr := divpoly_derivative_congr_mod_psi n hn
  -- evaluate at P; the derivative term vanishes, so `(n : K) * Ω n P = 0`.
  -- use `hn` and `Omega_ne_zero_of_psi_eq_zero`.
  sorry

/-- Separability/squarefreeness of the division polynomial. -/
theorem separable_preΨ'_of_char_not_dvd
    (n : ℕ) (hn : (n : K) ≠ 0) :
    (preΨ' n).Separable := by
  -- reduce to geometric roots and use `derivative_preΨ'_ne_zero_at_root`.
  sorry
```

The key point is that the first lemma should be the congruence `(★)`, not the full `x`-coordinate Wronskian.  The Wronskian is still useful as a check, but `(★)` is the identity that gives separability cleanly at a root.
