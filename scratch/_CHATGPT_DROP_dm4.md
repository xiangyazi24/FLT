# Q778 (dm4): proving separability of `preΨ'(n)` without defining `Ω_n`

## Bottom line

Do **not** define `Ω_n` just to prove separability of `preΨ'(n)`.  The clean route is the infinitesimal/kernel route:

```text
[n] is étale when (n : K) ≠ 0,
so its kernel has no nonzero dual-number tangent,
so the function cutting out the affine kernel has simple zeros.
```

In concrete Lean terms, this is the **dual-number/projective-coordinate proof**, not the `Ω_n` proof.

The set-theoretic statement

```text
ψ_n(P) = 0  ⇒  [n]P = O
```

is not enough by itself.  Squarefreeness is infinitesimal data.  A polynomial can cut out the correct set of points and still have multiple roots.  To prove

```text
ψ_n'(x₀) ≠ 0,
```

you need a first-order statement, either a differential identity or a dual-number argument.  Since `Ω_n` is absent from Mathlib and the usual formula for it has characteristic-`2` issues, the dual-number argument is the better Mathlib-compatible route.

## Correcting the formal-group intuition

The objection in the prompt is right in this form:

```text
[n]_F'(0) = n
```

is a statement at the identity, not directly at the torsion point `P`.

But for an elliptic curve, the differential of `[n]` is translation-invariant.  If `P` is an `n`-torsion point, then locally at `P` write a first-order deformation as

```text
P_ε = P + Q_ε,
```

where `Q_ε` is a dual-number point in the formal neighborhood of `O`.  Then

```text
[n](P_ε) = [n]P + [n](Q_ε) = O + [n](Q_ε) = [n](Q_ε).
```

On first-order tangent vectors, the formal group theorem gives

```text
[n](Q_ε) = n · Q_ε    mod ε².
```

Thus, if `(n : K) ≠ 0`, a nonzero tangent vector at any `n`-torsion point cannot be killed by `[n]`.  This is the infinitesimal fact you need.

So the right statement is not “evaluate `[n]_F` at `t(P)`.”  It is:

```text
d[n]_P = d(translation) ∘ d[n]_O ∘ d(translation),
```

and `d[n]_O` is scalar multiplication by `(n : K)`.

## Odd `n`: the dual-number proof

Let

```text
ψ = preΨ'(n)
```

in the odd case, so `ψ` is the usual x-polynomial division factor.

Work over an algebraic closure or a splitting field.  Let `x₀` be a root of `ψ`, and let `P = (x₀, y₀)` be the corresponding affine point on the curve.  The existing Mathlib facts you want to use are:

```text
ψ_n(P.x) = 0        ⇒        [n]P = O,
Φ_n(P.x) ≠ 0        at roots of ψ_n,
```

where the nonvanishing of `Φ_n` comes from the identity

```text
Φ_n = x · ψ_n² - ψ_{n+1}ψ_{n-1} · factor
```

plus the adjacent nonvanishing/coprimality lemma such as `no_adjacent_preΨ_zero`.

Now suppose, for contradiction, that

```text
ψ'(x₀) = 0.
```

Because `n` is odd, `P` is not a nontrivial `2`-torsion point.  Indeed, if `P` were killed by both `2` and odd `n`, it would be killed by `gcd(2,n)=1`, hence would be `O`, impossible for an affine root.  Therefore the projection to the `x`-line is unramified at `P`; equivalently

```text
v(P) = 2y₀ + a₁x₀ + a₃ ≠ 0.
```

This lets you build a dual-number tangent lift with `dx = 1`:

```text
x_ε = x₀ + ε,
y_ε = y₀ + y₁ ε,
```

where `y₁` is chosen from the linearized curve equation

```text
F_x(P) + F_y(P) · y₁ = 0,
```

and `F_y(P) = v(P)` is invertible.  Thus `P_ε = (x_ε, y_ε)` is a genuine `DualNumber K`-point of the curve with nonzero tangent vector.

For any polynomial `p`, evaluation on dual numbers gives

```text
p(x₀ + ε) = p(x₀) + p'(x₀) ε.
```

Applying this to `ψ`, the assumptions `ψ(x₀)=0` and `ψ'(x₀)=0` give

```text
ψ(x_ε) = 0
```

inside the dual-number ring.

Now use the projective division-polynomial/nsmul formula over the dual-number algebra.  Since the same kernel-cutting factor `ψ` vanishes on `P_ε`, and since `Φ_n(P_ε)` is a unit because its residue `Φ_n(P)` is nonzero, the projective formula forces

```text
[n](P_ε) = O
```

over the dual numbers.

But this says that the nonzero tangent vector represented by `P_ε` lies in the infinitesimal kernel of `[n]` at `P`.  That contradicts the formal-group/tangent result above, because `(n : K) ≠ 0`.

Therefore

```text
ψ'(x₀) ≠ 0.
```

Since this holds at every geometric root, `ψ` is squarefree, hence separable.

## What exactly must be proved in Lean

The proof can be organized into four reusable lemmas.

```lean
-- Schematic names only.  Use the repository/Mathlib names for the curve,
-- points, division polynomials, and dual-number API.

/-- Polynomial evaluation on a first-order x-lift. -/
theorem eval_dual_x_eq_eval_add_derivative
    (p : Polynomial K) (x₀ : K) :
    aeval (x₀ + ε) p = p.eval x₀ + (p.derivative.eval x₀) * ε := by
  -- standard polynomial induction / existing dual-number simp lemma
  sorry

/-- A nonvertical affine point admits a dual lift with dx = 1. -/
theorem exists_dual_lift_dx_one
    {P : E(K)} (hvertical : v P ≠ 0) :
    ∃ Pε : E(DualNumber K),
      residue Pε = P ∧ dx_tangent Pε = 1 := by
  -- choose y₁ = -F_x(P) / F_y(P)
  sorry

/-- If ψ_n and its derivative vanish at x(P), the dual lift is still in the ψ_n-zero locus. -/
theorem preΨ_dual_zero_of_root_and_derivative_zero
    {P : E(K)} {Pε : E(DualNumber K)}
    (hres : residue Pε = P)
    (hroot : (preΨ' n).eval P.x = 0)
    (hder : (preΨ' n).derivative.eval P.x = 0)
    (hdx : dx_tangent Pε = 1) :
    aeval Pε.x (preΨ' n) = 0 := by
  -- use `eval_dual_x_eq_eval_add_derivative`
  sorry

/-- No nonzero dual tangent at an n-torsion point is killed by [n] when n is invertible. -/
theorem no_infinitesimal_kernel_of_nsmul
    {P : E(K)} (hP : n • P = 0) (hn : (n : K) ≠ 0)
    {Pε : E(DualNumber K)}
    (hres : residue Pε = P) (htangent_ne : tangent Pε ≠ 0) :
    n • Pε ≠ O := by
  -- translate by `-P`, reduce to the formal group at O,
  -- and use `FormalNsmulDirect`: first-order coefficient is `(n : K)`.
  sorry
```

Then the root-level theorem is short:

```lean
theorem derivative_preΨ'_ne_zero_at_root_odd
    (hn_odd : Odd n) (hn : (n : K) ≠ 0)
    {x₀ : Kbar} (hroot : (preΨ' n).eval x₀ = 0) :
    ((preΨ' n).derivative.eval x₀) ≠ 0 := by
  intro hder

  -- Get an affine n-torsion point P above x₀.
  obtain ⟨P, hxP, hnP, hP_ne_O⟩ := point_of_preΨ'_root hroot

  -- Odd n means P is not 2-torsion, hence the x-map is unramified at P.
  have hv : v P ≠ 0 := by
    -- if v P = 0 then P is 2-torsion; combine with hnP and odd n.
    sorry

  -- Build a nonzero dual tangent with dx = 1.
  obtain ⟨Pε, hres, hdx⟩ := exists_dual_lift_dx_one hv
  have htangent_ne : tangent Pε ≠ 0 := by
    -- because dx_tangent = 1
    sorry

  -- ψ vanishes on the dual lift because ψ and ψ' vanish at x₀.
  have hψ_dual : aeval Pε.x (preΨ' n) = 0 := by
    exact preΨ_dual_zero_of_root_and_derivative_zero hres hroot hder hdx

  -- Projective division-polynomial formula: ψ=0 and Φ unit imply n • Pε = O.
  have hnPε : n • Pε = O := by
    apply nsmul_eq_zero_of_preΨ'_dual_zero
    · exact hψ_dual
    · -- Φ is a unit on Pε because Φ(P) ≠ 0, from adjacent nonvanishing.
      exact Phi_unit_at_dual_root hres hroot

  -- But [n] has no infinitesimal kernel when n is invertible.
  exact no_infinitesimal_kernel_of_nsmul hnP hn hres htangent_ne hnPε
```

The names are schematic, but this is the minimal shape: only `preΨ'`, `Φ`, adjacent nonvanishing, projective division-polynomial formulas, and formal-group/tangent scalar multiplication by `n`.

## Even `n`

For even `n`, split off the `2`-torsion/vertical factor exactly as Mathlib’s normalization requires.

The non-`2` roots are handled by the same argument: they are affine `n`-torsion points where the x-map is unramified, so the dual lift with `dx = 1` exists and the infinitesimal-kernel contradiction proves simple roots.

The `2`-torsion factor is separate.  If `(n : K) ≠ 0` and `n` is even, then `char K ≠ 2`.  In that case the `2`-torsion x-polynomial is squarefree by nonsingularity of the Weierstrass cubic: a multiple root of the cubic would make the affine cubic singular.  The `2`-torsion factor is coprime to the remaining factor because a common root would be a point killed by both `2` and the odd quotient, hence killed by `1`, i.e. the identity.

So the even proof should be a factorization proof:

```text
preΨ'(2m) = two_torsion_factor * non2_factor
```

with

```text
Squarefree two_torsion_factor,
Squarefree non2_factor,
IsCoprime two_torsion_factor non2_factor.
```

## Why defining `Ω_n` is not simpler

There are three traps in the `Ω_n` route.

First, the common formula

```text
Ω_n = (ψ_{2n}/ψ_n - ψ_n(a₁Φ_n + a₃ψ_n²)) / 2
```

is not characteristic-free.  It is fine when `2` is invertible, but it is not a good target for the theorem stated only under `(n : K) ≠ 0`.

Second, defining `Ω_n` by the Weierstrass equation

```text
Ω_n² + a₁Φ_nΩ_nψ_n + a₃Ω_nψ_n³
  = Φ_n³ + a₂Φ_n²ψ_n² + a₄Φ_nψ_n⁴ + a₆ψ_n⁶
```

is not really a definition.  It asks Lean to construct a polynomial square root / y-coordinate numerator.  That is essentially the missing Mathlib TODO.

Third, even if you define `Ω_n`, the separability proof still needs the differential/local-parameter identity.  Constructing `Ω_n` and proving that identity is at least as much work as the dual-number proof, and likely more.

## An Ω-free polynomial certificate, if you want one

There is a useful identity with no `Ω_n` in the **statement**.  From the local-parameter congruence

```text
v · Φ_n · ψ_n' + n · Ω_n ≡ 0 mod ψ_n
```

and the cleared curve equation, which gives

```text
Ω_n² ≡ Φ_n³ mod ψ_n,
```

one obtains the squared congruence

```text
v² · Φ_n² · (ψ_n')² ≡ n² · Φ_n³     mod ψ_n.      (†)
```

Equivalently, in the affine coordinate ring,

```text
ψ_n ∣ v² · Φ_n² · (ψ_n')² - n² · Φ_n³.
```

This identity is characteristic-free and does not mention `Ω_n`.  At a root of `ψ_n`, adjacent nonvanishing gives `Φ_n(x₀) ≠ 0`; if `ψ_n'(x₀)=0`, then `(†)` gives

```text
0 = n² · Φ_n(x₀)³,
```

contradicting `(n : K) ≠ 0` and `Φ_n(x₀) ≠ 0`.

However, proving `(†)` globally still requires some source of infinitesimal information.  Without `Ω_n`, that source is again the dual-number/projective-coordinate proof.  So `(†)` is a nice optional final certificate, but it is not a replacement for the infinitesimal argument unless you already have a way to prove it.

## Recommended implementation path

Use this order.

1. Prove the standard dual-number polynomial evaluation lemma:

```text
p(x + εu) = p(x) + p'(x)u ε.
```

2. Prove the nonvertical dual lift lemma for affine curve points.

3. Prove the infinitesimal kernel lemma for `[n]` from `FormalNsmulDirect`, using translation by the torsion point.

4. Extend the existing division-polynomial root criterion to dual numbers using projective formulas.  The needed input is only the `Z`/denominator factor `ψ_n` and the fact that `Φ_n` is a unit at a `ψ_n`-root.

5. Combine them to prove root-level derivative nonvanishing.

6. Convert root-level derivative nonvanishing over an algebraic closure into

```text
IsCoprime (preΨ' n) (Polynomial.derivative (preΨ' n))
```

or the Mathlib separability predicate you need.

This avoids `Ω_n`, avoids division by `2`, and proves exactly the infinitesimal fact that squarefreeness requires.
