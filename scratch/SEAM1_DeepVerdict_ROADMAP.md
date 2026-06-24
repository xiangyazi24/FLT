[ask-gpt dm1 tid=73a35cf6 +0s] dispatched, waiting for answer
[ask-gpt dm1 tid=73a35cf6 +90s] waiting (status=processing)
[ask-gpt dm1 tid=73a35cf6 +180s] waiting (status=processing)
[ask-gpt dm1 tid=73a35cf6 +270s] waiting (status=processing)
[ask-gpt dm1 tid=73a35cf6 +336s] terminal: status=completed
## Verdict

`ΨSq_order_two_at_non2_kernel` is **buildable in principle**, but **not closeable from the current SEAM2 + DualNumber first-jet stack alone**. It is a genuine missing local-analytic/formal-neighborhood theorem.

The pointwise SEAM2 theorem

```lean
xRep (n • P) ~ ![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

does not know multiplicity. The DualNumber calculation knows only the first derivative. To get

```lean
(Polynomial.evalAtX x₀ (W.ΨSq n)).order = 2
```

you need a formal arc / completed-local-ring version of SEAM2, plus the fact that `[n]` maps a local parameter at a kernel point to a unit multiple of the local parameter at `O`.

So I would mark this as a **named seam**, not as a small remaining lemma.

---

# 1. Minimal formal-arc development

The smallest honest development is option **(a)**: build only the local arcs needed for this theorem, not the full global formal group.

At a non-2 affine point

\[
P=(x_0,y_0),
\]

use the local parameter

\[
T=x-x_0.
\]

The non-2 condition is exactly

\[
2y_0+a_1x_0+a_3\ne0,
\]

so the Weierstrass equation can be solved uniquely as a power series

\[
y(T)=y_0+\cdots
\]

with \(x(T)=x_0+T\).

The first local object is:

```lean
namespace WeierstrassCurve.LocalArc

open PowerSeries Polynomial

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

noncomputable def yAtNon2
    (x₀ y₀ : k)
    (hcurve : W.toAffine.Equation x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    PowerSeries k := by
  -- recursive/Hensel construction
  sorry

theorem yAtNon2_coeff_zero
    (x₀ y₀ : k)
    (hcurve : W.toAffine.Equation x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    PowerSeries.coeff 0 (W.yAtNon2 x₀ y₀ hcurve hdy) = y₀ := by
  sorry

theorem yAtNon2_equation
    (x₀ y₀ : k)
    (hcurve : W.toAffine.Equation x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    let Xser : PowerSeries k := PowerSeries.C x₀ + PowerSeries.X
    let Yser : PowerSeries k := W.yAtNon2 x₀ y₀ hcurve hdy
    Yser^2 + PowerSeries.C W.a₁ * Xser * Yser
      + PowerSeries.C W.a₃ * Yser
      =
    Xser^3 + PowerSeries.C W.a₂ * Xser^2
      + PowerSeries.C W.a₄ * Xser
      + PowerSeries.C W.a₆ := by
  sorry
```

This is already nontrivial: Mathlib has `PowerSeries.order`, `order_mul`, `order_pow`, and basic power-series algebra, but no ready-made Hensel/implicit-function theorem for this curve. The `PowerSeries.Order` API is present and useful, but it does not build the branch for you. citeturn782423view2

Then make the corresponding point over the Laurent/function field of power series:

```lean
abbrev PSFrac (k : Type*) [Field k] :=
  FractionRing (PowerSeries k)

noncomputable def arcPointAtNon2
    (x₀ y₀ : k)
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    (W.baseChange (PSFrac k)).toAffine.Point := by
  refine WeierstrassCurve.Affine.Point.some
    (algebraMap (PowerSeries k) (PSFrac k) (PowerSeries.C x₀ + PowerSeries.X))
    (algebraMap (PowerSeries k) (PSFrac k)
      (W.yAtNon2 x₀ y₀ hP.1 hdy))
    ?_
  -- use `yAtNon2_equation`, mapped into `FractionRing`
  sorry
```

Now instantiate SEAM2 over `PSFrac k`:

```lean
theorem xRep_nsmul_arc
    {n : ℕ}
    (x₀ y₀ : k)
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    SameP1
      ((n • W.arcPointAtNon2 x₀ y₀ hP hdy).xRep)
      ![
        Polynomial.aeval
          (algebraMap (PowerSeries k) (PSFrac k)
            (PowerSeries.C x₀ + PowerSeries.X))
          ((W.Φ (n : ℤ)).map (algebraMap k (PSFrac k))),
        Polynomial.aeval
          (algebraMap (PowerSeries k) (PSFrac k)
            (PowerSeries.C x₀ + PowerSeries.X))
          ((W.ΨSq (n : ℤ)).map (algebraMap k (PSFrac k)))
      ] := by
  -- SEAM2 over `PSFrac k`, plus `baseChange_Φ`, `baseChange_ΨSq`
  sorry
```

Mathlib’s division-polynomial file has the relevant `baseChange_Φ`, `baseChange_ΨSq`, and the definitions of `Φ`/`ΨSq`; it also defines `ΨSq` as `preΨ²` times the 2-torsion factor in the even case. citeturn782423view0

The **missing theorem** is then:

```lean
/--
Formal-local statement:
if `P` is a non-2 point killed by `[n]` and `(n : k) ≠ 0`,
then along the local arc through `P`, the point `[n]R(T)` approaches `O`
with local parameter of order one.
-/
theorem nsmul_arc_tCoord_order_one_at_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0)
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0) :
    localTCoordAtO
      (n • W.arcPointAtNon2 x₀ y₀ hP hdy)
      |>.order = 1 := by
  -- this is exactly the completed-local-ring/formal-group bridge
  sorry
```

Then use the fact that at `O`

\[
x=t^{-2}\cdot\text{unit},
\]

so \(1/x\) has order `2`:

```lean
theorem nsmul_arc_invX_order_two_at_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0)
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0) :
    localInvXCoordAtO
      (n • W.arcPointAtNon2 x₀ y₀ hP hdy)
      |>.order = 2 := by
  have ht :=
    W.nsmul_arc_tCoord_order_one_at_kernel hn hP hdy hker
  -- local relation `1/x = t^2 * unit`
  -- `PowerSeries.order_mul`, `PowerSeries.order_pow`
  sorry
```

Finally compare this with SEAM2. Since `[n]P=O`, the denominator of the projective x-coordinate is `ΨSqₙ(x₀+T)`, and the numerator `Φₙ(x₀+T)` is a unit at `T=0`. Thus:

```lean
theorem ΨSq_order_two_at_non2_kernel
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0)
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0) :
    (Polynomial.evalAtX x₀ (W.ΨSq (n : ℤ))).order = 2 := by
  have hInvX :=
    W.nsmul_arc_invX_order_two_at_kernel hn hP hdy hker

  have hΦunit :
      (Polynomial.evalAtX x₀ (W.Φ (n : ℤ))).order = 0 := by
    -- from pointwise SEAM2 at `P`:
    -- `xRep (n•P) = xRep 0 = ![1,0]`
    -- so `ΨSq.eval x₀ = 0` and `Φ.eval x₀ ≠ 0`
    -- then `order_evalAtX_zero_of_eval_ne_zero`
    sorry

  -- SEAM2 over the formal arc gives:
  -- local `1/x([n]R)` = ΨSq(x₀+T) / Φ(x₀+T).
  -- Since Φ has order 0, ΨSq has order 2.
  exact by
    -- `PowerSeries.order_div` through unit inverse,
    -- or rewrite as multiplication by a unit.
    sorry
```

This is the minimal formal-arc route. It is bounded in the sense that it avoids Picard groups, divisors, and the full global formal group, but it is **still a substantial completed-local-ring development**.

Option **(b)**, the full Weierstrass formal group, is heavier: you must construct the formal parameter at `O`, the two-variable addition law, and associativity. That is reusable but too large for simply closing `preΨ'_separable`.

Option **(c)**, “pointwise SEAM2 + base change only,” does **not** work. Base change preserves equations and roots, but it does not reveal multiplicity. Multiplicity is exactly the missing local-order datum.

---

# 2. Can separability avoid the formal-order statement?

Yes, but only through a **different deep theorem**: a discriminant/resultant formula for the division polynomials.

A usable theorem would look like this:

```lean
theorem preΨ'_discr_ne_zero_of_natCast_ne_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).discr ≠ 0 := by
  -- universal discriminant formula for division polynomials
  sorry
```

Then separability is short:

```lean
theorem preΨ'_separable_of_discr_ne_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k)
    {n : ℕ}
    (hdisc : (W.preΨ' n).discr ≠ 0) :
    (W.preΨ' n).Separable := by
  -- use `Polynomial.resultant_deriv`,
  -- `Polynomial.isUnit_resultant_iff_isCoprime`,
  -- and the definition of `Polynomial.discr`
  sorry
```

Mathlib has `Polynomial.resultant`, `Polynomial.discr`, `Polynomial.resultant_deriv`, and `Polynomial.isUnit_resultant_iff_isCoprime`; these are real APIs, not hypothetical. citeturn116983view0

But what Mathlib does **not** have is the actual universal formula

\[
\operatorname{disc}(\operatorname{pre}\Psi_n)
=
\pm n^{A(n)}\Delta^{B(n)}
\]

with the correct even/odd normalization and the `Ψ₂Sq` factor handled. The division-polynomial docs confirm that Mathlib defines the polynomials and their recurrences, and explicitly notes the bivariate `ωₙ` is still TODO; it does not provide discriminant formulas. citeturn782423view0

So the discriminant route is **not shorter unless you take the discriminant formula as a named theorem**. Proving it from scratch in Lean would be a large EDS/resultant project. It avoids formal geometry, but replaces it with a universal resultant calculation over the Weierstrass coefficient ring. That is probably **at least as hard** as the local-arc route and much less reusable for Weil pairing/Galois-rep infrastructure.

A realistic discriminant seam would be:

```lean
axiom preΨ'_discr_formula
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R)
    (n : ℕ) :
    (W.preΨ' n).discr =
      divisionPolynomialDiscrFactor W n
```

or just the field-level consequence:

```lean
axiom preΨ'_discr_ne_zero_of_natCast_ne_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).discr ≠ 0
```

Then:

```lean
theorem preΨ'_separable_of_natCast_ne_zero_via_discr
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  exact preΨ'_separable_of_discr_ne_zero W
    (preΨ'_discr_ne_zero_of_natCast_ne_zero W hn)
```

---

# 3. Honest tractability ranking

## SEAM2: closeable

The x-only differential-addition theorem and the `xRep(n•P) ~ [Φ, ΨSq]` induction are hard but **closeable**.

They are algebraic: affine group-law formulas, projective `SameP1`, EDS recurrences, `field_simp`, `ring`, and strong induction. Mathlib already has the division-polynomial definitions, small cases, recurrences, `Φ`, `ΨSq`, and base-change lemmas. citeturn782423view0

I would keep pushing this one.

```lean
theorem xRep_nsmul_same_xPair
    (W : WeierstrassCurve k) [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    SameP1
      ((n • (W.toAffine.Point.some x y h : W.toAffine.Point)).xRep)
      ![(W.Φ (n : ℤ)).eval x, (W.ΨSq (n : ℤ)).eval x] := by
  -- closeable algebraic induction
  sorry
```

## SEAM1: deep infrastructure seam

`preΨ'_separable_of_natCast_ne_zero` is not closeable from current Mathlib primitives unless you add either:

1. the formal-local theorem

```lean
theorem ΨSq_order_two_at_non2_kernel :
  ...
```

or

2. the universal/resultant theorem

```lean
theorem preΨ'_discr_ne_zero_of_natCast_ne_zero :
  ...
```

Both are deep. The local theorem is more reusable and conceptually aligned with formal groups, Weil pairing, and Galois representations. The discriminant theorem is more targeted but requires a large universal resultant calculation.

So I would leave this as a named seam:

```lean
axiom preΨ'_separable_of_natCast_ne_zero
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

or, if you want the seam one layer lower:

```lean
axiom ΨSq_order_two_at_non2_kernel
    {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0)
    {x₀ y₀ : k}
    (hP : W.toAffine.Nonsingular x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0)
    (hker :
      n • (W.toAffine.Point.some x₀ y₀ hP : W.toAffine.Point) = 0) :
    (Polynomial.evalAtX x₀ (W.ΨSq (n : ℤ))).order = 2
```

I prefer the higher seam `preΨ'_separable...` for now, because it isolates less infrastructure.

## sub-D coprimality: likely closeable if it is purely polynomial

Assuming “sub-D coprimality” means a concrete gcd/resultant/coprimality statement among explicit polynomials in the modular-curve reductions, it is probably closer to SEAM2 than SEAM1: hard algebra, but bounded.

The Mathlib APIs you want are already there:

```lean
Polynomial.IsCoprime
Polynomial.resultant
Polynomial.isUnit_resultant_iff_isCoprime
Polynomial.resultant_ne_zero
Polynomial.resultant_eq_zero_iff
Polynomial.map
Polynomial.aeval
```

The resultant file has the central APIs, including `resultant`, `discr`, `resultant_deriv`, and `isUnit_resultant_iff_isCoprime`. citeturn116983view0

So the ranking is:

```text
SEAM2 diff-add/x-coordinate formula: closeable.
sub-D coprimality: probably closeable, depending on polynomial size.
SEAM1 separability / ΨSq order two: deep infrastructure seam.
```

---

# Smallest first lemma if you choose to attack SEAM1 anyway

Start here, not with the full formal group:

```lean
theorem exists_yPowerSeries_at_non2
    {k : Type*} [Field k]
    (W : WeierstrassCurve k)
    {x₀ y₀ : k}
    (hcurve : W.toAffine.Equation x₀ y₀)
    (hdy : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) :
    ∃ Y : PowerSeries k,
      PowerSeries.coeff 0 Y = y₀ ∧
      let Xser : PowerSeries k := PowerSeries.C x₀ + PowerSeries.X
      Y^2 + PowerSeries.C W.a₁ * Xser * Y
        + PowerSeries.C W.a₃ * Y
        =
      Xser^3 + PowerSeries.C W.a₂ * Xser^2
        + PowerSeries.C W.a₄ * Xser
        + PowerSeries.C W.a₆ := by
  -- recursive formal implicit-function theorem for this quadratic equation
  sorry
```

If this lemma becomes painful, that is a strong signal to stop and keep SEAM1 named. Everything after it still requires the regularized local `[n]` theorem.
