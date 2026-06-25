# Q594 / dm4 — Explicit leading computation for `normalizedAddY`

## Executive answer

With the conventions stated in the question,

```lean
normalizedAddY = formalAddY / (X₀ - X₁)^3
formalAddY     = Projective.addY(W', P(X₀), P(X₁))
P(t)           = [t, -1, w(t)]
```

the explicit Mathlib-formula computation gives

```text
formalAddY = (X₀ - X₁)^3 * (1 + higher terms).
```

Therefore

```lean
constantCoeff normalizedAddY = 1
```

not `-1`.

The `-1` appears if either:

1. you divide by `(X₁ - X₀)^3`, since `(X₁-X₀)^3 = -(X₀-X₁)^3`; or
2. you accidentally use `negAddY` instead of `addY`. Indeed `negAddY` has leading term `-(X₀-X₁)^3`.

This sign matters, but the formal group law still has the expected leading term:

```text
normalizedAddX = -(X₀ + X₁) + O(total degree ≥ 2)
normalizedAddY =  1 + O(total degree ≥ 1)
F = -normalizedAddX * normalizedAddY⁻¹ = X₀ + X₁ + O(total degree ≥ 2).
```

So the constant coefficient of `F` is `0`, and the two linear coefficients are both `1`.

## Mathlib formulas used

From `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`, the relevant definitions are:

```lean
def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]
```

and

```lean
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z
```

Therefore

```text
addY(P,Q) = -negAddY(P,Q) - a₁*addX(P,Q) - a₃*addZ(P,Q).
```

The raw `negAddY` formula is:

```text
negAddY(P,Q) =
  -3*Px^2*Qx*Qy + 3*Px*Qx^2*Py
  - Py^2*Qy*Qz + Py*Qy^2*Pz
  + a₁*Px*Qy^2*Pz - a₁*Qx*Py^2*Qz
  - a₂*Px^2*Qy*Qz + a₂*Qx^2*Py*Pz
  + 2*a₂*Px*Qx*Py*Qz - 2*a₂*Px*Qx*Qy*Pz
  - a₃*Py^2*Qz^2 + a₃*Qy^2*Pz^2
  + a₄*Px*Py*Qz^2 - 2*a₄*Px*Qy*Pz*Qz
  + 2*a₄*Qx*Py*Pz*Qz - a₄*Qx*Qy*Pz^2
  + 3*a₆*Py*Pz*Qz^2 - 3*a₆*Qy*Pz^2*Qz.
```

The raw `addX` and `addZ` formulas are the Mathlib ones. The only fact about `addY` needed for the leading sign is the identity above:

```text
addY = -negAddY - a₁ addX - a₃ addZ.
```

## Formal point expansion

The formal point is

```text
P(t) = [t, -1, w(t)]
```

with `w` satisfying

```text
w = t^3 + a₁*t*w + a₂*t^2*w + a₃*w^2 + a₄*t*w^2 + a₆*w^3.
```

Thus

```text
w(t) = t^3
     + a₁*t^4
     + (a₁^2 + a₂)*t^5
     + (a₁^3 + 2*a₁*a₂ + a₃)*t^6
     + (a₁^4 + 3*a₁^2*a₂ + 3*a₁*a₃ + a₂^2 + a₄)*t^7
     + O(t^8).
```

For the leading computation through total degree `6`, it is enough to use

```text
w(t) = t^3 + a₁*t^4 + (a₁^2+a₂)*t^5 + (a₁^3+2a₁a₂+a₃)*t^6 + O(t^7).
```

Set

```text
x = X₀,
y = X₁,
δ = X₀ - X₁,
w₀ = w(X₀),
w₁ = w(X₁),
P = [X₀,-1,w₀],
Q = [X₁,-1,w₁].
```

## Explicit component expansions

After substituting `Py = Qy = -1`, `Pz = w₀`, `Qz = w₁`, the Mathlib formulas give the following leading terms.

### `addZ`

```text
addZ(P,Q) = -δ^3*(X₀+X₁)^3 + O(total degree ≥ 7).
```

So `addZ` starts only in total degree `6`.

### `addX`

```text
addX(P,Q)
  = -δ^3 * (
      (X₀+X₁)
    + a₁*(X₀^2 + X₀X₁ + X₁^2)
    + (a₁^2+a₂)*(X₀^3 + X₀^2X₁ + X₀X₁^2 + X₁^3)
    + O(total degree ≥ 4 inside the parentheses)
    ).
```

In particular,

```text
normalizedAddX = addX/δ^3 = -(X₀+X₁) + O(total degree ≥ 2).
```

### `negAddY`

```text
negAddY(P,Q)
  = -δ^3 * (
      1
    + a₂*(X₀^2 + X₀X₁ + X₁^2)
    + a₁*a₂*(X₀^3 + X₀^2X₁ + X₀X₁^2 + X₁^3)
    + O(total degree ≥ 4 inside the parentheses)
    ).
```

This is probably where the expected `-1` came from: `negAddY/δ^3` has constant coefficient `-1`.

### `addY`

But Mathlib's actual `addY` is

```text
addY = -negAddY - a₁*addX - a₃*addZ.
```

Combining the previous expansions gives:

```text
addY(P,Q)
  = δ^3 * (
      1
    + a₁*(X₀+X₁)
    + (a₁^2+a₂)*(X₀^2 + X₀X₁ + X₁^2)
    + (a₁^3+2*a₁*a₂)*(X₀^3 + X₀^2X₁ + X₀X₁^2 + X₁^3)
    + a₃*(X₀+X₁)^3
    + O(total degree ≥ 4 inside the parentheses)
    ).
```

Equivalently, written without the shorthand `δ`:

```text
addY(P,Q)
  = (X₀-X₁)^3
  + a₁*(X₀-X₁)^3*(X₀+X₁)
  + (a₁^2+a₂)*(X₀-X₁)^3*(X₀^2+X₀X₁+X₁^2)
  + O(total degree ≥ 6).
```

Including the total-degree-6 terms:

```text
addY(P,Q)
  = (X₀-X₁)^3 * (
      1
    + a₁*(X₀+X₁)
    + (a₁^2+a₂)*(X₀^2 + X₀X₁ + X₁^2)
    + (a₁^3+2*a₁*a₂)*(X₀^3 + X₀^2X₁ + X₀X₁^2 + X₁^3)
    + a₃*(X₀+X₁)^3
    )
  + O(total degree ≥ 7).
```

Thus, with divisor `(X₀-X₁)^3`, the quotient has leading expansion

```text
normalizedAddY
  = 1
  + a₁*(X₀+X₁)
  + (a₁^2+a₂)*(X₀^2 + X₀X₁ + X₁^2)
  + O(total degree ≥ 3).
```

So

```text
constantCoeff normalizedAddY = 1.
```

If instead the quotient is defined by dividing by `(X₁-X₀)^3`, then the expansion becomes

```text
addY(P,Q) = -(X₁-X₀)^3 * (1 + higher terms),
```

and then the constant coefficient is `-1`.

## Lean consequence: fix the sign target

If your Lean definition is literally:

```lean
formalAddY = Projective.addY(W', P X₀, P X₁)
formalAddY = (X₀ - X₁)^3 * normalizedAddY
```

then the theorem should be:

```lean
theorem normalizedAddY_constantCoeff :
    MvPowerSeries.constantCoeff normalizedAddY = 1 := by
  ...
```

not `= -1`.

If your current intended theorem is:

```lean
MvPowerSeries.constantCoeff normalizedAddY = -1
```

then one of these is true:

1. your divisor is actually `(X₁-X₀)^3`; or
2. your `formalAddY` is actually Mathlib's `negAddY`; or
3. the target sign is wrong.

## Minimal coefficient proof for `normalizedAddY_constantCoeff`

Let

```lean
δ = X₀ - X₁
hY : formalAddY = δ^3 * normalizedAddY
```

and prove the degree-3 coefficient calculation:

```lean
coeff_X0_cubed_formalAddY :
  MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) formalAddY = 1
```

This is exactly the leading term above: the coefficient of `X₀^3` in `(X₀-X₁)^3` is `1`.

Then compare coefficients in `hY`:

```lean
have hcoeff := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)) hY
```

The right side reduces to the constant coefficient of `normalizedAddY`, because the only way to get the monomial `X₀^3` from

```text
(X₀-X₁)^3 * normalizedAddY
```

is the `X₀^3` term of `(X₀-X₁)^3` times the constant term of `normalizedAddY`.

Lean skeleton:

```lean
open MvPowerSeries Finsupp

local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)
local notation "δ"  => (X₀ - X₁)

-- Proved by expanding Mathlib's `addY = -negAddY - a₁*addX - a₃*addZ`
-- after substituting `P(X₀), P(X₁)` and using `w = X^3 + O(X^4)`.
lemma coeff_X0_cubed_formalAddY :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) formalAddY = 1 := by
  -- `rw [formalAddY, Projective.addY, Projective.negY_eq, ...]`
  -- all terms except the cubic part of `-negAddY` vanish at this coefficient.
  -- The surviving contribution is `X₀^3` from `(X₀-X₁)^3`.
  sorry

lemma coeff_X0_cubed_delta_pow_mul (G : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) (δ^3 * G)
      = MvPowerSeries.constantCoeff G := by
  -- Use `MvPowerSeries.coeff_mul`.
  -- Only the antidiagonal pair `(single 0 3, 0)` contributes.
  -- Coefficients of `δ^3` at all other monomials that could combine
  -- to `single 0 3` are zero/impossible except `single 0 3`.
  sorry

theorem normalizedAddY_constantCoeff
    (hY : formalAddY = δ^3 * normalizedAddY) :
    MvPowerSeries.constantCoeff normalizedAddY = 1 := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)) hY
  rw [coeff_X0_cubed_formalAddY, coeff_X0_cubed_delta_pow_mul] at h
  exact h.symm
```

If using divisor `(X₁-X₀)^3`, replace `δ` by `X₁-X₀`; then the analogous coefficient of `X₀^3` in `(X₁-X₀)^3` is `-1`, so the result is `-1`.

## Constant coefficient of `F`

From the expansion of `addX`:

```text
normalizedAddX = -(X₀+X₁) + O(total degree ≥ 2),
```

so

```lean
constantCoeff normalizedAddX = 0.
```

Also

```lean
constantCoeff normalizedAddY = 1
```

so `normalizedAddY` is a unit and

```lean
constantCoeff normalizedAddY⁻¹ = 1.
```

Therefore

```text
constantCoeff F
= constantCoeff (-normalizedAddX * normalizedAddY⁻¹)
= -0 * 1
= 0.
```

Lean skeleton:

```lean
theorem formalGroupLaw_constantCoeff
    (hX0 : MvPowerSeries.constantCoeff normalizedAddX = 0)
    (hY0 : MvPowerSeries.constantCoeff normalizedAddY = 1) :
    MvPowerSeries.constantCoeff (-normalizedAddX * normalizedAddY⁻¹) = 0 := by
  simp [map_mul, hX0, hY0]
```

Over a field, `constantCoeff_inv` rewrites the inverse constant coefficient:

```lean
@[simp] theorem MvPowerSeries.constantCoeff_inv (φ : MvPowerSeries σ k) :
  constantCoeff φ⁻¹ = (constantCoeff φ)⁻¹
```

so `simp [hY0]` should finish.

## Linear coefficients of `F`

The leading expansions are:

```text
normalizedAddX = -(X₀+X₁) + O(total degree ≥ 2)
normalizedAddY = 1 + a₁*(X₀+X₁) + O(total degree ≥ 2)
normalizedAddY⁻¹ = 1 - a₁*(X₀+X₁) + O(total degree ≥ 2).
```

Since `normalizedAddX` has zero constant term, the linear part of

```text
-normalizedAddX * normalizedAddY⁻¹
```

only sees the constant term of `normalizedAddY⁻¹`, which is `1`. Hence

```text
F = X₀ + X₁ + O(total degree ≥ 2).
```

So:

```lean
coeff (single 0 1) F = 1
coeff (single 1 1) F = 1
```

A direct coefficient proof can use these helper facts:

```lean
constantCoeff normalizedAddX = 0
coeff (single 0 1) normalizedAddX = -1
coeff (single 1 1) normalizedAddX = -1
constantCoeff normalizedAddY = 1
constantCoeff normalizedAddY⁻¹ = 1
```

Then coefficient multiplication at a linear monomial gives:

```text
coeff_X₀(normalizedAddX * normalizedAddY⁻¹)
  = coeff_X₀(normalizedAddX)*constantCoeff(normalizedAddY⁻¹)
    + constantCoeff(normalizedAddX)*coeff_X₀(normalizedAddY⁻¹)
  = (-1)*1 + 0*... = -1.
```

After the outer negation, the result is `1`. The `X₁` proof is identical.

Lean skeleton:

```lean
lemma coeff_X0_mul_of_left_const_zero {A B : MvPowerSeries (Fin 2) K}
    (hA0 : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (A * B)
      = MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) A
          * MvPowerSeries.constantCoeff B := by
  -- Expand `MvPowerSeries.coeff_mul` at `single 0 1`.
  -- The antidiagonal has only `(0,single 0 1)` and `(single 0 1,0)`.
  -- The first term vanishes by `hA0` if arranged appropriately.
  sorry

theorem formalGroupLaw_lin_coeff_X
    (hA0 : MvPowerSeries.constantCoeff normalizedAddX = 0)
    (hAX : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) normalizedAddX = -1)
    (hY0 : MvPowerSeries.constantCoeff normalizedAddY = 1) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
      (-normalizedAddX * normalizedAddY⁻¹) = 1 := by
  have hBinv0 : MvPowerSeries.constantCoeff normalizedAddY⁻¹ = 1 := by
    simp [hY0]
  rw [map_neg]
  -- use the multiplication helper
  -- coefficient of product is `-1`, then negation gives `1`.
  sorry
```

Alternatively, use the specialization route from Q548:

```text
F(T,0)=T  ⇒ coeff X₀ F = 1
F(0,T)=T  ⇒ coeff X₁ F = 1.
```

That route is more geometric and avoids proving multiplication-at-linear-monomial lemmas, but the expansion above is already enough for the coefficients.

## Recommended corrected theorem targets

With `δ = X₀-X₁`:

```lean
normalizedAddY_constantCoeff : constantCoeff normalizedAddY = 1
formalGroupLaw_constantCoeff : constantCoeff formalGroupLaw = 0
formalGroupLaw_lin_coeff_X  : coeff (single 0 1) formalGroupLaw = 1
formalGroupLaw_lin_coeff_Y  : coeff (single 1 1) formalGroupLaw = 1
```

With `δ = X₁-X₀`:

```lean
normalizedAddY_constantCoeff : constantCoeff normalizedAddY = -1
normalizedAddX_lin_X        : coeff (single 0 1) normalizedAddX = 1
normalizedAddX_lin_Y        : coeff (single 1 1) normalizedAddX = 1
```

and the final `F = -normalizedAddX * normalizedAddY⁻¹` still has linear coefficients `1`.

## Bottom line

The explicit leading computation is:

```text
Projective.addY(P(X₀), P(X₁))
  = (X₀-X₁)^3 * (1 + a₁(X₀+X₁) + O(total degree ≥ 2)).
```

So the quotient by `(X₀-X₁)^3` has constant coefficient `+1`. If Lean is asking you to prove `-1`, the sign convention of the divisor or the use of `negAddY` vs `addY` is mismatched.
