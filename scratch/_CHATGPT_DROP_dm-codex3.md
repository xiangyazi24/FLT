# Q2972: route audit for order-12 Tate point -> ψ₄ core at `3P`

Target: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.
Namespace: `MazurProof.KubertBridgeN12`.

## Verdict

Yes: the residual

```lean
tatePsi4CoreAt3P b c = 0
```

from

```lean
addOrderOf (tateOriginAffine b c hb) = 12
```

is mathematically the right minimal remaining statement if your downstream algebra already has

```lean
tatePsi4CoreAt3P b c = c * K(b,c)
```

and `c ≠ 0` from order 12. It is exactly the non-`ψ₂` factor of `ψ₄(3P)`.

However, the most Lean-friendly residual may be slightly weaker/more concrete:

```lean
ψ₂(2*(3P)) = 0
```

proved by the affine group law. For `Q=3P=(c,b-c)`, this reduces by `field_simp; ring` to

```text
ψ₂(2Q) = c * K(b,c) / (b - c - c^2)^3.
```

With already-checked `c ≠ 0` and `b-c-c^2 ≠ 0`, this gives `K(b,c)=0` without needing a general division-polynomial theorem for `ψ₄`.

## Short rigorous proof path

Let

```lean
P := tateOriginAffine b c hb
Q := 3 • P
```

and suppose

```lean
hOrder : addOrderOf P = 12.
```

Group-theoretically:

```text
addOrderOf Q = addOrderOf (3P) = 12 / gcd(12,3) = 4.
```

Hence:

```text
4Q = 0,
2Q ≠ 0,
Q ≠ 0.
```

Using the checked affine formula `3P=(c,b-c)`, this says `Q` is the affine point `(c,b-c)` of exact order 4.

For a generalized Weierstrass curve, define

```text
ψ₂(x,y) = 2*y + a₁*x + a₃.
```

For the Tate curve

```text
a₁ = 1-c, a₃ = -b,
ψ₂(x,y) = 2*y + (1-c)*x - b.
```

At `Q=(c,b-c)`:

```text
ψ₂(Q) = 2*(b-c) + (1-c)*c - b
      = b - c - c^2.
```

If `ψ₂(Q)=0`, then `Q=-Q`, so `2Q=0`, contradicting `addOrderOf Q = 4`. Thus

```text
D := b - c - c^2 ≠ 0.
```

Since `4Q=0`, the point `2Q` is 2-torsion:

```text
2Q = -(2Q),
```

so

```text
ψ₂(2Q)=0.
```

There are two equivalent ways to finish:

### Division-polynomial finish

The generalized Weierstrass `ψ₄` factorization is

```text
ψ₄(x,y) = ψ₂(x,y) * Ψ₄core(x),
```

where

```text
Ψ₄core(x) =
  2*x^6 + b₂*x^5 + 5*b₄*x^4 + 10*b₆*x^3 + 10*b₈*x^2
    + (b₂*b₈ - b₄*b₆)*x + (b₄*b₈ - b₆^2).
```

Because `4Q=0`, `ψ₄(Q)=0`. Because `ψ₂(Q)≠0`, the core vanishes:

```text
Ψ₄core(c)=0.
```

That is your residual:

```lean
tatePsi4CoreAt3P b c = 0
```

provided `tatePsi4CoreAt3P` is exactly `Ψ₄core(c)`.

### Direct affine-doubling finish, recommended for Lean

Let

```text
D = b - c - c^2,
L = (2*c^2 - b*c + c - b) / D.
```

Here `L` is the tangent slope at `Q=(c,b-c)`:

```text
L = (3*c^2 + 2*(-b)*c - (1-c)*(b-c)) / (b-c-c^2).
```

Define the double of `Q` by Mathlib’s affine formulas:

```text
x₂ = L^2 + (1-c)*L + b - 2*c,
y₂ = - (L*(x₂-c) + (b-c)) - (1-c)*x₂ + b.
```

Then the key identity is:

```text
ψ₂(x₂,y₂) = c*K(b,c) / D^3.
```

So `ψ₂(2Q)=0`, `D≠0`, and `c≠0` imply `K(b,c)=0`.

This route avoids a generic `ψ₄` theorem and uses only concrete affine `add_self_of_Y_ne` plus a `field_simp; ring` identity.

## Hidden exceptional cases

All hidden cases are accounted for by the hypotheses you listed.

### 1. Singular curve

If the curve is singular, division-polynomial/order arguments can be false or meaningless. Your residual includes

```lean
hDelta : (tateW b c).Δ ≠ 0
```

and the point type is already `WeierstrassCurve.Affine.Point`, i.e. nonsingular affine points plus infinity. This is enough.

### 2. `Q=O`

Impossible. If `Q=3P=O`, then `3P=0`, so the order of `P` divides `3`, contradicting `addOrderOf P=12`.

Lean group lemma shape:

```lean
theorem tate_order12_threeP_ne_zero
    {G : Type*} [AddCommGroup G] {P : G}
    (hOrder : addOrderOf P = 12) : (3 : ℕ) • P ≠ 0 := by
  -- from `addOrderOf P ∣ 3` if `3•P=0`, contradiction with 12
  sorry
```

### 3. `Q` is 2-torsion / vertical tangent denominator zero

Impossible. If `Q=-Q`, then `2Q=0`, so `addOrderOf Q≤2`, contradicting `addOrderOf Q=4`.

In coordinates this is exactly

```lean
b - c - c^2 ≠ 0
```

because

```lean
ψ₂(Q)=2*(b-c)+(1-c)*c-b = b-c-c^2.
```

### 4. `c=0`

Impossible under order 12 once `3P=(c,b-c)` is known. If `c=0`, then

```text
Q = (0,b) = -P,
```

so `3P=-P`, hence `4P=0`, contradicting order 12.

This is exactly the already-checked `c≠0` brick.

### 5. Denominator in doubling formula

The only denominator for doubling `Q` is

```lean
D = b - c - c^2 = ψ₂(Q).
```

It is nonzero by exact order 4 of `Q`. No additional denominator is hidden.

## Recommended Lean residual hierarchy

### Residual C1: group-only order step

```lean
theorem order12_three_nsmul_order4
    {G : Type*} [AddCommGroup G] {P : G}
    (hOrder : addOrderOf P = 12) :
    addOrderOf ((3 : ℕ) • P) = 4 := by
  -- likely one line if `addOrderOf_nsmul` is available:
  -- simpa [hOrder] using addOrderOf_nsmul P 3
  sorry
```

If `addOrderOf_nsmul` is awkward, use only the consequences:

```lean
theorem order12_three_nsmul_four_zero_two_ne_zero
    {G : Type*} [AddCommGroup G] {P : G}
    (hOrder : addOrderOf P = 12) :
    (4 : ℕ) • ((3 : ℕ) • P) = 0 ∧
      (2 : ℕ) • ((3 : ℕ) • P) ≠ 0 := by
  -- `4*(3P)=12P=0`; if `2*(3P)=0`, then `6P=0`, contradicts exact order 12.
  sorry
```

This second statement is often easier than proving `addOrderOf ((3:ℕ)•P)=4`.

### Residual C2: abstract 2-torsion criterion in generalized Weierstrass coordinates

```lean
def tatePsi2 (b c x y : ℚ) : ℚ :=
  2*y + (1-c)*x - b

theorem affine_point_eq_neg_iff_psi2_eq_zero
    {W : WeierstrassCurve.Affine ℚ} {x y : ℚ}
    (h : W.Nonsingular x y) :
    WeierstrassCurve.Affine.Point.some x y h =
      -WeierstrassCurve.Affine.Point.some x y h ↔
      2*y + W.a₁*x + W.a₃ = 0 := by
  -- unfold `Point.neg`, `negY`; equality of `some` points gives `y = negY x y`.
  sorry
```

Specialized Tate version:

```lean
theorem tate_two_torsion_iff_psi2_zero
    {b c x y : ℚ} {h : (tateW b c).Nonsingular x y} :
    WeierstrassCurve.Affine.Point.some x y h =
      -WeierstrassCurve.Affine.Point.some x y h ↔
      tatePsi2 b c x y = 0 := by
  -- use the abstract lemma, then unfold `tateW`, `tatePsi2`
  sorry
```

### Residual C3: concrete doubling identity, Lean-friendly replacement for ψ₄

```lean
def tateDouble3P_D (b c : ℚ) : ℚ :=
  b - c - c^2

def tateDouble3P_L (b c : ℚ) : ℚ :=
  (2*c^2 - b*c + c - b) / tateDouble3P_D b c

def tateDouble3P_x (b c : ℚ) : ℚ :=
  (tateDouble3P_L b c)^2 + (1-c)*(tateDouble3P_L b c) + b - 2*c

def tateDouble3P_y (b c : ℚ) : ℚ :=
  - ((tateDouble3P_L b c) * (tateDouble3P_x b c - c) + (b-c)) -
    (1-c) * tateDouble3P_x b c + b

/-- Pure algebra: `ψ₂(2*(3P))` has numerator equal to the C12 core. -/
theorem tatePsi2_double3P_eq_core_div
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    tatePsi2 b c (tateDouble3P_x b c) (tateDouble3P_y b c) =
      c * tateC12_K b c / (tateDouble3P_D b c)^3 := by
  unfold tatePsi2 tateDouble3P_x tateDouble3P_y tateDouble3P_L tateDouble3P_D tateC12_K
  field_simp [hD]
  ring
```

This identity is the most useful proof brick. It is fully local algebra over `ℚ`.

Then the order-to-core theorem can be stated without mentioning `ψ₄`:

```lean
theorem tate_origin_order12_implies_K_via_double3P
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12)
    (h3P : (3 : ℕ) • tateOriginAffine b c hb = tateP3 b c hb)
    (hc : c ≠ 0)
    (hD : b - c - c^2 ≠ 0) :
    tateC12_K b c = 0 := by
  -- 1. From hOrder, get `2 • (3 • P)` is nonzero 2-torsion.
  -- 2. Rewrite `3 • P` by h3P.
  -- 3. Use affine doubling formula for `tateP3 + tateP3`; denominator hD.
  -- 4. Apply `tate_two_torsion_iff_psi2_zero`.
  -- 5. Rewrite by `tatePsi2_double3P_eq_core_div hD`.
  -- 6. Since `c≠0` and `D≠0`, conclude `K=0`.
  sorry
```

### Residual C4: original ψ₄-core residual

If you prefer to keep the ψ₄ formulation, isolate only this theorem:

```lean
theorem tate_origin_order12_implies_psi4_core_at_3P
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12)
    (h3P : (3 : ℕ) • tateOriginAffine b c hb = tateP3 b c hb)
    (hD : b - c - c^2 ≠ 0) :
    tatePsi4CoreAt3P b c = 0 := by
  -- Q=3P has order 4, so ψ4(Q)=0.
  -- ψ2(Q)=D≠0.
  -- ψ4(Q)=ψ2(Q)*tatePsi4CoreAt3P(b,c).
  sorry
```

This is mathematically cleaner but depends on a division-polynomial theorem that may not exist in Mathlib for generalized Weierstrass affine points. If that theorem is not already present, C3 is lower-risk.

## Bottom line

*Mathematical truth:* `addOrderOf(P)=12` implies `Q=3P` has exact order 4, hence `ψ₄(Q)=0` and `ψ₂(Q)≠0`, so the `ψ₄` core at `Q` vanishes. No exceptional case remains after `hDelta`, `c≠0`, and `b-c-c^2≠0`.

*Lean route:* prove the concrete affine doubling identity

```lean
tatePsi2_double3P_eq_core_div
```

first. It is just `field_simp [hD]; ring`, and it replaces a possibly missing general division-polynomial library theorem with a local computation tailored to the Tate curve.
