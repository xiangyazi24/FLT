# Q500 / dm4 — Can we bypass `(X₀-X₁)^3` divisibility by defining the Weierstrass formal group directly?

## Executive answer

For a **genuine Mathlib `FormalGroup K`**, this shortcut is **not shorter** than the `(X₀-X₁)^3` divisibility / normalization route.

It is shorter only if the target is a **finite jet** or a **low-order computation** such as `lin_coeff_X`, `lin_coeff_Y`, or a first-order tangent calculation. It is not a viable shortcut for constructing an actual inhabitant of

```lean
FormalGroup K
```

because Mathlib's `FormalGroup.assoc` field is an **exact equality of full multivariate power series**, not an equality modulo degree `N`.

The key misconception in the proposed shortcut is:

> "Associativity is a finite check modulo sufficiently high degree."

That is false for formal group laws in Mathlib and false mathematically for full formal power series. A finite truncation proves associativity only in a truncated Artin quotient, not in `MvPowerSeries` itself.

## Mathlib API checked

The repo pins Mathlib at:

```toml
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

At that revision, `Mathlib/RingTheory/FormalGroup/Basic.lean` defines:

```lean
structure FormalGroup where
  toPowerSeries : MvPowerSeries (Fin 2) R
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)
```

So to build `FormalGroup K`, you must prove an equality in

```lean
MvPowerSeries (Fin 3) K
```

not a truncated equality.

The substitution API in `Mathlib/RingTheory/MvPowerSeries/Substitution.lean` is also full-power-series substitution:

```lean
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S
```

with lemmas such as:

```lean
theorem subst_add
theorem subst_sub
theorem subst_mul
theorem subst_pow
theorem coeff_subst
```

Again, this is exact API, not a finite-jet API.

## Why the affine formula route is not a shortcut

The affine chord formula wants to use

```text
x(t) = t / w(t),
y(t) = -1 / w(t),
```

where, for the local parameter at infinity,

```text
w(t) = t^3 u(t),       u(0) = 1.
```

Thus

```text
x(t) = 1 / (t^2 u(t)),
y(t) = -1 / (t^3 u(t)).
```

These are Laurent series, not ordinary `PowerSeries` / `MvPowerSeries`. The final formal group law

```text
F(t₁,t₂) = t(P(t₁) + P(t₂))
```

is an ordinary power series, but the intermediate affine slope/intercept formulas live in Laurent/rational expressions and then cancel.

So the affine formula does not remove the cancellation problem; it merely moves it from projective `addXYZ` normalization to Laurent-series cancellation.

In Lean, unless you introduce a robust Laurent/Hahn-series layer and prove the cancellation back into `MvPowerSeries`, this is probably **longer** than the projective route.

## Why a finite Silverman table is insufficient

Silverman's displayed expansion

```text
F(T₁,T₂) = T₁ + T₂ - a₁T₁T₂ - a₂(T₁²T₂ + T₁T₂²) - ...
```

is only the beginning of an infinite power series. If we define a finite polynomial/truncation from the table, say

```lean
def F_trunc : MvPowerSeries (Fin 2) K :=
  X₀ + X₁ - C a₁ * X₀ * X₁ - C a₂ * (X₀^2 * X₁ + X₀ * X₁^2) + ...
```

then `zero_constantCoeff`, `lin_coeff_X`, and `lin_coeff_Y` are easy. But `assoc` will normally fail as an exact equality, because the omitted higher terms are exactly what cancel the higher-degree associator.

Finite checking proves only statements like

```text
assoc holds modulo total degree ≤ N
```

not

```lean
F.subst ![F.subst ![Y₀,Y₁],Y₂]
  = F.subst ![Y₀,F.subst ![Y₁,Y₂]]
```

in `MvPowerSeries (Fin 3) K`.

There is no finite `N` that determines a one-dimensional formal group law over a field. For example, over a characteristic-zero field, the coordinate changes

```text
φ(T) = T + c T^(N+1)
```

produce formal group laws

```text
Fφ(X,Y) = φ⁻¹(φ(X) + φ(Y))
```

which agree with the additive formal group law through degree `N` but differ in higher degree. Thus finite jets cannot certify a full formal group law.

## Can we define `F` coefficient-by-coefficient?

Technically, yes: `MvPowerSeries (Fin 2) K` is just a coefficient function

```lean
def MvPowerSeries (σ : Type*) (R : Type*) := (σ →₀ ℕ) → R
```

so one can define

```lean
def F : MvPowerSeries (Fin 2) K := fun d =>
  -- coefficient indexed by d : Fin 2 →₀ ℕ
  ...
```

or pattern-match on

```lean
d (0 : Fin 2), d (1 : Fin 2)
```

for explicitly known low-degree coefficients.

But this only moves the hard part. To make a `FormalGroup`, you must prove:

```lean
F.subst ![F.subst ![Y₀, Y₁], Y₂]
  = F.subst ![Y₀, F.subst ![Y₁, Y₂]]
```

That proof is coefficientwise infinite. It requires showing every coefficient of the associator is zero. There are two realistic ways to do this:

1. prove the coefficient recursion is exactly the one obtained from the elliptic curve group law, then inherit associativity from the curve group law; or
2. define the coefficients recursively so that the associator vanishes at every degree, and then prove this recursion matches the Weierstrass/Silverman formal group.

Both are substantially larger than proving one localized divisibility/cancellation statement for the projective formula.

## The finite-check idea would require a different structure

If the immediate goal is only a finite-order calculation, define a jet structure instead of using Mathlib's `FormalGroup`:

```lean
structure FormalGroupJet (R : Type*) [CommRing R] (N : ℕ) where
  F : MvPolynomial (Fin 2) R       -- or truncated MvPowerSeries
  zero_constantCoeff : ...
  lin_coeff_X : ...
  lin_coeff_Y : ...
  assoc_mod_degree : ...           -- modulo total degree > N
```

Then the Silverman table route is attractive. It is excellent for proving low-order facts like:

```lean
coeff (single 0 1) F = 1
coeff (single 1 1) F = 1
coeff (single 0 1 + single 1 1) F = -a₁
```

But this does not produce a value of type

```lean
FormalGroup K
```

and therefore will not plug into Mathlib's existing `FormalGroup` API.

## Comparison with the `(X₀-X₁)^3` divisibility route

### Divisibility/projective route

Hard point:

```lean
(X₀ - X₁)^3 ∣ addX/addY/addZ numerator pieces
```

or some equivalent normalization/cancellation statement.

Advantages:

* It keeps everything in ordinary `MvPowerSeries` / polynomial expressions.
* It is tied directly to Mathlib's projective addition formulas.
* Once the normalized expression is identified with actual curve addition, associativity should ultimately come from the elliptic curve group law rather than an infinite coefficient proof.
* The hard lemma is local and algebraic.

### Direct Silverman coefficient route

Hard points:

* need an infinite coefficient definition, not merely the displayed first terms;
* need exact associativity of the infinite power series;
* need a proof that the constructed series is the Weierstrass formal group law, not just some formal group law with the same low-degree terms;
* if using affine formulas, need Laurent/rational cancellation anyway.

Verdict: this is likely much longer for a genuine `FormalGroup`.

## Recommended practical route

### If the goal is `W.formalGroup : FormalGroup K`

Stay with the projective/normalization route. Avoid `IsCoprime` from the previous question, because it is the wrong notion in the local ring. Instead use one of:

1. direct factorization of the concrete normalized numerator;
2. a custom `δ`-adic divisibility lemma for `δ = X₀ - X₁`;
3. a coordinate-change argument `U = X₀ - X₁`, `V = X₁`, reducing divisibility by `δ` to divisibility by a coordinate variable `U` and using `MvPowerSeries.X_pow_dvd_iff`.

The third route is probably the cleanest Mathlib-aligned approach if direct `ring` factorization is too large.

### If the goal is only the tangent bridge / linear coefficient

Do not build the full `FormalGroup` yet. Define or prove only the required jet-level facts:

```lean
F = T₁ + T₂ + terms of total degree ≥ 2
```

or explicitly:

```lean
coeff (single 0 1) F = 1
coeff (single 1 1) F = 1
```

A Silverman-table finite truncation is useful here. But call it a jet/truncation theorem, not `FormalGroup`.

## Lean skeleton for the safe finite-jet approach

A minimal finite-jet object could look like:

```lean
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc

open MvPowerSeries Finsupp

noncomputable section

variable {K : Type*} [Field K]

abbrev R₂ := MvPowerSeries (Fin 2) K

local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : R₂)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : R₂)

-- Low-order Silverman polynomial, not a full formal group law.
def WeierstrassFJet2 (a₁ : K) : R₂ :=
  X₀ + X₁ - MvPowerSeries.C a₁ * X₀ * X₁

example (a₁ : K) : (WeierstrassFJet2 (K := K) a₁).constantCoeff = 0 := by
  simp [WeierstrassFJet2]

example (a₁ : K) :
    (WeierstrassFJet2 (K := K) a₁).coeff (single (0 : Fin 2) 1) = 1 := by
  -- likely `simp [WeierstrassFJet2, coeff_index_single_X, X, monomial_mul_monomial]`
  sorry

example (a₁ : K) :
    (WeierstrassFJet2 (K := K) a₁).coeff (single (1 : Fin 2) 1) = 1 := by
  -- same style
  sorry
```

This is useful for local coefficient computations, but intentionally does **not** attempt:

```lean
def bad : FormalGroup K := ...
```

because exact associativity is unavailable from a finite truncation.

## Bottom line

*Defining a finite Silverman expansion is shorter for coefficient/jet lemmas.*

*It is not shorter for constructing `W.formalGroup : FormalGroup K`.* The full `FormalGroup` route still needs an exact infinite associativity proof. The projective normalization route remains the better path because it ties the power series to the actual elliptic curve addition law and localizes the hard algebra to the normalization/divisibility step.
