# Q479 / dm4 — `MvPowerSeries (Fin 2) K`, UFD, and coprimality

## Executive answer

For the intended divisibility step

```lean
(X₀ - X₁)^3 ∣ addZ * X₀^3 * X₁^3  ⟹  (X₀ - X₁)^3 ∣ addZ
```

do **not** try to use Mathlib's `IsCoprime` between `(X₀ - X₁)^3` and `X₀^3 * X₁^3`. In Mathlib, `IsCoprime a b` means a Bézout/comaximal identity `∃ u v, u * a + v * b = 1`. In the local ring `K⟦X₀,X₁⟧ = MvPowerSeries (Fin 2) K`, both `(X₀ - X₁)^3` and `X₀^3 * X₁^3` have zero constant coefficient, so they lie in the maximal ideal. Hence they are **not** `IsCoprime`.

Mathematically, `K⟦X₀,X₁⟧` is a UFD and `(X₀ - X₁)` has no common prime factor with `X₀ X₁`. But at the pinned Mathlib revision in this repo, the multivariate UFD API does not appear to be available. Mathlib has enough to know `MvPowerSeries` has no zero divisors over a domain, but not enough out-of-the-box to run a UFD/no-common-prime-factor cancellation argument in `MvPowerSeries (Fin 2) K`.

## Repo / Mathlib revision checked

`FLT/lakefile.toml` pins:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

I inspected the relevant Mathlib files at that revision.

## Grep / API findings

### 1. `MvPowerSeries` basic ring/domain API

Relevant files:

```text
Mathlib/RingTheory/MvPowerSeries/Basic.lean
Mathlib/RingTheory/MvPowerSeries/NoZeroDivisors.lean
Mathlib/RingTheory/MvPowerSeries/Inverse.lean
```

`MvPowerSeries.Basic` defines

```lean
def MvPowerSeries (σ : Type*) (R : Type*) := (σ →₀ ℕ) → R
```

and provides the usual algebraic structure:

```lean
instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R)
instance [CommRing R] : CommRing (MvPowerSeries σ R)
```

It also defines the variables and the important monomial divisibility tests:

```lean
def X (s : σ) : MvPowerSeries σ R

 theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
   (X s : MvPowerSeries σ R) ^ n ∣ φ ↔
     ∀ m : σ →₀ ℕ, m s < n → coeff m φ = 0

 theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
   (X s : MvPowerSeries σ R) ∣ φ ↔
     ∀ m : σ →₀ ℕ, m s = 0 → coeff m φ = 0
```

`MvPowerSeries.NoZeroDivisors` gives:

```lean
instance [Semiring R] [NoZeroDivisors R] : NoZeroDivisors (MvPowerSeries σ R)
```

and also:

```lean
lemma X_mem_nonzeroDivisors {i : σ} :
    X i ∈ (MvPowerSeries σ R)⁰
```

So for `[Field K]`, the ring

```lean
MvPowerSeries (Fin 2) K
```

has `CommRing` and `NoZeroDivisors`. If a proof needs an explicit `IsDomain`, try adding the local instance

```lean
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

open MvPowerSeries

variable (K : Type*) [Field K]

local instance : IsDomain (MvPowerSeries (Fin 2) K) :=
  NoZeroDivisors.to_isDomain _
```

I did not find a dedicated declaration named like `MvPowerSeries.IsDomain`; the available multivariate file gives `NoZeroDivisors`, not a named `IsDomain` theorem.

### 2. UFD API

Searches for multivariate UFD instances did **not** find an instance of the form

```lean
UniqueFactorizationMonoid (MvPowerSeries σ R)
```

or, more specifically,

```lean
UniqueFactorizationMonoid (MvPowerSeries (Fin 2) K)
```

What Mathlib does have is univariate `PowerSeries` UFD/DVR API:

```lean
-- Mathlib/RingTheory/PowerSeries/Inverse.lean
instance : UniqueFactorizationMonoid k⟦X⟧
instance : IsDiscreteValuationRing k⟦X⟧
```

for `[Field k]`, and also:

```lean
-- Mathlib/RingTheory/PowerSeries/Ideal.lean
instance [IsPrincipalIdealRing R] [IsDomain R] : UniqueFactorizationMonoid R⟦X⟧
```

The same `PowerSeries/Ideal.lean` file explicitly says:

```lean
## TODO
Prove noetherianity of `MvPowerSeries` in finitely many variables.
```

That is strong evidence that the finite-variable multivariate UFD route is not currently packaged in Mathlib at this revision.

### 3. Coprimality API

Relevant files:

```text
Mathlib/RingTheory/Coprime/Basic.lean
Mathlib/RingTheory/Coprime/Lemmas.lean
Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean
```

`IsCoprime` is generic, not power-series-specific:

```lean
def IsCoprime (x y : R) : Prop :=
  ∃ a b, a * x + b * y = 1
```

The key cancellation lemmas are:

```lean
theorem IsCoprime.dvd_of_dvd_mul_right
    (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y

theorem IsCoprime.dvd_of_dvd_mul_left
    (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z
```

and power closure exists:

```lean
theorem IsCoprime.pow_left  (H : IsCoprime x y) : IsCoprime (x ^ m) y
theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n)
theorem IsCoprime.pow       (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n)
```

But these do **not** apply here because the required `IsCoprime` fact is false.

There is also UFD-style Euclid API:

```lean
namespace UniqueFactorizationMonoid

 theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
     (h : ∀ ⦃d⦄, d ∣ a → d ∣ c → ¬Prime d) : a ∣ b * c → a ∣ b

 theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
     (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : a ∣ b * c → a ∣ c
```

This is the *mathematically right shape*, but it requires a `UniqueFactorizationMonoid` instance for the ambient ring, which Mathlib does not appear to provide for `MvPowerSeries (Fin 2) K`.

## Answers to the five questions

### (a) Is `MvPowerSeries (Fin 2) K` a UFD when `K` is a field?

Mathematically: **yes**. `K[[X₀,X₁]]` is a regular local ring / formal power series ring over a field, hence a UFD.

Lean/Mathlib at this repo's pinned revision: **not available as an instance**, as far as the grep/direct inspection shows.

### (b) Does Mathlib have `MvPowerSeries.IsDomain` or `MvPowerSeries.UniqueFactorizationDomain`?

`MvPowerSeries.NoZeroDivisors` exists:

```lean
instance [Semiring R] [NoZeroDivisors R] : NoZeroDivisors (MvPowerSeries σ R)
```

I did **not** find a named `MvPowerSeries.IsDomain` theorem or instance. If needed, use:

```lean
local instance : IsDomain (MvPowerSeries (Fin 2) K) :=
  NoZeroDivisors.to_isDomain _
```

I also did **not** find a `UniqueFactorizationMonoid (MvPowerSeries σ R)` instance. The UFD/DVR results I found are for univariate `PowerSeries`, not multivariate `MvPowerSeries`.

### (c) Does Mathlib have `IsCoprime` for power series?

Mathlib has generic `IsCoprime` for any `CommSemiring`, so it can be used in power series rings. But it is the **Bézout/comaximal** notion:

```lean
IsCoprime x y = ∃ a b, a * x + b * y = 1
```

There is no special power-series-specific `IsCoprime` API that turns UFD-relative-prime facts into `IsCoprime` in `MvPowerSeries`.

### (d) Can we prove `IsCoprime (X₀-X₁)^3 (X₀^3·X₁^3)` in `MvPowerSeries`?

No. That proposition is false.

Reason: in `K[[X₀,X₁]]`, the ring is local and units are exactly the series with nonzero constant coefficient. Both

```lean
(X₀ - X₁)^3
X₀^3 * X₁^3
```

have constant coefficient `0`. If there were `a b` with

```lean
a * (X₀ - X₁)^3 + b * (X₀^3 * X₁^3) = 1
```

then applying `constantCoeff` would give `0 = 1`, contradiction.

Lean skeleton:

```lean
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Coprime.Lemmas

open MvPowerSeries

noncomputable section

variable {K : Type*} [Field K]

abbrev R₂ := MvPowerSeries (Fin 2) K

local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : R₂)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : R₂)

example : ¬ IsCoprime ((X₀ - X₁)^3) (X₀^3 * X₁^3) := by
  rintro ⟨a, b, h⟩
  have hcc := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K)) h
  -- `simp` should reduce the left side to `0` and the right side to `1`.
  simpa using hcc
```

If `simp` needs help in the local file, add:

```lean
  simp [map_add, map_mul, map_sub, map_pow] at hcc
```

or explicitly rewrite the constant coefficients of `X₀` and `X₁` using `MvPowerSeries.constantCoeff_X`.

### (e) Can a non-zero-divisor cancellation lemma replace coprimality?

Not for the stated shape.

From

```lean
a ∣ b * c
```

and `c` a non-zero-divisor, one **cannot** conclude `a ∣ b`. Counterexample in `ℤ`: `6 ∣ 2 * 3`, and `3` is a non-zero-divisor, but `6 ∤ 2`.

Regular cancellation works for shapes where the same regular factor appears on both sides, e.g.

```lean
a * c ∣ b * c  ⟹  a ∣ b
```

under suitable cancellativity / non-zero-divisor hypotheses. But your hypothesis has only

```lean
(X₀ - X₁)^3 ∣ addZ * X₀^3 * X₁^3
```

not

```lean
(X₀ - X₁)^3 * X₀^3 * X₁^3 ∣ addZ * X₀^3 * X₁^3.
```

So `mul_dvd_cancel` / regular-factor cancellation is not enough.

## Recommended Lean route

Do not aim for `IsCoprime`. The viable routes are:

### Route 1: direct factorization

Best if the expression is concrete.

Prove directly:

```lean
∃ q : MvPowerSeries (Fin 2) K, addZ = (X₀ - X₁)^3 * q
```

or, at the polynomial/CAS layer before coercing into `MvPowerSeries`, factor the numerator and transport the identity.

This avoids needing any UFD/coprime infrastructure.

### Route 2: prove a custom `δ`-adic Euclid lemma

Let

```lean
δ = X₀ - X₁
m = X₀^3 * X₁^3
```

Mathematically, the needed statement is:

```lean
δ^3 ∣ f * m → δ^3 ∣ f
```

because the `δ`-adic order of `m` is `0`.

A possible formal path is to build a change-of-coordinates automorphism

```text
U = X₀ - X₁,
V = X₁,
X₀ = U + V,
X₁ = V.
```

Under this automorphism, the multiplier becomes

```text
(U + V)^3 * V^3,
```

which is not divisible by `U`. Then prove an `X`-adic order/cancellation lemma for the distinguished variable `U`. This is more work, but it uses the existing `X_pow_dvd_iff` / order API rather than a missing multivariate UFD instance.

### Route 3: develop enough UFD/prime API locally

This is mathematically clean but likely too expensive for the current divisibility goal:

1. prove `MvPowerSeries (Fin 2) K` is a UFD, or at least prove `Prime (X₀ - X₁)`;
2. prove `¬ (X₀ - X₁ ∣ X₀)` and `¬ (X₀ - X₁ ∣ X₁)`;
3. use repeated Euclid/prime divisibility to cancel the multiplier.

Given the Mathlib TODO on finite-variable `MvPowerSeries` noetherianity, this route is probably overkill.

## Bottom line

- `K[[X₀,X₁]]` is mathematically a UFD.
- Mathlib at the pinned revision has `MvPowerSeries` as a domain/no-zero-divisors ring, but not as a packaged UFD.
- Mathlib's `IsCoprime` is comaximal/Bézout and is false for `(X₀-X₁)^3` and `X₀^3 X₁^3`.
- A non-zero-divisor multiplier is not enough to cancel from `a ∣ b*c`.
- For the current project, the shortest Lean route is probably direct factorization of `addZ`, or a custom `δ`-adic divisibility lemma after the linear change of variables `U = X₀-X₁`, `V=X₁`.
