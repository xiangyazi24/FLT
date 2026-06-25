# Q479 / dm4 — `MvPowerSeries (Fin 2) K`, UFD, and coprimality

## Executive answer

For the intended step

```lean
(X₀ - X₁)^3 ∣ addZ * X₀^3 * X₁^3  ⟹  (X₀ - X₁)^3 ∣ addZ
```

do **not** use Mathlib's `IsCoprime` between `(X₀ - X₁)^3` and `X₀^3 * X₁^3`.  That statement is not merely missing from Mathlib; with Mathlib's definition it is **false**.

Mathlib's `IsCoprime x y` is Bézout/comaximal coprimality:

```lean
def IsCoprime (x y : R) : Prop :=
  ∃ a b, a * x + b * y = 1
```

In the local power series ring `K[[X₀,X₁]] = MvPowerSeries (Fin 2) K`, both `(X₀ - X₁)^3` and `X₀^3 * X₁^3` have zero constant coefficient.  Applying `constantCoeff` to any supposed Bézout identity gives `0 = 1`.

Mathematically, `K[[X₀,X₁]]` is a UFD and `(X₀ - X₁)` has no common prime factor with `X₀X₁`.  But Mathlib, at the pinned FLT mathlib revision,

```toml
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

does not appear to package a multivariate `MvPowerSeries (Fin 2) K` UFD instance.  It does provide the no-zero-divisors/domain API and univariate `PowerSeries` UFD API.

The best Lean route is a `δ`-adic / weighted-order cancellation after the linear change of variables

```text
U = X₀ - X₁,   V = X₁.
```

Under this change, the divisor becomes `U^3` and the multiplier becomes `(U+V)^3 * V^3`, which has `U`-order `0`.  So it cannot contribute any factor of `U`.

---

## Grep/API findings

### 1. `MvPowerSeries` domain/no-zero-divisors API

Relevant files:

```text
Mathlib/RingTheory/MvPowerSeries/Basic.lean
Mathlib/RingTheory/MvPowerSeries/NoZeroDivisors.lean
Mathlib/RingTheory/MvPowerSeries/Order.lean
Mathlib/RingTheory/MvPowerSeries/Inverse.lean
Mathlib/RingTheory/MvPowerSeries/Substitution.lean
```

`MvPowerSeries.Basic` defines:

```lean
def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ →₀ ℕ) → R
```

and gives the usual algebraic instances, including:

```lean
instance [CommSemiring R] : CommSemiring (MvPowerSeries σ R)
instance [CommRing R]    : CommRing    (MvPowerSeries σ R)
```

The key domain file is `Mathlib/RingTheory/MvPowerSeries/NoZeroDivisors.lean`.  It contains:

```lean
theorem MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff

lemma MvPowerSeries.X_mem_nonzeroDivisors {i : σ} :
    X i ∈ (MvPowerSeries σ R)⁰

instance [Semiring R] [NoZeroDivisors R] :
    NoZeroDivisors (MvPowerSeries σ R)
```

and the order-multiplication theorem:

```lean
theorem MvPowerSeries.weightedOrder_mul
    (w : σ → ℕ) (f g : MvPowerSeries σ R) :
    (f * g).weightedOrder w = f.weightedOrder w + g.weightedOrder w
```

under `[Semiring R] [NoZeroDivisors R]`.

So over a field:

```lean
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

example {K : Type*} [Field K] :
    NoZeroDivisors (MvPowerSeries (Fin 2) K) := by
  infer_instance

example {K : Type*} [Field K] :
    IsDomain (MvPowerSeries (Fin 2) K) := by
  exact NoZeroDivisors.to_isDomain _
```

I did not find a dedicated declaration named `MvPowerSeries.IsDomain`; the available multivariate declaration is the `NoZeroDivisors` instance, and `IsDomain` follows by the general lemma `NoZeroDivisors.to_isDomain`.

### 2. UFD API

Relevant file:

```text
Mathlib/RingTheory/PowerSeries/Ideal.lean
```

Mathlib has the univariate power-series UFD/UFM theorem:

```lean
instance [IsPrincipalIdealRing R] [IsDomain R] :
    UniqueFactorizationMonoid R⟦X⟧
```

Here

```lean
PowerSeries R := MvPowerSeries Unit R
```

so this is a theorem about **one-variable** power series.  In particular, for a field `K`, `K⟦X⟧` has the packaged UFM instance.

I did **not** find an instance of the form

```lean
UniqueFactorizationMonoid (MvPowerSeries σ R)
```

or specifically

```lean
UniqueFactorizationMonoid (MvPowerSeries (Fin 2) K)
```

The same `PowerSeries/Ideal.lean` file has the relevant TODO:

```text
Prove noetherianity of `MvPowerSeries` in finitely many variables.
```

That is strong evidence that the finite-variable multivariate UFD route is not currently packaged in Mathlib.

### 3. Coprimality API

Relevant files:

```text
Mathlib/RingTheory/Coprime/Basic.lean
Mathlib/RingTheory/Coprime/Lemmas.lean
```

Useful generic declarations:

```lean
#check IsCoprime
#check IsCoprime.dvd_of_dvd_mul_left
#check IsCoprime.dvd_of_dvd_mul_right
#check IsCoprime.mul_left
#check IsCoprime.mul_right
#check IsCoprime.pow_left
#check IsCoprime.pow_right
#check IsCoprime.pow
```

These are generic for commutative semirings/rings; there does not appear to be special `PowerSeries`/`MvPowerSeries` coprimality API that would solve this goal.

More importantly, `IsCoprime` is the wrong notion here.  In a UFD one would want a no-common-prime-factor / relative-prime statement, not a Bézout identity.  The Mathlib coprime documentation explicitly warns that `IsCoprime` is stronger than `IsRelPrime`; multivariate polynomial variables are the standard example.

---

## Answers to the numbered questions

### (a) Is `MvPowerSeries (Fin 2) K` a UFD when `K` is a field?

Mathematically: **yes**.  `K[[X₀,X₁]]` is a regular local ring, hence a UFD.

In Mathlib: **not available as a packaged instance/theorem** that I found.  The univariate theorem exists for `PowerSeries K = K⟦X⟧`, but the finite multivariate theorem for `MvPowerSeries (Fin 2) K` does not appear to be present.

### (b) Does Mathlib have `MvPowerSeries.IsDomain` or `MvPowerSeries.UniqueFactorizationDomain`?

`MvPowerSeries.IsDomain`: not as a dedicated declaration.  But for `[Field K]`:

```lean
example : NoZeroDivisors (MvPowerSeries (Fin 2) K) := by
  infer_instance

example : IsDomain (MvPowerSeries (Fin 2) K) := by
  exact NoZeroDivisors.to_isDomain _
```

`MvPowerSeries.UniqueFactorizationDomain` / `UniqueFactorizationMonoid`: not found for `MvPowerSeries (Fin 2) K`.  The available UFM instance is univariate:

```lean
instance [IsPrincipalIdealRing R] [IsDomain R] :
    UniqueFactorizationMonoid R⟦X⟧
```

### (c) Does Mathlib have `IsCoprime` for `MvPowerSeries`?

Only generically.  Since `MvPowerSeries σ R` is a commutative semiring/ring when `R` is, the generic definition and lemmas apply.  But there does not appear to be power-series-specific API, and generic `IsCoprime` is Bézout/comaximal coprimality.

### (d) Can we prove `IsCoprime (X₀-X₁)^3 (X₀^3·X₁^3)` in `MvPowerSeries`?

No.  It is false.

Lean-shaped obstruction:

```lean
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section

open MvPowerSeries

variable {K : Type*} [Field K]

abbrev Biv := MvPowerSeries (Fin 2) K

abbrev X0 : Biv := MvPowerSeries.X (0 : Fin 2)
abbrev X1 : Biv := MvPowerSeries.X (1 : Fin 2)
abbrev Δ  : Biv := X0 - X1

lemma not_isCoprime_delta_cube_X0X1_cube :
    ¬ IsCoprime (Δ ^ 3) (X0 ^ 3 * X1 ^ 3) := by
  intro h
  rcases h with ⟨a, b, hab⟩
  have hc := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K)) hab
  -- `constantCoeff` kills `X0`, `X1`, and hence `Δ`; RHS has constant coefficient `1`.
  simpa [Δ, X0, X1] using hc
```

If `simp` needs help in the local file, add explicit rewrites using `map_add`, `map_mul`, `map_sub`, `map_pow`, and `MvPowerSeries.constantCoeff_X`.

### (e) Can we use `mul_dvd_cancel` / `dvd_of_mul_dvd_mul_left` if the multiplier is a non-zero-divisor?

Not for this shape.

A non-zero-divisor multiplier `m` does **not** imply

```lean
p ∣ f * m  →  p ∣ f
```

Counterexample in a domain: `2 ∣ 1 * 2`, but `2 ∤ 1`.

The standard cancellation lemmas cancel a common factor on both sides, e.g.

```lean
#check mul_dvd_mul_iff_left
#check mul_dvd_mul_iff_right
```

with shapes like

```lean
a * b ∣ a * c ↔ b ∣ c
```

under nonzero/cancellative hypotheses on `a`.  They do not prove cancellation from `p ∣ f*m`.

For the intended argument you need one of:

1. UFD/GCD-style relative primality between `p` and `m`;
2. `m` is a non-zero-divisor modulo `(p^3)`;
3. an order/valuation argument showing that `m` has `p`-adic order zero.

For the current `MvPowerSeries` goal, option 3 is the shortest with available Mathlib API.

---

## Recommended Lean route: shear + weighted order

Let

```lean
U = X₀ - X₁
V = X₁
```

Equivalently, apply the substitution/automorphism

```text
X₀ ↦ U + V,
X₁ ↦ V.
```

Then

```text
X₀ - X₁       ↦ U,
X₀^3 * X₁^3  ↦ (U + V)^3 * V^3.
```

Define the weight measuring only the `U` exponent:

```lean
abbrev Biv := MvPowerSeries (Fin 2) K
abbrev U : Biv := MvPowerSeries.X (0 : Fin 2)
abbrev V : Biv := MvPowerSeries.X (1 : Fin 2)

def uWeight : Fin 2 → ℕ := fun i => if i = 0 then 1 else 0
```

Then `U^n ∣ f` can be bridged to weighted-order using:

```lean
#check MvPowerSeries.X_pow_dvd_iff
#check MvPowerSeries.nat_le_weightedOrder
#check MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder
```

A useful local lemma is:

```lean
lemma U_pow_dvd_of_uWeight_ge {n : ℕ} {f : Biv}
    (h : (n : ℕ∞) ≤ f.weightedOrder uWeight) :
    U ^ n ∣ f := by
  rw [MvPowerSeries.X_pow_dvd_iff]
  intro m hm
  apply MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder uWeight
  refine lt_of_lt_of_le ?_ h
  -- Need the small simplification lemma: `Finsupp.weight uWeight m = m 0`.
  simpa [uWeight, U] using hm

lemma uWeight_ge_of_U_pow_dvd {n : ℕ} {f : Biv}
    (h : U ^ n ∣ f) :
    (n : ℕ∞) ≤ f.weightedOrder uWeight := by
  rw [MvPowerSeries.X_pow_dvd_iff] at h
  apply MvPowerSeries.nat_le_weightedOrder uWeight
  intro m hm
  apply h m
  -- Again use `Finsupp.weight uWeight m = m 0`.
  simpa [uWeight, U] using hm
```

If the `simpa [uWeight]` does not close, prove once:

```lean
lemma weight_uWeight (m : Fin 2 →₀ ℕ) :
    Finsupp.weight uWeight m = m (0 : Fin 2) := by
  classical
  -- finite-support sum; coordinate `1` has weight zero.
  sorry
```

Now the cancellation lemma is exactly `weightedOrder_mul`:

```lean
lemma U_pow_dvd_of_U_pow_dvd_mul_of_uOrder_zero
    {n : ℕ} {f m : Biv}
    (hm : m.weightedOrder uWeight = 0)
    (hdiv : U ^ n ∣ f * m) :
    U ^ n ∣ f := by
  apply U_pow_dvd_of_uWeight_ge (K := K)
  have hge : (n : ℕ∞) ≤ (f * m).weightedOrder uWeight :=
    uWeight_ge_of_U_pow_dvd (K := K) hdiv
  simpa [MvPowerSeries.weightedOrder_mul, hm] using hge
```

For the sheared multiplier

```lean
def multUV : Biv := (U + V)^3 * V^3
```

prove:

```lean
lemma multUV_uOrder_zero :
    (multUV (K := K)).weightedOrder uWeight = 0 := by
  -- Coefficient of `V^6` is `1`, and its `uWeight` is `0`.
  -- Use `MvPowerSeries.weightedOrder_le` and the coefficient computation.
  sorry
```

The coefficient proof is small: the monomial `V^6` occurs uniquely from choosing the `V^3` term in `(U+V)^3` and multiplying by `V^3`.

Finally, build the shear via substitution:

```lean
def shearArgs : Fin 2 → Biv := ![U + V, V]

lemma shear_hasSubst : MvPowerSeries.HasSubst (R := K) (S := K) shearArgs := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [shearArgs, U, V]

def shear : Biv →ₐ[K] Biv :=
  MvPowerSeries.substAlgHom shear_hasSubst
```

with inverse substitution

```lean
def unshearArgs : Fin 2 → Biv := ![X0 - X1, X1]
```

and use `MvPowerSeries.substAlgHom_X`, `subst_add`, `subst_sub`, `subst_mul`, and `subst_pow` to show the two substitutions are inverse and transport divisibility back.

Conceptually the final theorem is:

```lean
lemma delta_cube_dvd_of_delta_cube_dvd_mul
    {addZ : Biv}
    (h : (X0 - X1)^3 ∣ addZ * (X0^3 * X1^3)) :
    (X0 - X1)^3 ∣ addZ := by
  -- apply `shear` to `h`
  -- reduce to `U^3 ∣ shear addZ * multUV`
  -- use `U_pow_dvd_of_U_pow_dvd_mul_of_uOrder_zero multUV_uOrder_zero`
  -- apply `unshear` to return to original variables
  sorry
```

The remaining work is substitution bookkeeping and one finite coefficient calculation, not a missing UFD/coprimality theorem.

---

## Bottom line

* `K[[X₀,X₁]]` is mathematically a UFD.
* Mathlib has `NoZeroDivisors` / domain API for `MvPowerSeries`, but I did not find a multivariate UFD instance.
* Mathlib has univariate `PowerSeries` UFD/UFM API.
* `IsCoprime ((X₀-X₁)^3) (X₀^3*X₁^3)` is false because `IsCoprime` is Bézout/comaximal coprimality.
* Non-zero-divisor cancellation alone does not prove `p ∣ f*m → p ∣ f`.
* Use direct factorization if available; otherwise use the shear `U=X₀-X₁`, `V=X₁` and `MvPowerSeries.weightedOrder_mul` / `X_pow_dvd_iff`.
