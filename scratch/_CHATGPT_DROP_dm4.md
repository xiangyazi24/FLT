# Q450 / dm4 — MvPowerSeries substitution API for formal-group construction

## Question

For the formal group law

```lean
F : MvPowerSeries (Fin 2) K
```

we need to insert a univariate power series `u(t) : PowerSeries K` into the two bivariate variables `t₁` and `t₂`, then use the resulting bivariate series inside the projective addition formula.

The key API questions are:

* how `PowerSeries K` relates to `MvPowerSeries (Fin 2) K`;
* how to define `u(t₁)` and `u(t₂)`;
* how to divide by a unit bivariate power series;
* how to prove coefficient statements such as `coeff (single 0 1) F = 1`.

## Short verdict

There is no dedicated API called

```lean
PowerSeries.toMvPowerSeries : PowerSeries K → MvPowerSeries (Fin 2) K
```

that embeds a univariate series as the `i`-th variable.  The right API is **substitution**:

```lean
PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) u
```

This is exactly `u(tᵢ)` as a bivariate power series.

## Imports

Use these imports:

```lean
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Inverse
```

`PowerSeries.Substitution` imports the multivariate substitution/evaluation API and provides the univariate wrapper.

## Basic definitions

```lean
noncomputable section

open MvPowerSeries
open Finsupp

variable {K : Type*} [Field K]

abbrev Biv (K : Type*) [Field K] := MvPowerSeries (Fin 2) K

def t₁ : Biv K := MvPowerSeries.X (0 : Fin 2)
def t₂ : Biv K := MvPowerSeries.X (1 : Fin 2)

/-- Interpret a univariate power series `f(t)` as `f(tᵢ)` in `K⟦t₁,t₂⟧`. -/
def atVar (i : Fin 2) (f : PowerSeries K) : Biv K :=
  PowerSeries.subst (R := K) (S := K) (τ := Fin 2)
    (MvPowerSeries.X i : Biv K) f

notation f "⟦t₁⟧" => atVar (K := K) (0 : Fin 2) f
notation f "⟦t₂⟧" => atVar (K := K) (1 : Fin 2) f
```

Then, for `u : PowerSeries K`, use

```lean
def u₁ (u : PowerSeries K) : Biv K := atVar (K := K) 0 u
def u₂ (u : PowerSeries K) : Biv K := atVar (K := K) 1 u
```

or just inline

```lean
PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : Biv K) u
PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : Biv K) u
```

## Why this is the right API

Mathlib defines

```lean
PowerSeries R := MvPowerSeries Unit R
```

so a univariate power series is literally a multivariate power series with one variable, indexed by `Unit`.  But to move from the `Unit` variable to the `Fin 2` variables, the API is substitution, not coercion/embedding.

The relevant univariate substitution definition is:

```lean
noncomputable def PowerSeries.subst
    (a : MvPowerSeries τ S) (f : PowerSeries R) : MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f
```

So `PowerSeries.subst (MvPowerSeries.X i) f` is exactly the substitution of the unique univariate variable by the bivariate variable `X i`.

The required substitution hypothesis is packaged as

```lean
PowerSeries.HasSubst a := IsNilpotent (MvPowerSeries.constantCoeff a)
```

and Mathlib has

```lean
PowerSeries.HasSubst.X : HasSubst (MvPowerSeries.X t)
PowerSeries.HasSubst.X' : HasSubst (PowerSeries.X)
PowerSeries.HasSubst.of_constantCoeff_zero
```

Since `MvPowerSeries.X i` has constant coefficient zero, the substitution `f(tᵢ)` is legitimate.

## Coefficient formula for substituted univariate series

Mathlib has a coefficient formula:

```lean
theorem PowerSeries.coeff_subst
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
  MvPowerSeries.coeff e (PowerSeries.subst a f) =
    finsum (fun d : ℕ ↦
      PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d))
```

In particular, for `a = X i`, this reduces morally to

```text
coeff_e(f(tᵢ)) = coeff_d(f)
```

when `e = single i d`, and zero when `e` has support in the wrong variable or has mixed support.  You may need a small local lemma for the exact shape you use, proved from `PowerSeries.coeff_subst`, `MvPowerSeries.coeff_X`, and `MvPowerSeries.coeff_X_pow`.

For linear terms, the cheap lemmas are usually enough:

```lean
#check MvPowerSeries.coeff_index_single_X
#check MvPowerSeries.coeff_index_single_self_X
```

They say:

```lean
coeff (single t 1) (X s) = if t = s then 1 else 0
coeff (single s 1) (X s) = 1
```

These are the lemmas to prove `lin_coeff_X` and `lin_coeff_Y` once you know your constructed `F` is `X 0 + X 1 + higher`.

## Substituting into a six-variable polynomial/power-series expression

For the projective addition formula, the cleanest approach is not to manufacture a separate six-variable `MvPowerSeries`; just instantiate the formula directly over the bivariate power-series coefficient ring.

Sketch:

```lean
open WeierstrassCurve WeierstrassCurve.Projective

variable (W : WeierstrassCurve K)

abbrev R₂ := MvPowerSeries (Fin 2) K

def W₂ : WeierstrassCurve.Projective (R₂ K) :=
  W.map (algebraMap K (R₂ K))

def P₁ (w : PowerSeries K) : Fin 3 → R₂ K :=
  ![MvPowerSeries.X (0 : Fin 2), -1, PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : R₂ K) w]

def P₂ (w : PowerSeries K) : Fin 3 → R₂ K :=
  ![MvPowerSeries.X (1 : Fin 2), -1, PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : R₂ K) w]

def rawAddXYZ (w : PowerSeries K) : Fin 3 → R₂ K :=
  (W₂ W).addXYZ (P₁ w) (P₂ w)
```

This works because the raw projective formulas are polynomial expressions over a `CommRing`, and `MvPowerSeries (Fin 2) K` is a commutative ring.

If you do have a separate six-variable expression, use `MvPowerSeries.subst` for a power series expression, or `MvPolynomial.aeval` for a polynomial expression:

```lean
-- six-variable target, schematic only
abbrev Six := Fin 6

-- for a polynomial p : MvPolynomial Six K
-- MvPolynomial.aeval coords p : R₂ K

-- for a power series f : MvPowerSeries Six K
-- MvPowerSeries.subst coords f : R₂ K
```

where `coords : Six → R₂ K` maps the six variables to the three coordinates of `P₁` and `P₂`.

## Division by a unit bivariate power series

Use `MvPowerSeries.invOfUnit` when you have an explicit unit constant coefficient:

```lean
def divByUnit (num den : Biv K) (u : Kˣ)
    (hden : MvPowerSeries.constantCoeff den = u) : Biv K :=
  num * MvPowerSeries.invOfUnit den u
```

Relevant API:

```lean
MvPowerSeries.invOfUnit
MvPowerSeries.mul_invOfUnit
MvPowerSeries.invOfUnit_mul
MvPowerSeries.isUnit_iff_constantCoeff
```

So if the denominator has constant coefficient `-1`, `1`, or another nonzero scalar, package it as a `Kˣ` and use `invOfUnit`.  Over a field, `IsUnit (constantCoeff den)` is equivalent to `constantCoeff den ≠ 0`, but `invOfUnit` is usually the most controllable for rewriting.

## Coefficients of the final formal group law

For your custom `FormalGroup`, the linear coefficient fields should be proved from statements of the form

```lean
MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F = 1
MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F = 1
```

Recommended proof strategy:

1. First prove a local expansion lemma:

```lean
F = MvPowerSeries.X 0 + MvPowerSeries.X 1 + H
```

where all coefficients of `H` of total degree `≤ 1` vanish.

2. Then the linear coefficient proofs are short rewrites using:

```lean
MvPowerSeries.coeff_index_single_X
MvPowerSeries.coeff_index_single_self_X
MvPowerSeries.coeff_add
MvPowerSeries.coeff_zero
```

3. For `H`, use a purpose-built lemma, e.g.

```lean
theorem coeff_H_linear_zero (i : Fin 2) :
  MvPowerSeries.coeff (Finsupp.single i 1) H = 0 := ...
```

Do not try to prove the linear coefficient facts directly from the full projective `addXYZ` expression in one `ring_nf`; isolate the degree-1 truncation first.

## Answer to each question

### 1. How to define `F` by substituting `u(t₁)`, `u(t₂)`?

Use

```lean
PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) u
PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) u
```

then instantiate `Projective.addXYZ` over `MvPowerSeries (Fin 2) K`.

### 2. How does Mathlib handle `PowerSeries → MvPowerSeries` conversion?

`PowerSeries K` is definitionally `MvPowerSeries Unit K`.  To reinterpret it in two variables, use `PowerSeries.subst`, not a coercion.

### 3. Is there `PowerSeries.toMvPowerSeries`?

Not as the right tool.  The effective operation is:

```lean
PowerSeries.subst (MvPowerSeries.X i) f
```

### 4. How to express `u(t₁)` vs `u(t₂)`?

```lean
def u_at (i : Fin 2) (u : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) u

abbrev u₁ (u : PowerSeries K) := u_at (K := K) 0 u
abbrev u₂ (u : PowerSeries K) := u_at (K := K) 1 u
```

### 5. Division by a unit?

Use

```lean
MvPowerSeries.invOfUnit den u
```

with proof `constantCoeff den = u`, or use `MvPowerSeries.isUnit_iff_constantCoeff` to convert a unit constant coefficient into a unit power series.

### 6. Computing coefficients?

Use

```lean
MvPowerSeries.coeff e F
```

with `e : Fin 2 →₀ ℕ`, especially `Finsupp.single 0 1` and `Finsupp.single 1 1`.  The core variable coefficient lemmas are `coeff_index_single_X` and `coeff_index_single_self_X`.

## Final recommended minimal API layer

Put this in a scratch helper file:

```lean
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Inverse

noncomputable section

open MvPowerSeries
open Finsupp

namespace WeierstrassFormalGroupScratch

variable {K : Type*} [Field K]

abbrev Biv := MvPowerSeries (Fin 2) K

abbrev T₁ : Biv := MvPowerSeries.X (0 : Fin 2)
abbrev T₂ : Biv := MvPowerSeries.X (1 : Fin 2)

def atVar (i : Fin 2) (f : PowerSeries K) : Biv :=
  PowerSeries.subst (R := K) (S := K) (τ := Fin 2)
    (MvPowerSeries.X i : Biv) f

abbrev atT₁ (f : PowerSeries K) : Biv := atVar (K := K) 0 f
abbrev atT₂ (f : PowerSeries K) : Biv := atVar (K := K) 1 f

def divByUnit (num den : Biv) (u : Kˣ)
    (_hden : MvPowerSeries.constantCoeff den = u) : Biv :=
  num * MvPowerSeries.invOfUnit den u

end WeierstrassFormalGroupScratch
```

This is enough to express `u(t₁)`, `u(t₂)`, instantiate projective `addXYZ` over the bivariate power-series ring, normalize by a unit denominator, and state/prove the linear coefficient properties of the resulting formal group law.
