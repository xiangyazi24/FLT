# Q462 / dm4 — proving `lin_coeff_X = 1` and `lin_coeff_Y = 1` for the Weierstrass formal group law

## Goal

Assume the normalized formal group law has already been defined as

```lean
F : MvPowerSeries (Fin 2) K
```

with variables

```lean
T₁ = MvPowerSeries.X (0 : Fin 2)
T₂ = MvPowerSeries.X (1 : Fin 2)
```

The target fields are

```lean
lin_coeff_X : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F = 1
lin_coeff_Y : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F = 1
```

Mathematically this is the statement

```text
F(T₁,T₂) = T₁ + T₂ + terms of total degree ≥ 2.
```

## Main recommendation

Do **not** prove these coefficients by expanding the full normalized `-addX/addY` expression and asking `ring_nf` to find the linear terms.  Instead prove the two one-variable neutral-axis identities:

```lean
F(T₁, 0) = T₁
F(0, T₂) = T₂
```

Then extract the coefficient of `X^1` from each identity.

This is much smaller in Lean because the neutral-element property collapses one input point to `O`, and the final coefficient extraction is a generic `MvPowerSeries` lemma.

## Important caveat about raw `addXYZ`

The raw standard-projective formula can produce representatives with a common nonunit factor on the axes.  For example, with

```text
P(t) = [t : -1 : w(t)],   O = P(0) = [0 : -1 : 0],
```

Mathlib's standard projective lemma for adding a point at infinity gives a scalar multiple of `P(t)`, and the scalar may be a nonunit such as `w(t)`.  Therefore the identity should be proved for the **normalized local parameter formula** defining `F`, not by treating raw `addXYZ(P(t),O)` as a unit-equivalent projective representative.

Concretely: once your construction has cancelled the common factor and defined a denominator with unit constant term, prove the axis identities for that normalized quotient.

## API setup

Use bivariate power series and the two coordinate variables:

```lean
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Inverse

noncomputable section

open MvPowerSeries
open Finsupp

variable {K : Type*} [Field K]

abbrev Biv := MvPowerSeries (Fin 2) K

abbrev T₁ : Biv := MvPowerSeries.X (0 : Fin 2)
abbrev T₂ : Biv := MvPowerSeries.X (1 : Fin 2)
```

Define the two axis-specialization maps by substitution:

```lean
/-- Substitute `(T₁,T₂) = (X,0)`, giving a univariate power series. -/
def axis₁Args : Fin 2 → PowerSeries K :=
  ![PowerSeries.X, 0]

/-- Substitute `(T₁,T₂) = (0,X)`, giving a univariate power series. -/
def axis₂Args : Fin 2 → PowerSeries K :=
  ![0, PowerSeries.X]

lemma axis₁_hasSubst : MvPowerSeries.HasSubst (R := K) (S := K) axis₁Args := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [axis₁Args]

lemma axis₂_hasSubst : MvPowerSeries.HasSubst (R := K) (S := K) axis₂Args := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [axis₂Args]

def axis₁ : Biv →ₐ[K] PowerSeries K :=
  MvPowerSeries.substAlgHom axis₁_hasSubst

def axis₂ : Biv →ₐ[K] PowerSeries K :=
  MvPowerSeries.substAlgHom axis₂_hasSubst
```

You get the expected behavior on variables from `MvPowerSeries.subst_X` / `substAlgHom_X`:

```lean
lemma axis₁_T₁ : axis₁ (K := K) T₁ = PowerSeries.X := by
  rw [axis₁, MvPowerSeries.substAlgHom_X]
  rfl

lemma axis₁_T₂ : axis₁ (K := K) T₂ = 0 := by
  rw [axis₁, MvPowerSeries.substAlgHom_X]
  rfl

lemma axis₂_T₁ : axis₂ (K := K) T₁ = 0 := by
  rw [axis₂, MvPowerSeries.substAlgHom_X]
  rfl

lemma axis₂_T₂ : axis₂ (K := K) T₂ = PowerSeries.X := by
  rw [axis₂, MvPowerSeries.substAlgHom_X]
  rfl
```

The exact syntax may need minor adjustment around implicit parameters, but this is the intended API shape.

## Generic coefficient-extraction lemmas

Prove these once and reuse them.

```lean
lemma coeff_axis₁_one (G : Biv) :
    PowerSeries.coeff 1 (axis₁ (K := K) G)
      = MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) G := by
  -- Recommended proof:
  -- 1. unfold `axis₁` and `PowerSeries.coeff`;
  -- 2. use `MvPowerSeries.coeff_subst axis₁_hasSubst G (Finsupp.single () 1)`;
  -- 3. all terms vanish except the source exponent `single 0 1`;
  -- 4. use `coeff_X_pow`, `coeff_zero`, and `zero_pow`.
  -- This is a finite-support/finsum cleanup lemma.  Prove it once.
  sorry

lemma coeff_axis₂_one (G : Biv) :
    PowerSeries.coeff 1 (axis₂ (K := K) G)
      = MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) G := by
  -- Same proof, with variables swapped.
  sorry
```

This pair is the clean bridge from one-variable neutral identities to bivariate linear coefficients.

If the `finsum` proof is annoying, an alternative is to use `MvPowerSeries.truncTotal` and prove that `axis₁` preserves the degree-1 truncation.  But `coeff_subst` is the most direct theorem.

Relevant APIs:

```lean
#check MvPowerSeries.coeff_subst
#check MvPowerSeries.substAlgHom
#check MvPowerSeries.subst_X
#check MvPowerSeries.substAlgHom_X
#check PowerSeries.coeff_one_X
#check MvPowerSeries.coeff_index_single_X
#check MvPowerSeries.coeff_index_single_self_X
```

## The two curve-specific neutral-axis lemmas

For the normalized formal group law, prove:

```lean
lemma formalGroupLaw_axis₁ (F : Biv) :
    axis₁ (K := K) F = PowerSeries.X := by
  -- This is the curve-specific content.
  -- It should come from the construction of `F` and the identity `P(t) + O = P(t)`.
  -- Do this after normalization/cancellation, not at raw `addXYZ` level.
  sorry

lemma formalGroupLaw_axis₂ (F : Biv) :
    axis₂ (K := K) F = PowerSeries.X := by
  -- Same, using `O + P(t) = P(t)`.
  sorry
```

More specifically, if

```lean
P(t) = [t, -1, w(t)]
```

and your bivariate inputs are

```lean
P₁ = [T₁, -1, w(T₁)]
P₂ = [T₂, -1, w(T₂)]
```

then `axis₁` sends `P₂` to `O` and leaves `P₁` as the univariate point `P(t)`.  The normalized local parameter of `P(t)+O` is exactly `t`, hence `axis₁ F = X`.  Similarly, `axis₂` sends `P₁` to `O`, leaves `P₂ = P(t)`, and gives `axis₂ F = X`.

The raw projective helper lemmas that may help diagnose the axis computation are:

```lean
WeierstrassCurve.Projective.addXYZ_of_Z_eq_zero_left
WeierstrassCurve.Projective.addXYZ_of_Z_eq_zero_right
WeierstrassCurve.Projective.map_addXYZ
WeierstrassCurve.Projective.baseChange_addXYZ
```

but remember: because the scalar can be a nonunit in the power-series ring, the final axis proof should use the normalized quotient/factorization defining `F`.

## Final linear coefficient proofs

Once the generic coefficient-extraction lemmas and the two axis identities are available, the formal group linear coefficient fields are tiny:

```lean
theorem lin_coeff_X_of_axis₁
    {F : Biv}
    (hF₁ : axis₁ (K := K) F = PowerSeries.X) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F = 1 := by
  rw [← coeff_axis₁_one (K := K) F]
  rw [hF₁]
  exact PowerSeries.coeff_one_X


theorem lin_coeff_Y_of_axis₂
    {F : Biv}
    (hF₂ : axis₂ (K := K) F = PowerSeries.X) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F = 1 := by
  rw [← coeff_axis₂_one (K := K) F]
  rw [hF₂]
  exact PowerSeries.coeff_one_X
```

Then instantiate these with your formal group law:

```lean
theorem W_formalGroup_lin_coeff_X :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) W.F = 1 := by
  exact lin_coeff_X_of_axis₁ (formalGroupLaw_axis₁ W.F)


theorem W_formalGroup_lin_coeff_Y :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) W.F = 1 := by
  exact lin_coeff_Y_of_axis₂ (formalGroupLaw_axis₂ W.F)
```

Adjust field names to your actual `FormalGroup` structure.

## Why this is better than direct coefficient expansion

A direct proof of

```lean
MvPowerSeries.coeff (single 0 1) F = 1
```

from the full formula sees every piece of the normalized addition expression.  Even if all high-degree terms vanish, Lean still has to expand/project/cancel a large projective expression.

The axis proof uses only:

1. the neutral element identity in one variable;
2. a generic `coeff_subst` lemma;
3. `PowerSeries.coeff_one_X`.

So the hard algebra is concentrated in proving

```lean
axis₁ F = X
axis₂ F = X
```

which is exactly what the group-law construction is supposed to guarantee.

## Alternative: degree-1 truncation

If the axis identities are hard because the normalization is still being built, a second viable target is the linear truncation:

```lean
F = T₁ + T₂ + H
```

where

```lean
MvPowerSeries.coeff (single (0 : Fin 2) 0) H = 0
MvPowerSeries.coeff (single (0 : Fin 2) 1) H = 0
MvPowerSeries.coeff (single (1 : Fin 2) 1) H = 0
```

More invariantly, all coefficients of total degree `≤ 1` in `H` vanish.  Mathlib has `MvPowerSeries.truncTotal` for finite variable types, so one can prove

```lean
F.truncTotal 1 = (T₁ + T₂).truncTotal 1
```

or the corresponding coefficient equalities.  However, the neutral-axis approach is usually shorter because it avoids bivariate total-degree bookkeeping.

## Bottom line

The recommended Lean route is:

1. Define axis specialization homs:

```lean
axis₁ : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K
axis₂ : MvPowerSeries (Fin 2) K →ₐ[K] PowerSeries K
```

by `MvPowerSeries.substAlgHom ![PowerSeries.X,0]` and `![0,PowerSeries.X]`.

2. Prove once:

```lean
PowerSeries.coeff 1 (axis₁ G) = coeff (single 0 1) G
PowerSeries.coeff 1 (axis₂ G) = coeff (single 1 1) G
```

using `MvPowerSeries.coeff_subst`.

3. Prove the curve-specific neutral identities after normalization:

```lean
axis₁ F = PowerSeries.X
axis₂ F = PowerSeries.X
```

4. Finish both formal group fields by rewriting and applying:

```lean
PowerSeries.coeff_one_X
```

This avoids expanding the full bivariate addition formula and isolates the actual geometry in the two neutral-axis lemmas.
