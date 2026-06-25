# Q415 / dm2 — blind design brainstorm for `W.formalGroup`

This is an independent design, written without looking at dm1's answer.

Goal:

```lean
W.formalGroup : FormalGroup K
```

for a general Weierstrass curve

```text
y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆,
```

using Mathlib's `PowerSeries` / `MvPowerSeries` API and eventually connecting the formal-group linear term to division-polynomial tangent computations.

## Executive recommendation

I would **not** construct the formal group law by introducing Laurent series `x(t)` and `y(t)` in Lean.

Instead, use projective coordinates near infinity:

```text
t = -X/Y,
w = -Z/Y,
P(t) = [X : Y : Z] = [t : -1 : w(t)].
```

This keeps everything inside ordinary power series.  The only one-variable power series needed is `w(t)`, satisfying

```text
w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³.
```

Then define the two-variable formal group law by projective addition:

```text
P(T₁) + P(T₂) = [X₁₂ : Y₁₂ : Z₁₂],
F(T₁,T₂)     = -X₁₂ / Y₁₂,
```

where `Y₁₂` is a unit because the sum is again near `[0:1:0]`.  This avoids custom Laurent series completely and makes the connection to the projective division-polynomial formula much cleaner.

## (a) Construction plan: key definitions and lemmas

### 1. Work universally first

Define the universal coefficient ring

```lean
A := MvPolynomial (Fin 5) ℤ
```

or a named polynomial ring with variables `a₁,a₂,a₃,a₄,a₆`.  Build the universal formal group over `A`, then map it to an arbitrary coefficient ring `K` using Mathlib's `FormalGroup.map`.

Why universal first:

* all associativity and coefficient identities are polynomial identities;
* no field or nonzero-discriminant hypothesis is needed for the formal group law itself;
* division-polynomial compatibility later is easier to state once universally and then specialize.

Final specialization should look morally like

```lean
def WeierstrassCurve.formalGroup (W : WeierstrassCurve K) : FormalGroup K :=
  (universalFormalGroup.map (universalCoeffMap W))
```

unless direct construction over `K` is easier in the local codebase.

### 2. Define the one-variable series `w(t)`

Definitions:

```lean
def W.w : PowerSeries K
```

with equation

```lean
W.w = X^3
    + C a₁ * X * W.w
    + C a₂ * X^2 * W.w
    + C a₃ * W.w^2
    + C a₄ * X * W.w^2
    + C a₆ * W.w^3
```

Key lemmas:

```lean
@[simp] lemma w_coeff_0 : coeff K 0 W.w = 0
@[simp] lemma w_coeff_1 : coeff K 1 W.w = 0
@[simp] lemma w_coeff_2 : coeff K 2 W.w = 0
@[simp] lemma w_coeff_3 : coeff K 3 W.w = 1
lemma w_eq : W.w = ...
lemma w_unique : equation w' -> w' = W.w
lemma w_order3 : ∃ u : PowerSeries Kˣ-or-Unit, W.w = X^3 * u ∧ constantCoeff u = 1
```

Implementation detail: define `w` by coefficient recursion, not by closed forms.  The equation is triangular: the coefficient of `t^n` on the right only involves coefficients of `w` of degree `< n`.  No division by integers is required.

Do not expose much of the recursion.  Most later files should use only `w_eq`, the first few coefficients, and `w_unique`.

### 3. Define the formal projective point

In one variable:

```text
P(T) = [T : -1 : w(T)].
```

In `MvPowerSeries (Fin n) K`, define a substitution/rename helper:

```lean
def W.wAt (i : Fin n) : MvPowerSeries (Fin n) K
```

so that

```text
Pᵢ = [Xᵢ : -1 : wAt i].
```

Key lemma:

```lean
lemma formalPoint_on_curve :
  W.projectiveEquation Xᵢ (-1) (wAt i) = 0
```

This is just `w_eq` rewritten in homogeneous/projective form.

### 4. Define projective addition of two formal points

Use existing projective addition formulas if the project already has them.  The desired object is a coordinate triple

```lean
def W.formalAddXYZ : (MvPowerSeries (Fin 2) K)^3
```

representing

```text
P(T₁) + P(T₂) = [X₁₂ : Y₁₂ : Z₁₂].
```

If the only available addition formula is affine, do not form `x=t/w` or `y=-1/w` in Lean.  Use the projective version or the cleared-denominator collinearity determinant.  The projective point `[t:-1:w]` is the main trick that keeps this in `PowerSeries`.

Key lemmas:

```lean
lemma formalAdd_on_curve : W.projectiveEquation X₁₂ Y₁₂ Z₁₂ = 0
lemma formalAdd_Y_constantCoeff : constantCoeff Y₁₂ = 1  -- or -1, depending conventions
lemma formalAdd_Y_isUnit : IsUnit Y₁₂
lemma formalAdd_t_def : W.F = -X₁₂ * (Y₁₂)⁻¹
```

I would normalize signs once and then hide them behind simp lemmas.

### 5. Define the formal group law

```lean
def W.formalGroupLaw : MvPowerSeries (Fin 2) K :=
  - formalAddX * formalAddY⁻¹
```

Then package:

```lean
def W.formalGroup : FormalGroup K where
  toPowerSeries := W.formalGroupLaw
  zero_constantCoeff := ...
  lin_coeff_X := ...
  lin_coeff_Y := ...
  assoc := ...
```

Linear coefficient lemmas should be proved by reducing the projective addition formula modulo terms of total degree `≥ 2`.  Expected statement:

```text
F(T₁,T₂) = T₁ + T₂ + O(deg ≥ 2).
```

Concrete first lemmas:

```lean
lemma formalGroupLaw_constantCoeff : constantCoeff W.formalGroupLaw = 0
lemma formalGroupLaw_coeff_X : coeff (single 0 1) W.formalGroupLaw = 1
lemma formalGroupLaw_coeff_Y : coeff (single 1 1) W.formalGroupLaw = 1
lemma formalGroupLaw_eq_linear_mod_square :
  W.formalGroupLaw - X₀ - X₁ ∈ augmentationIdeal^2
```

### 6. Associativity

This is the key design choice.  I would avoid a brute-force `ring_nf` proof of associativity of the expanded two-variable formal law.

Preferred proof:

1. In three variables, define the three formal projective points

   ```text
   P₀ = [T₀:-1:w(T₀)], P₁ = [T₁:-1:w(T₁)], P₂ = [T₂:-1:w(T₂)].
   ```

2. Show both power series

   ```text
   F(F(T₀,T₁),T₂)
   F(T₀,F(T₁,T₂))
   ```

   are the local parameter `-X/Y` of the corresponding projective sums

   ```text
   (P₀ + P₁) + P₂,
   P₀ + (P₁ + P₂).
   ```

3. Use associativity of the projective Weierstrass group law.

4. Since both resulting projective representatives have `Y` a unit, equality of projective points implies equality of normalized local parameters `-X/Y`.

If the existing projective group law is only available over fields, prove the universal associativity over the fraction field of the universal power-series ring, then inject back into power series.  This is still not a custom Laurent series API; it uses Mathlib's fraction field/ring machinery.  The projective point `[T:-1:w(T)]` remains in ordinary power series, while the field proof can temporarily interpret `x=T/w` and `y=-1/w` if needed.

Key associativity support lemmas:

```lean
lemma formalAdd_subst_left :
  W.formalGroupLaw.subst ![W.formalGroupLaw.subst ![Y₀,Y₁], Y₂]
    = t_of_projective_sum ((P₀ + P₁) + P₂)

lemma formalAdd_subst_right :
  W.formalGroupLaw.subst ![Y₀, W.formalGroupLaw.subst ![Y₁,Y₂]]
    = t_of_projective_sum (P₀ + (P₁ + P₂))

lemma normalized_t_eq_of_projective_eq
  (h : projectivelyEquivalent P Q)
  (hPY : IsUnit P.Y) (hQY : IsUnit Q.Y) :
  -P.X/P.Y = -Q.X/Q.Y
```

The final `assoc` field is then a short wrapper around these lemmas.

## (b) Shortest path / can we avoid `w(t)` iteration?

Shortest path in Lean:

```text
w(t) once  →  projective formal point [t:-1:w(t)]
          →  projective addition formulas
          →  F = -X/Y
          →  associativity from projective group-law associativity
          →  FormalGroup instance
```

This avoids:

* defining Laurent series;
* expanding `x(t)=t/w(t)` and `y(t)=-1/w(t)` as Laurent series;
* deriving the affine addition formula in the completed local ring;
* proving associativity by direct coefficient bashing.

Can `w(t)` iteration be avoided entirely?  I do not think so, not if we want a concrete formal point on the curve using only `PowerSeries`.  Some object equivalent to `w(t)` is needed because `[t:-1:w]` must satisfy the homogeneous Weierstrass equation.

But we can avoid making the iteration part of the main proof.  Prove once:

```lean
existsUnique_w : ∃! w, w = t³ + a₁tw + a₂t²w + a₃w² + a₄tw² + a₆w³
```

then define

```lean
def W.w := Classical.choose existsUnique_w
```

and expose only `w_eq` and `w_unique`.  That keeps the formal group construction from depending on a long list of explicit coefficient computations.

The only place I would compute coefficients of `w` is for small-order lemmas such as

```text
w = t³ + a₁t⁴ + (a₁²+a₂)t⁵ + ...
```

used to prove linear terms or to debug CAS output.  These should not be part of the core definition.

## (c) Biggest risk / hardest step

The hardest step is **associativity in Mathlib's `MvPowerSeries.subst` language**.

There are three separate risks:

1. **Projective group-law availability.**  If the repository already has a robust associative projective Weierstrass addition theorem over the rings needed for `MvPowerSeries`, this is manageable.  If not, proving associativity of the formal law from scratch will dominate the project.

2. **Normalization by a unit.**  The proof must repeatedly show that the `Y` coordinate of a formal sum has unit constant coefficient, so `-X/Y` is a legal `PowerSeries` expression.  This is conceptually easy but can create many API lemmas about `constantCoeff`, `IsUnit`, and substitution.

3. **Substitution bookkeeping.**  The `FormalGroup.assoc` field is stated using `MvPowerSeries.subst`.  The proof has to align projective addition after substituting `F(T₀,T₁)` with Mathlib's exact `subst ![...]` expression.  This is mostly API engineering, but it is brittle.

If projective associativity is unavailable, the fallback is to prove the universal identity in a fraction field of the universal power-series ring and inject back.  That avoids custom Laurent series, but it increases algebraic overhead.

## (d) Size estimate

Assuming a usable projective Weierstrass addition API already exists:

```text
w(t) existence/uniqueness:              250–500 lines
formal point + substitution helpers:    150–300 lines
formal addition and Y-unit lemmas:       250–500 lines
linear coefficient proofs:              100–250 lines
associativity wrapper:                  300–700 lines
generic n-series tangent lemma:         150–300 lines
-----------------------------------------------------
total:                                1,200–2,500 lines
```

If projective associativity or coordinate addition has to be formalized from scratch, the estimate jumps to roughly

```text
4,000–8,000 lines
```

because the projective group-law algebra, normalization, and substitution compatibility become the main proof burden.

A pragmatic milestone split:

```text
Milestone 1: w(t), formal point, F definition, linear coefficients.
Milestone 2: associativity via existing projective group law.
Milestone 3: n-series linear coefficient = n for any FormalGroup.
Milestone 4: division-polynomial compatibility and tangent bridge.
```

## (e) How Mathlib's `RingTheory/FormalGroup/Basic.lean` helps

It helps as the target API and proof style, but it does not remove the Weierstrass-specific work.

Useful parts:

* `FormalGroup` already has exactly the fields we need:

  ```lean
  toPowerSeries
  zero_constantCoeff
  lin_coeff_X
  lin_coeff_Y
  assoc
  ```

* The associativity field is already phrased in terms of `MvPowerSeries.subst`, so our `F` should be built directly as an `MvPowerSeries (Fin 2) K`.

* `additiveFormalGroup` and `multiplicativeFormalGroup` are good templates for how to prove the linear coefficient and associativity fields using `simp`, `subst_add`, `subst_mul`, and `subst_X`.

* `FormalGroup.map` is important.  It strongly suggests the universal-first construction:

  ```text
  build once over ℤ[a₁,a₂,a₃,a₄,a₆], then map coefficients to K.
  ```

* If the pinned Mathlib version has group/point instances for formal group laws over the evaluation ideal, those can help later for the tangent bridge and for defining/using the formal `[n]`-series.  They are not, by themselves, enough to construct `W.formalGroup`; the Weierstrass addition law and associativity proof still have to be supplied.

I would also add a small local API if Mathlib does not already provide it:

```lean
def FormalGroup.nseries (F : FormalGroup K) : ℕ → PowerSeries K
lemma nseries_zero
lemma nseries_succ
lemma coeff_one_nseries : coeff 1 (F.nseries n) = (n : K)
```

The proof of `coeff_one_nseries` uses only `lin_coeff_X = 1` and `lin_coeff_Y = 1`; it should be independent of Weierstrass curves.

## Tangent bridge to division polynomials

Once `W.formalGroup` exists, the bridge should be separated into two independent layers.

### Layer 1: pure formal-group tangent theorem

For any formal group law `F` over `K`, prove:

```text
[n]_F(T) = nT + O(T²).
```

In dual numbers this gives

```text
[n]_F(ε c) = ε · n · c.
```

Lean shape:

```lean
lemma coeff_one_nseries (F : FormalGroup K) (n : ℕ) :
  coeff 1 (F.nseries n) = (n : K)
```

and then a dual-number corollary.

### Layer 2: Weierstrass/division-polynomial identification

Prove that for the formal point

```text
P(T) = [T:-1:w(T)],
```

projective multiplication by `n` agrees with the division-polynomial projective formula:

```text
[n]P(T) = [Φ_n(P(T)) : Ω_n(P(T)) : Ψ_n(P(T))]
```

with the repository's exact conventions.  Then

```text
t([n]P(T)) = -X([n]P(T)) / Y([n]P(T)) = [n]_F(T).
```

Taking the coefficient of `T` gives `(n : K)`.  Substituting `T = ε c` gives

```text
coeffε(t([n]Pε)) = (n : K) · c.
```

For a non-identity point `P`, `c` must be the coefficient of a source local parameter normalized by the invariant differential, not necessarily the coefficient of the global affine function `-x/y`.  The formal group lives at `O`; nonzero torsion points enter by translating the local parameter to `O` before applying the theorem.

## Final design choice

My preferred construction is:

```text
1. Define w(t) as the unique ordinary PowerSeries solving the Weierstrass local equation.
2. Use projective coordinates P(t) = [t:-1:w(t)].
3. Define F(T₁,T₂) = -X/Y from projective addition P(T₁)+P(T₂).
4. Prove linear coefficients by first-order truncation.
5. Prove associativity using projective group-law associativity plus Y-unit normalization.
6. Use Mathlib FormalGroup.map to specialize from the universal coefficient ring.
7. Prove the generic n-series tangent theorem once for all FormalGroup laws.
8. Connect to division polynomials by showing their projective formula computes the same [n]P(T).
```

This is the shortest path I see that respects the `PowerSeries` constraint while keeping the final tangent bridge aligned with the projective division-polynomial formulas.
