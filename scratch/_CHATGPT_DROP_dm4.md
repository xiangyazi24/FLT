# Q514 / dm4 — Bypass full `FormalGroup`: prove the `[n]` tangent scalar directly from finite-point formulas

## Executive answer

Yes, this is a plausible bypass of the full `W.formalGroup : FormalGroup K` construction **for the tangent bridge only**. But the proposed statement needs two important corrections.

1. The additive tangent coordinate is **not** the raw `dx` or `dy` coefficient. It is the coordinate defined by the invariant differential

```text
ω = dx / (2y + a₁x + a₃)
```

on the chart where `2y + a₁x + a₃ ≠ 0`, with the alternative `dy`-chart at 2-torsion points. Addition is additive on this invariant-differential coordinate.

2. The final induction step where `(n-1)P + P = O` is **not** an affine secant computation. The affine denominator has zero scalar part, hence is not invertible in `K[ε]`. That endpoint still needs a projective/local-parameter computation using `addXYZ` or a special vertical-addition lemma.

So the corrected route is:

```text
finite secant/doubling tangent lemmas
  + one vertical endpoint lemma into the local parameter at O
  + induction along the finite orbit P, 2P, ..., (n-1)P, O
```

This can bypass full formal groups. It probably is shorter than constructing a genuine `FormalGroup K`, but it is **not** just one affine `K[ε]` lemma.

## Mathlib surface checked

The repo pins Mathlib at

```toml
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

Relevant files:

```text
Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean
Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean
```

`Affine/Formula.lean` has exactly the branch formulas one would want to differentiate:

```lean
WeierstrassCurve.Affine.negY
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.negAddY
WeierstrassCurve.Affine.addY
```

The file documents the affine slope branches:

```text
if x₁ ≠ x₂,       ℓ = (y₁ - y₂) / (x₁ - x₂)
if P = Q nonvert, ℓ = (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)
```

and then

```text
x(P+Q) = ℓ² + a₁ℓ - a₂ - x₁ - x₂
y(P+Q) = -(ℓ(x(P+Q)-x₁)+y₁) - a₁x(P+Q) - a₃.
```

`Affine/Point.lean` builds the actual point group law over a **field** and proves `AddCommGroup W.Point`. This is useful for scalar/base points, but it does **not** give a group law over `K[ε]`, because `K[ε]` is not a field.

That is the first Lean implementation warning: do not try to instantiate `W.Point` over `TrivSqZeroExt K K`. Instead, differentiate the branch formulas over `K` or define branch-specific dual-number formulas with explicit inverses for denominators whose scalar part is nonzero.

## Why the raw `K[ε]` affine statement is too optimistic

The proposed lemma was:

```text
for P,Q distinct finite affine points over K[ε],
tangent(P+Q) decomposes additively.
```

This needs to be narrowed.

### Problem 1: `K[ε]` is not a field

Mathlib's `Affine.Point` group law is over fields. The dual numbers are a commutative ring with nilpotents, not a field. So the existing field-level `slope` and `Point.add` API cannot be used directly over `K[ε]`.

For the secant branch with distinct **reductions** `x₁ ≠ x₂` over `K`, the denominator

```text
(x₁ + ε dx₁) - (x₂ + ε dx₂)
```

has nonzero scalar part and is a unit in `K[ε]`. That branch is fine, but Lean should use either:

* an explicit inverse formula for dual units; or
* ordinary derivative formulas over `K`, avoiding division in the dual ring.

### Problem 2: dual-number distinctness is not enough

If the reductions have the same `x`-coordinate, the affine denominator may be nilpotent. For example, in the final vertical step, the scalar denominator is zero. Then it is not a unit in `K[ε]`, so the affine secant formula is not valid.

The branch condition should be scalar/open-chart data such as:

```lean
hx : x₁ ≠ x₂
```

not merely `Pε ≠ Qε` in the dual ring.

### Problem 3: addition is additive only after the right tangent trivialization

For a finite nonsingular point `(x,y)`, the tangent equation is the linearization of the Weierstrass equation. In one common convention,

```text
F(x,y) = y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆,
```

so a tangent vector `(dx,dy)` satisfies

```text
(a₁y - 3x² - 2a₂x - a₄) dx + (2y + a₁x + a₃) dy = 0.
```

The invariant-differential coordinate is

```text
θ(x,y; dx,dy) = dx / (2y + a₁x + a₃)
```

when `2y + a₁x + a₃ ≠ 0`. At a 2-torsion point this denominator vanishes, and one must use the equivalent `dy` formula on the other nonsingular chart.

The correct local statement is not

```text
dx(P+Q) = dx(P) + dx(Q),
```

but rather

```text
θ(P+Q; d(P+Q)) = θ(P; dP) + θ(Q; dQ).
```

This is the algebraic form of

```text
m^*ω = pr₁^*ω + pr₂^*ω
```

for the group law.

## Correct finite-point lemma package

The route should be organized into branch lemmas, not one giant dual-number theorem.

### 1. Tangent data and invariant coordinate

Use definitions like:

```lean
namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

-- Name only; exact polynomial signs should match Mathlib's `polynomialX/polynomialY` convention.
def TangentAt (x y dx dy : K) : Prop :=
  W.polynomialX.evalEval x y * dx + W.polynomialY.evalEval x y * dy = 0

-- On the non-2-torsion finite chart.
def psi (x y : K) : K :=
  y - W.negY x y       -- equals 2*y + a₁*x + a₃ after simp/ring

noncomputable def omegaCoord (x y dx dy : K) : K :=
  dx / W.psi x y

end WeierstrassCurve.Affine
```

For an input deformation of the form

```text
Pε = (x + ε, y + ε s),
```

`(1,s)` must satisfy the tangent equation. Its invariant coordinate is generally

```text
1 / (2y + a₁x + a₃),
```

not `1`. If the target theorem wants output coefficient `n`, normalize the input tangent vector so that `θ = 1`; if the input is `dx = 1`, expect output coefficient

```text
n / (2y + a₁x + a₃)
```

up to the sign convention of the local parameter at `O`.

### 2. Secant tangent-addition lemma

For scalar finite points with `x₁ ≠ x₂`, define the derivative of the affine formulas explicitly.

Mathematically:

```text
ℓ  = (y₁ - y₂)/(x₁ - x₂)
dℓ = ((dy₁ - dy₂)(x₁ - x₂) - (y₁ - y₂)(dx₁ - dx₂))/(x₁ - x₂)²

x₃  = ℓ² + a₁ℓ - a₂ - x₁ - x₂
dx₃ = (2ℓ + a₁)dℓ - dx₁ - dx₂

y₃  = -(ℓ(x₃-x₁)+y₁) - a₁x₃ - a₃
dy₃ = -(dℓ(x₃-x₁) + ℓ(dx₃-dx₁) + dy₁) - a₁dx₃
```

Then prove:

```text
TangentAt(x₁,y₁,dx₁,dy₁)
TangentAt(x₂,y₂,dx₂,dy₂)
x₁ ≠ x₂
---------------------------------------------
TangentAt(x₃,y₃,dx₃,dy₃)
omegaCoord(x₃,y₃,dx₃,dy₃)
  = omegaCoord(x₁,y₁,dx₁,dy₁)
  + omegaCoord(x₂,y₂,dx₂,dy₂)
```

Lean proof style: expand definitions, use `field_simp` with the nonzero denominators, then `ring`/`ring_nf`. This is a finite calculation over `K`.

This is probably much easier than a multivariate `MvPowerSeries` associativity proof.

### 3. Doubling tangent lemma

For `P = Q` with `P` not 2-torsion, use the tangent-line slope branch:

```text
ℓ = (3x² + 2a₂x + a₄ - a₁y)/(2y + a₁x + a₃).
```

Differentiate this formula and prove:

```text
omegaCoord(d(2P)) = 2 * omegaCoord(dP).
```

Again this is finite `field_simp` + `ring`, but it is a separate branch. It is needed for the first induction step `[2]Q = Q + Q` unless the proof starts from a projective `dblXYZ` tangent lemma.

### 4. Vertical endpoint lemma into `O`

This is the unavoidable endpoint.

If `R = -P`, then `R + P = O`. For deformations

```text
Rε near R,
Pε near P,
```

the affine secant denominator has zero scalar part. It is not invertible in `K[ε]`. Therefore the affine formula cannot compute the output near `O`.

The correct endpoint lemma is projective/local:

```text
localParameterCoeffAtO(addXYZ(Rε, Pε))
  = omegaCoord(R; dR) + omegaCoord(P; dP)
```

with the sign fixed by the chosen convention for the local parameter at infinity, e.g. `t = -X/Y` or `t = -XZ/Y` depending on the projective representative convention.

This is still only a **finite dual-number computation**, not a full formal group construction. It should be much smaller than proving full `(X₀-X₁)^3` normalization as a two-variable power-series identity.

But it means the route is not purely affine.

## Induction theorem shape

Assume `P` has exact order `n` and, for the simplest version, assume the orbit avoids 2-torsion on the finite steps where the `dx/ψ` chart is used. For odd exact order this avoids the main chart-switching problem. For even order, `(n/2)P` is 2-torsion and one must either switch charts or add a 2-torsion branch lemma.

A clean theorem statement should look more like:

```lean
-- P is finite, nonsingular, exact order n, with a tangent vector v at P.
-- `thetaP` is the invariant-differential coordinate of v.
theorem localCoeff_nsmul_torsion_direct
    {n : ℕ} {P : W.Point} {v : TangentVectorAt P}
    (hPfin : P is finite)
    (horder : exact_order P n)
    (hchart : orbit_chart_good P n)
    (htangent : tangent vector data is valid) :
  coeffε (localParameterAtO ([n] (P + ε v))) = (n : K) * thetaP := by
  -- induction on k
  -- k = 1: identity
  -- k = 2: doubling lemma
  -- 2 < k < n: secant finite-add lemma
  -- k = n: vertical endpoint lemma
```

More concretely, maintain an induction invariant:

```text
For 1 ≤ k < n,
  [k](Pε) is a deformation of kP with invariant coordinate k * θ(Pε).
```

Then:

* `k = 1`: immediate.
* `k = 2`: finite doubling lemma, unless `2P=O`.
* `2 ≤ k ≤ n-2`: add the deformation of `kP` to the original deformation of `P`; use the secant lemma, because for exact order `n`, `kP` is neither `P` nor `-P` in the generic range.
* `k = n-1`: `kP = -P`; use the vertical endpoint lemma to land in the local parameter at `O`.

The final result is:

```text
local t coefficient of [n](Pε) = n * θ(Pε).
```

If `Pε = (x + ε, y + εs)` with `dx = 1`, then `θ(Pε) = 1 / (2y + a₁x + a₃)` on the non-2 chart. So the output is not literally `n` unless the input tangent was normalized to have invariant coordinate `1`.

## What this bypasses and what it does not

### It bypasses

* defining `F(T₁,T₂)` as a full `MvPowerSeries`;
* proving `FormalGroup.assoc`;
* proving full two-variable associativity / formal group law identities;
* proving the complete `(X₀-X₁)^3` normalization for all formal variables, if the only target is the tangent scalar.

### It does not bypass

* differentiating the affine add/double formulas;
* handling branch conditions (`secant`, `doubling`, `vertical endpoint`);
* one projective/local calculation at `O`;
* chart-switching at 2-torsion orbit points, unless excluded;
* exact-order/orbit bookkeeping.

## Lean implementation recommendation

Do **not** phrase the first lemmas over dual-number `Point`s. Instead define branchwise derivative formulas over `K`.

Recommended order:

1. Define `TangentAt` and `omegaCoord` for finite affine points.
2. Prove the finite secant derivative lemma in ordinary field algebra.
3. Prove the finite doubling derivative lemma in ordinary field algebra.
4. Prove the vertical endpoint lemma using `Projective.addXYZ`/local parameter over `TrivSqZeroExt K K`.
5. Assemble the exact-order induction.

This avoids fighting `K[ε]` as a non-field and avoids `if` branches in `Affine.slope`.

A branch lemma skeleton:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

open WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve.Affine K)

noncomputable def psi (x y : K) : K :=
  y - W.negY x y

-- Use the exact `polynomialX/polynomialY` convention from Mathlib.
def TangentAt (x y dx dy : K) : Prop :=
  W.polynomialX.evalEval x y * dx + W.polynomialY.evalEval x y * dy = 0

noncomputable def omegaCoord (x y dx dy : K) : K :=
  dx / W.psi x y

-- Secant branch: scalar reductions have x₁ ≠ x₂.
theorem omegaCoord_add_secant
    {x₁ y₁ x₂ y₂ dx₁ dy₁ dx₂ dy₂ : K}
    (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂)
    (ht₁ : W.TangentAt x₁ y₁ dx₁ dy₁)
    (ht₂ : W.TangentAt x₂ y₂ dx₂ dy₂) :
    -- after defining ℓ,dℓ,x₃,y₃,dx₃,dy₃:
    True := by
  -- expand definitions; `field_simp [hx, ...]`; `ring_nf`
  trivial

-- Doubling branch: non-vertical tangent.
theorem omegaCoord_dbl
    {x y dx dy : K}
    (h : W.Nonsingular x y)
    (hpsi : W.psi x y ≠ 0)
    (ht : W.TangentAt x y dx dy) :
    -- omegaCoord of the doubled tangent = 2 * omegaCoord of input
    True := by
  -- expand definitions; `field_simp [hpsi, ...]`; `ring_nf`
  trivial

end WeierstrassCurve.Affine
```

The real theorem bodies should not leave `True`; this is just the recommended decomposition. The point is that each branch is a finite rational identity over `K`.

## Verdict

This route is worth pursuing if the only required result is the tangent scalar used in the division-polynomial bridge:

```text
coeffε(t([n](Pε))) = n * θ(Pε).
```

It is likely shorter than constructing the full Weierstrass `FormalGroup`. But the viable proof is not the naive affine addition over `K[ε]`; it is a branchwise proof using the invariant differential, plus one projective vertical endpoint computation. If you restrict to exact odd order and non-2-torsion charts, the induction becomes much cleaner. For general `n`, chart switching and earlier hits of `O` must be handled explicitly.
