# Q177 (dm1): path selection for the projective bridge / `Ωₙ`

## Executive ranking

The critical API check changes the ranking slightly:

```text
Mathlib.Jacobian.Formula.addXYZ / dblXYZ       works over CommRing representatives
Mathlib.Jacobian.Point group law               field-only
```

So Path C is **not** available as a ready-made group law over `K[ε]`, but its raw coordinate polynomials are available over `TrivSqZeroExt K K`.  That makes Path C useful as a source of polynomial formulas, not as a turnkey `nsmul` over dual numbers.

My path ranking is:

```text
1. Path A / A+C hybrid: define Ωₙ and prove projective division-polynomial formula.
   Use Mathlib's ring-level Jacobian coordinate polynomials as checking/proof support.

2. Path C pure raw-Jacobian recursion over K[ε].
   Promising for experiments, but for general n it becomes a re-proof of the division-polynomial
   projective formula and has exceptional-case bookkeeping.

3. Path B coordinate-ring-only without Ωₙ.
   Not recommended; affine `mk_φ` and `mk_Ψ_sq` do not see the local parameter at O.
```

The shortest robust formalization is therefore **Path A with support from the existing `Jacobian.Formula` ring-level coordinate formulas**.  In other words: add the missing `Ωₙ`/`ωₙ` object and the projective formula, but do not build a full group law over dual numbers.

---

## (a) Path C API check: does `Jacobian.addXYZ` work over `CommRing`?

Yes for the raw formulas.

In pinned Mathlib, `Jacobian/Formula.lean` has the ambient variables

```lean
variable {R S A F B K : Type*}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Field F] [Field K]
  {W' : Jacobian R} {W : Jacobian F}
```

and the coordinate formula definitions are ring-level:

```lean
def dblXYZ (W' : Jacobian R) (P : Fin 3 → R) : Fin 3 → R

def addXYZ (W' : Jacobian R) (P Q : Fin 3 → R) : Fin 3 → R
```

Their map/base-change lemmas are also ring-level.  This is good news: we can evaluate those coordinate polynomials in

```lean
R := TrivSqZeroExt K K.
```

But `Jacobian/Point.lean` is still a field-level group-law file.  Its docstring and variables are explicitly about nonsingular Jacobian points over a field, and `Point.instAddCommGroup` is built by comparison with affine points over fields.  So there is no packaged

```lean
AddCommGroup ((W.map ... over TrivSqZeroExt K K).Jacobian.Point)
```

that we can use directly.

### Consequence for Path C

Path C is not “just compute `[n]Pε` by `nsmul` over `K[ε]`.”  You would need to define your own raw recursive multiplication using `dblXYZ`/`addXYZ` and then prove that it represents the actual multiplication-by-`n` functor.  For general `n`, that proof is essentially the projective division-polynomial theorem.

A small experimental Path C target is still useful:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open MvPolynomial

namespace WeierstrassCurve
namespace Jacobian

noncomputable section

variable {K : Type*} [Field K]

abbrev Dual (K : Type*) [Field K] := TrivSqZeroExt K K

-- Raw coordinate formulas are available over the dual-number ring.
#check WeierstrassCurve.Jacobian.dblXYZ
#check WeierstrassCurve.Jacobian.addXYZ
#check WeierstrassCurve.Jacobian.map_dblXYZ
#check WeierstrassCurve.Jacobian.map_addXYZ

end

end Jacobian
end WeierstrassCurve
```

But this is not yet the group law over dual numbers.

---

## (b) Exact `ωₙ` definition matching Mathlib’s normalization

Mathlib’s `DivisionPolynomial.Basic` documentation states exactly the intended definition, and it is the normalization to use.

For the bivariate division polynomials:

```text
φₙ := X ψₙ² - ψₙ₊₁ ψₙ₋₁
```

and

```text
ωₙ := (ψ₂ₙ / ψₙ - ψₙ · (a₁ φₙ + a₃ ψₙ²)) / 2.
```

Equivalently, to avoid exposing polynomial division in the statement, define/prove `ωₙ` by the identity

```text
2 ψₙ ωₙ = ψ₂ₙ - ψₙ² · (a₁ φₙ + a₃ ψₙ²).
```

Then the affine multiplication formula is

```text
[n]P = ( φₙ(P) / ψₙ(P)² ,  ωₙ(P) / ψₙ(P)³ )
```

when `ψₙ(P) ≠ 0`, and the Jacobian/projective form is

```text
[n]P = [ φₙ(P) : ωₙ(P) : ψₙ(P) ]
```

in weighted Jacobian coordinates, where affine coordinates are recovered by

```text
x = X / Z²,
y = Y / Z³.
```

This is the formula compatible with Mathlib’s `Jacobian` coordinates.  In the local parameter

```text
t = -x/y = -X*Z/Y,
```

one gets

```text
t([n]P) = - φₙ(P) * ψₙ(P) / ωₙ(P).
```

This corrects the earlier shorthand `-Φ·Ψ/Ω`: the actual Jacobian-coordinate statement is

```text
X_n = φₙ,
Y_n = ωₙ,
Z_n = ψₙ,
t = -X_n Z_n / Y_n.
```

### Silverman reference

This is the standard division-polynomial formula in Silverman, *The Arithmetic of Elliptic Curves*, Chapter III, §2, in the division-polynomial discussion: the formulas defining `φ_m` and `ω_m`, followed by

```text
x(mP) = φ_m(P)/ψ_m(P)^2,
y(mP) = ω_m(P)/ψ_m(P)^3.
```

The exact numbering differs by edition/printing; in the common second-edition citation this is the formula package around Chapter III, §2, Proposition/Theorem 2.3.  It is also precisely the formula copied into the Mathlib `DivisionPolynomial.Basic` module docstring.

### Lean definition strategy

There are two levels.

#### Char not 2 / application-level definition

If you only care about characteristic zero first, you can define `ωₙ` using division by `2` and the quotient `ψ₂ₙ / ψₙ` after proving divisibility:

```lean
noncomputable def omegaAux
    {K : Type*} [Field K] (W : WeierstrassCurve K) (n : ℤ) : K[X][Y] :=
  ((W.ψ (2*n)) / (W.ψ n)
    - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)) / 2
```

This is Lean-convenient in characteristic not `2`, but it is **not** the right final general theorem if you want `(n : K) ≠ 0` in characteristic `2` for odd `n`.

#### Integral/universal definition

For the final Mathlib-quality definition, define `ωₙ` integrally over the universal Weierstrass ring, or define it by a recurrence / quotient theorem proving the numerator is divisible by `2 ψₙ`.  The identity to expose should be:

```lean
/-- Defining identity for the bivariate `ωₙ`. -/
theorem two_mul_ψ_mul_ω
    (W : WeierstrassCurve R) (n : ℤ) :
    (2 : R[X][Y]) * W.ψ n * W.ω n =
      W.ψ (2*n)
        - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  sorry
```

Then the projective formula target is:

```lean
/-- Projective/Jacobian division-polynomial formula. -/
theorem jacobian_nsmul_eq_division_polynomials
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℤ) (P : /* affine or Jacobian point */) :
    /* [n]P is represented by ![φₙ(P), ωₙ(P), ψₙ(P)] */ := by
  sorry
```

For the separability bridge, you need only this formula over dual numbers and only near `ψₙ=0`.

---

## (c) Path C proof sketch if using raw Jacobian formulas over `K[ε]`

Because `addXYZ`/`dblXYZ` are polynomial formulas over any `CommRing`, one can define a raw recursive multiplication over dual numbers:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open MvPolynomial

namespace WeierstrassCurve
namespace Jacobian

noncomputable section

variable {K : Type*} [Field K]
variable (W : Jacobian (TrivSqZeroExt K K))

/-- Raw double-and-add representative.  This is not yet a quotient/group-law statement. -/
def rawMulXYZ : ℕ → (Fin 3 → TrivSqZeroExt K K) → (Fin 3 → TrivSqZeroExt K K)
  | 0, _ => ![1, 1, 0]  -- O in Jacobian coordinates, up to the convention in Mathlib
  | 1, P => P
  | n + 2, P =>
      -- This is schematic.  A real definition should use a stable recursion aligned with
      -- `normEDSRec`, with `dblXYZ` for doubling and `addXYZ` for addition of distinct terms.
      W.addXYZ (rawMulXYZ (n + 1) P) P

end

end Jacobian
end WeierstrassCurve
```

But this naive recursion is not good enough.  `addXYZ` is documented as the formula for two **distinct** representatives; if the representatives are equal, `addXYZ P P = ![0,0,0]`, while `dblXYZ P` is the doubling formula.  Therefore a correct raw multiplication recursion must branch/use `dblXYZ` for doubling and `addXYZ` only for appropriate additions.

The natural recursion is not plain repeated addition.  It should be aligned with the division-polynomial EDS recursion:

```text
n = 2m      use dblXYZ(raw mP)
n = 2m+1    use addXYZ(raw (m+1)P) (raw mP) or equivalent
```

Then the theorem you need is:

```lean
/-- Raw Jacobian multiplication is represented by division polynomials. -/
theorem rawMulXYZ_eq_division_polynomials
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K}
    (hP : W.Equation x y) :
    -- after evaluating in the dual ring too:
    -- rawMulXYZ n ![xε, yε, 1] is equivalent to ![φₙ(Pε), ωₙ(Pε), ψₙ(Pε)]
    True := by
  -- This is a general-n induction and is basically the projective formula theorem.
  sorry
```

Once that is available, the desired first-order statement is easy.  Suppose

```text
ψₙ(P) = 0,
ψₙ(Pε) = ε·u,
φₙ(P) ≠ 0,
ωₙ(P) ≠ 0.
```

Then

```text
[n]Pε = [φₙ(Pε) : ωₙ(Pε) : ψₙ(Pε)]
```

and the local parameter coefficient at `O` is

```text
t([n]Pε) = -X Z / Y
          = -φₙ(Pε) ψₙ(Pε) / ωₙ(Pε)
          = ε · ( -φₙ(P) * u / ωₙ(P) ).
```

For the reduced polynomial at a non-2-torsion point,

```text
u = coeffε(ψₙ(Pε))
  = unit_ψ₂(P) * dx * (preΨ'_n)'(x)
```

with the unit factor present only in the even case.

So the concrete Path C local proof target is:

```lean
/-- Local-parameter coefficient from raw/projective coordinates. -/
theorem localCoeff_t_nsmul_eq_unit_mul_dpreΨ'
    {n : ℕ} {x y dx dy : K}
    (hPε : /* dual point */)
    (hψ : /* ψₙ(P)=0 */)
    (hφ : /* φₙ(P) ≠ 0 */)
    (hω : /* ωₙ(P) ≠ 0 */) :
    /* coeffε(t([n]Pε)) */
      = (- (/* φₙ(P) */) / (/* ωₙ(P) */))
          * (/* ψ₂ unit factor */) * dx * (derivative (W.preΨ' n)).eval x := by
  -- Expand `t = -X*Z/Y` and use dual-number Taylor on ψₙ/preΨ'ₙ.
  sorry
```

But again, proving `rawMulXYZ_eq_division_polynomials` is essentially Path A.

---

## (d) Does `Ωₙ(P) ≠ 0` follow from existing Mathlib facts?

Not directly.

There are three levels:

### 1. From projective equation plus `φₙ(P) ≠ 0`

If you have the projective formula

```text
[n]P = [φₙ(P) : ωₙ(P) : ψₙ(P)]
```

and `ψₙ(P)=0`, then the weighted projective Weierstrass equation at `Z=0` gives

```text
ωₙ(P)^2 = φₙ(P)^3
```

(up to the sign/convention of Mathlib’s Jacobian equation; in its coordinates, the point at infinity representatives are weighted-equivalent to `![1,1,0]`).  Hence

```text
φₙ(P) ≠ 0 → ωₙ(P) ≠ 0.
```

So `ωₙ(P) ≠ 0` does not need an independent resultant if you already have `φₙ(P) ≠ 0` and the projective equation.

### 2. But `φₙ(P) ≠ 0` is itself a no-common-root theorem

At `ψₙ(P)=0`, proving `φₙ(P) ≠ 0` is the statement that the projective representative is not `![0,0,0]` and actually represents `O`.  In univariate reduced form, this is the no-common-root theorem

```lean
¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)
```

or the equivalent bivariate statement for `φₙ` and `ψₙ` at a non-2-torsion point.

This is **not** a theorem supplied by `mk_φ` / `mk_Ψ_sq` alone.  Those identify coordinate-ring expressions; they do not prove the no-common-root/nonzero-coordinate property at torsion roots.

### 3. Mathlib currently has no packaged `ωₙ`, hence no packaged `ωₙ(P)≠0`

Since `ωₙ` is a TODO in `DivisionPolynomial.Basic`, there is no existing theorem like

```lean
theorem omega_ne_zero_of_psi_eq_zero ...
```

in Mathlib.

Thus answer:

```text
Ωₙ(P)≠0 follows from projective formula + φₙ(P)≠0 + equation at Z=0,
but neither Ωₙ nor this theorem is currently packaged.
```

If your repo already has a non-circular `Φ/ΨSq` no-common-root theorem, reuse it.  Otherwise this remains a separate seam.

---

## Path-by-path critical checks

### Path A: define `ωₙ` and prove projective formula

Critical checks:

1. Can define `ωₙ` integrally, not only by division by `2`, if the final theorem must include characteristic `2`.
2. Prove
   ```text
   [n]P = [φₙ(P) : ωₙ(P) : ψₙ(P)]
   ```
   in Jacobian coordinates.
3. Prove or import no-common-root `φₙ(P) ≠ 0` at `ψₙ(P)=0`.
4. Then get `ωₙ(P)≠0` from the equation at `Z=0`.
5. Dual-number local parameter computation is then short:
   ```text
   t = -X*Z/Y = -φₙ ψₙ / ωₙ.
   ```

Estimated difficulty: medium-high, but coherent and aligned with Mathlib’s TODO.

### Path B: coordinate ring / formal completion without `ωₙ`

Critical check:

```text
Can you express the local parameter t at O using only mk_φ and mk_Ψ_sq?
```

Answer: no, not without adding the missing target `Y` coordinate or a projective/formal-completion chart.  `mk_φ` and `mk_Ψ_sq` describe affine `x([n]P)`, which has a pole at `O`; they do not describe `t=-x/y`.

Estimated difficulty: high and likely to collapse back into Path A.

### Path C: raw Jacobian formulas over `K[ε]`

Critical checks:

1. Raw formulas `dblXYZ`/`addXYZ` are available over `CommRing`: yes.
2. Packaged group law over `TrivSqZeroExt K K`: no.
3. Need a custom raw multiplication recursion using `dblXYZ` and `addXYZ`, not naive repeated addition.
4. Need proof raw recursion equals division-polynomial coordinates: this is essentially Path A.
5. Exceptional cases must be controlled: `addXYZ P P = ![0,0,0]`, so the recursion must use `dblXYZ` for doubling.

Estimated difficulty: medium-high as an experimental route, high as a general theorem.  It is not lighter than Path A unless you only prove a few fixed-`n` cases.

---

## Recommended concrete next step

Do **not** start with a full `ωₙ` for all uses.  Start by adding the minimal object and theorem shape that the separability bridge needs:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- TODO: bivariate `ωₙ`, the missing projective Y-coordinate division polynomial. -/
noncomputable def omegaDivPoly (n : ℤ) : K[X][Y] := by
  -- First implementation can assume char ≠ 2 / use quotient if your immediate target is char 0.
  -- Final implementation should be integral/universal.
  exact 0

/-- Defining identity for `omegaDivPoly`, avoiding affine division in downstream proofs. -/
theorem two_mul_psi_mul_omegaDivPoly (n : ℤ) :
    (2 : K[X][Y]) * W.ψ n * W.omegaDivPoly n =
      W.ψ (2*n)
        - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  sorry

/-- Projective/Jacobian division-polynomial formula. -/
theorem jacobian_nsmul_eq_phi_omega_psi
    (n : ℤ) {x y : K}
    (hP : W.Equation x y) :
    -- Schematic:
    -- `[n]![x,y,1]` is represented by
    --   ![φₙ(x,y), omegaDivPolyₙ(x,y), ψₙ(x,y)]
    True := by
  sorry

/-- Local parameter at O from projective division-polynomial coordinates. -/
theorem localParameter_nsmul_eq_neg_phi_mul_psi_div_omega
    (n : ℤ) {x y : K}
    (hP : W.Equation x y)
    (homega : /* omegaDivPoly_n(P) */ True) :
    -- Schematic: t([n]P) = -φₙ(P)*ψₙ(P)/ωₙ(P)
    True := by
  sorry

end

end WeierstrassCurve
```

For Round 4 I would focus only on the exact `omegaDivPoly` definition strategy:

```text
char-0-only quotient definition first, or universal integral definition now?
```

Given the application is char 0, a char-0 prototype is likely the fastest way to validate the bridge, but the final theorem for `(n : K) ≠ 0` in arbitrary characteristic will eventually need the integral definition.

## Final recommendation

Choose **Path A+C hybrid**:

```text
Use Mathlib's ring-level Jacobian coordinate formulas as the polynomial backbone,
but add the missing ωₙ / Ωₙ object and projective division-polynomial theorem.
```

Do not choose pure Path B.  Do not rely on packaged Path C group law over dual numbers; it is field-only at the point/group layer.  The raw formulas are valuable, but the projective division-polynomial theorem is the real deliverable.
