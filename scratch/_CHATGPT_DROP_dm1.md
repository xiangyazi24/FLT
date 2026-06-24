# Q181 (dm1): `ωₙ` / projective bridge implementation atoms

## Executive refinement

Your decomposition is close, but I would change two important things before coding:

1. **Do not define `ωₙ` by polynomial division by `W.ψ n`.**  In Mathlib, `K[X][Y]` means `Polynomial (Polynomial K)`, whose coefficient ring `K[X]` is not a field.  A Euclidean quotient by an arbitrary bivariate polynomial is not the right primitive here, and even if a quotient can be forced via a fraction field, it is the wrong object.  Use the existing EDS complement sequence instead.

2. **Merge ATOM 3 and ATOM 4 into one projective-formula seam.**  A coordinate-ring identity such as `mk_ω_eq_y_mul_ψ_cubed` is not the correct global object: `ωₙ/ψₙ³` is an affine chart formula on the open where `ψₙ ≠ 0`, while the bridge needs the projective representative at `ψₙ = 0`.  The real theorem is a homogeneous/Jacobian representative theorem:

```text
[n]P is represented by [φₙ(P) : ωₙ(P) : ψₙ(P)]
```

in weighted Jacobian coordinates.

The EDS complement discovery is valuable: it makes ATOM 1/2 much cleaner.  The hard part remains the projective formula and its normalization, not the quotient `ψ₂ₙ/ψₙ`.

---

## Revised atom list

### ATOM 0: bivariate evaluation and dual-number boilerplate

**Status:** mostly already exists / easy wrappers.

You need a consistent way to evaluate `K[X][Y]` at `(x,y)` and at dual-number points `(xε,yε)`.

Suggested local wrappers:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluation of a bivariate polynomial `K[X][Y]` at `(x,y)`. -/
abbrev evalBivar (f : K[X][Y]) (x y : K) : K :=
  f.eval y |>.eval x

/-- Evaluation at a dual-number point. -/
abbrev evalBivarDual (f : K[X][Y])
    (x y : TrivSqZeroExt K K) : TrivSqZeroExt K K :=
  f.eval y |>.eval x

end

end WeierstrassCurve
```

If your repo already has this under a different name, use that.  This atom is not mathematically hard.

---

## ATOM 1: define the quotient `ψ₂ₙ / ψₙ` using `complEDS₂`

**Status:** easy/mechanical, because Mathlib already has the EDS quotient.

Mathlib has

```lean
W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
```

and the EDS file has

```lean
normEDS_mul_complEDS₂ :
  normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k)
```

So define the quotient polynomial as:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- The EDS complement polynomial representing `ψ₂ₙ / ψₙ`. -/
noncomputable def ψTwoMulQuot (n : ℤ) : K[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

@[simp] theorem ψ_mul_ψTwoMulQuot (n : ℤ) :
    W.ψ n * W.ψTwoMulQuot n = W.ψ (2 * n) := by
  simpa [WeierstrassCurve.ψ, ψTwoMulQuot]
    using (normEDS_mul_complEDS₂ (b := W.ψ₂) (c := C W.Ψ₃) (d := C W.preΨ₄) n)

end

end WeierstrassCurve
```

This atom is the clean replacement for polynomial division by `W.ψ n`.

---

## ATOM 2: define `ωₙ` in the characteristic-not-2 prototype

**Status:** easy/mechanical for char not 2; final integral version is genuinely harder.

For the char-zero / `2`-invertible prototype, define `ωₙ` using the EDS quotient and scalar multiplication by `2⁻¹`:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Prototype bivariate `ωₙ` over a field.  This version uses division by `2` as a scalar;
the final integral/general-characteristic version should avoid this definition. -/
noncomputable def ω (n : ℤ) : K[X][Y] :=
  C (C ((2 : K)⁻¹)) *
    (W.ψTwoMulQuot n
      - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2))

/-- Normalization identity for the prototype `ωₙ`. -/
theorem two_mul_ψ_mul_ω (h2 : (2 : K) ≠ 0) (n : ℤ) :
    (2 : K[X][Y]) * W.ψ n * W.ω n =
      W.ψ (2*n)
        - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  have hquot := W.ψ_mul_ψTwoMulQuot n
  -- This should be a short `linear_combination` / `ring_nf` proof using
  -- `2 * 2⁻¹ = 1` and `hquot`.
  -- Exact local proof shape:
  --   field_simp [ω, h2]
  --   linear_combination hquot
  sorry

end

end WeierstrassCurve
```

Do **not** use

```lean
(W.ψ (2*n)) / (W.ψ n)
```

as the definition in `K[X][Y]`.  The complement sequence is more canonical and avoids quotient ambiguity.

For the final arbitrary-characteristic theorem, ATOM 2 becomes hard: you must construct `ωₙ` integrally/universally, or prove that the prototype descends.  For char-zero this atom is small.

---

## ATOM 3/4: projective division-polynomial formula

**Status:** genuinely hard.  This is the main new theorem.

Your ATOM 3 coordinate-ring statement is not the right target.  The affine formula

```text
y([n]P) = ωₙ(P) / ψₙ(P)^3
```

only makes sense when `ψₙ(P) ≠ 0`.  At the torsion root, the needed object is the projective/Jacobian representative:

```text
[n]P = [φₙ(P) : ωₙ(P) : ψₙ(P)]
```

where Jacobian affine recovery is

```text
x = X / Z²,
y = Y / Z³.
```

Suggested theorem shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Schematic evaluated projective division-polynomial formula.  The actual RHS should be
converted to the local Jacobian/Projective point representation used in the file. -/
theorem nsmul_eq_jacobian_divPolyRep
    (n : ℤ) {x y : K}
    (hP : W.Equation x y) :
    -- `n • Point.some x y hP` is represented by
    -- `![evalBivar (W.φ n) x y, evalBivar (W.ω n) x y, evalBivar (W.ψ n) x y]`.
    True := by
  sorry

end

end WeierstrassCurve
```

### Does Mathlib already have this?

No.  Mathlib has:

```lean
WeierstrassCurve.ψ
WeierstrassCurve.φ
Affine.CoordinateRing.mk_ψ
Affine.CoordinateRing.mk_φ
Affine.CoordinateRing.mk_Ψ_sq
```

and it has raw Jacobian coordinate formulas:

```lean
Jacobian.dblXYZ
Jacobian.addXYZ
```

but it does **not** have the missing `ωₙ`, and it does not have a theorem like

```lean
n • Point.some x y h = Point.some (φₙ/ψₙ²) (ωₙ/ψₙ³) ...
```

Nor does it have the projective representative theorem.  ATOM 3/4 must be proved from scratch or added as the main bridge theorem.

### How to prove it non-circularly

Use the raw `Jacobian.Formula` coordinate polynomials and induction on `n`, not torsion/root counting.  The proof should compare a recursively defined projective representative with

```lean
![W.φ n, W.ω n, W.ψ n]
```

modulo the Weierstrass equation / up to weighted scalar equivalence.  This is a polynomial identity proof and does not require separability.

Expected size: >100 lines, likely several hundred.

---

## ATOM 5: `ωₙ(P) ≠ 0` at a `ψₙ`-root

**Status:** easy once ATOM 3/4 and Seam C are available.

You said Seam C is already proven:

```text
ψₙ(P)=0 and P non-2-torsion  ⇒  φₙ(P)≠0.
```

Then the projective representative

```text
[φₙ(P) : ωₙ(P) : 0]
```

lies on the Jacobian/projective curve.  At `Z=0`, the equation reduces, in Mathlib’s Jacobian normalization, to something equivalent to

```text
ωₙ(P)^2 = φₙ(P)^3
```

or with the exact `![1,1,0]` convention.  Hence `φₙ(P)≠0` implies `ωₙ(P)≠0` over a field.

Suggested theorem shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Nonzero `ωₙ` at a torsion root, from the projective equation at infinity and `φₙ≠0`. -/
theorem ω_eval_ne_zero_of_ψ_eval_zero
    (n : ℤ) {x y : K}
    (hP : W.Equation x y)
    (hψ : evalBivar (W.ψ n) x y = 0)
    (hφ : evalBivar (W.φ n) x y ≠ 0) :
    evalBivar (W.ω n) x y ≠ 0 := by
  -- Use ATOM 3/4 to know the representative satisfies the projective equation.
  -- Substitute `hψ`; the equation at Z=0 gives `ω^2 = φ^3` up to convention.
  -- Then `ω=0` would imply `φ^3=0`, contradiction.
  sorry

end

end WeierstrassCurve
```

This should be under 100 lines if the projective formula gives the equation membership cleanly.

---

## ATOM 6: local parameter over dual numbers

**Status:** easy/mechanical after ATOM 3/4 and ATOM 5.

In Jacobian coordinates, the local parameter at `O` is

```text
t = -x/y = - (X/Z²) / (Y/Z³) = -X*Z/Y.
```

For the projective representative

```text
[φₙ(Pε) : ωₙ(Pε) : ψₙ(Pε)]
```

and `ωₙ(P)` nonzero, `ωₙ(Pε)` is a unit in dual numbers, so

```text
t([n]Pε) = - φₙ(Pε) * ψₙ(Pε) / ωₙ(Pε).
```

At a `ψₙ(P)=0` root, first-order coefficient is

```text
- φₙ(P) / ωₙ(P) * coeffε(ψₙ(Pε)).
```

Suggested theorem shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Local parameter coefficient of `[n]Pε` at a `ψₙ`-root. -/
theorem localParam_nsmul_dual_coeff
    (n : ℤ) {x y : K}
    (hP : W.Equation x y)
    (hψ0 : evalBivar (W.ψ n) x y = 0)
    (hω : evalBivar (W.ω n) x y ≠ 0) :
    -- coeffε(t([n]Pε)) =
    --   - evalBivar (W.φ n) x y / evalBivar (W.ω n) x y
    --     * coeffε(evalBivarDual (W.ψ n) xε yε)
    True := by
  -- Dual-number algebra: expand `-φ*ψ/ω`, use `ψ(P)=0`, and invert `ω(Pε)`.
  sorry

end

end WeierstrassCurve
```

This is not conceptually hard.  It is mostly `TrivSqZeroExt` extensionality and first-order Taylor/field simplification.

---

## ATOM 7: coefficient of full `ψₙ(Pε)` vs derivative of reduced `preΨ'_n`

**Status:** moderate/mechanical; may already be partly in your repo.

This is a parity/unit-factor lemma.  At a non-2-torsion dual point, `ψ₂(Pε)` is a unit, so full `ψₙ` vanishes to first order exactly when the reduced univariate `preΨ'_n` does.  The coefficient relation is:

```text
odd n:
  coeffε(ψₙ(Pε)) = dx * (preΨ'_n)'(x)

even n:
  coeffε(ψₙ(Pε)) = ψ₂(P) * dx * (preΨ'_n)'(x)
```

up to the exact normalization through `Ψ`/`ψ` and the coordinate-ring congruence.

Suggested theorem shape:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- First-order coefficient of the full bivariate `ψₙ` at a non-2-torsion dual point,
expressed through the derivative of the reduced univariate `preΨ'_n`. -/
theorem coeffε_ψ_dual_eq_unit_mul_deriv_preΨ'
    (n : ℕ) {x y : K}
    (hP : W.Equation x y)
    (h2unit : IsUnit (/* ψ₂(Pε) */ (1 : TrivSqZeroExt K K))) :
    -- coeffε(ψₙ(Pε)) = unitFactor(n,P) * (derivative (W.preΨ' n)).eval x
    True := by
  -- Split on parity of n.
  -- Use `Affine.CoordinateRing.mk_ψ` / `Ψ` definition, or any existing repo lemma
  -- connecting full and reduced division polynomials on dual curve points.
  sorry

end

end WeierstrassCurve
```

This atom is smaller than ATOM 3/4 but not entirely trivial, because `ψ` and `Ψ` are equal only on the curve, via the coordinate-ring congruence.  If your repo already has `ψ₂`-unit and full/reduced evaluation lemmas, it may be short.

---

## ATOM 8: final assembly

**Status:** easy once ATOM 3/4, 5, 6, 7 and Seam C are available.

The final theorem should be the existing sorry seam:

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Nonzero derivative of the reduced division polynomial at a non-2-torsion root. -/
theorem preΨ'_deriv_ne_zero_at_nontorsion_root
    {n : ℕ} (hn : (n : K) ≠ 0)
    {x y : K}
    (hP : W.Equation x y)
    (hroot : (W.preΨ' n).eval x = 0)
    (h2 : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    (derivative (W.preΨ' n)).eval x ≠ 0 := by
  -- Assume derivative zero, build the dual deformation with `xε = x + ε` and `yε`
  -- from the existing y-lift theorem.
  -- ATOM 7 says coeffε ψₙ(Pε)=0.
  -- ATOM 6 says local parameter coeff of `[n]Pε` is zero.
  -- Existing `TangentO.nsmul₁_eq_natCast_mul` says it is `(n : K) * nonzero_scalar`.
  -- Contradiction with `hn` and non-2-torsion.
  sorry

end

end WeierstrassCurve
```

This is not hard; the hard work has been pushed into the bridge atoms.

---

## Answers to the explicit questions

### (a) Is the decomposition correct? Missing atoms?

Mostly yes, with these corrections:

* Replace ATOM 1 by `ψTwoMulQuot` via `complEDS₂`, then define `ω` from that quotient and scalar `2⁻¹` for the char-zero prototype.
* Merge ATOM 3/4 into the projective-formula atom.  Do not try to express it as a global affine coordinate-ring equality.
* Add ATOM 0 for bivariate/dual evaluation wrappers.
* Add an explicit “projective representative satisfies equation / equation at `Z=0`” sublemma for ATOM 5.
* Add explicit parity/full-vs-reduced lemma for ATOM 7.

### (b) Does Mathlib already connect `Point` group law to division-polynomial evaluations?

No.  Mathlib has `mk_ψ`, `mk_φ`, and `mk_Ψ_sq`, plus raw Jacobian coordinate formulas, but no `ωₙ` and no theorem of the form

```lean
n • Point.some x y h = ... φₙ ... ωₙ ... ψₙ ...
```

You must prove the projective formula from scratch, probably by induction using raw Jacobian formulas and the division polynomial recurrences.

### (c) Is `complEDS₂` cleaner than polynomial division?

Yes.  It is strictly cleaner and probably necessary for a robust Lean implementation.

Use:

```lean
ψTwoMulQuot n := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
```

and then the existing theorem gives:

```lean
W.ψ n * W.ψTwoMulQuot n = W.ψ (2*n)
```

This is exactly the quotient needed in the `ωₙ` formula, without requiring Euclidean division in `K[X][Y]`.

### (d) Which atoms are genuinely hard?

Genuinely hard / likely >100 lines:

```text
ATOM 3/4: projective division-polynomial formula [n]P=[φₙ:ωₙ:ψₙ]
ATOM 7: full ψ vs reduced preΨ' coefficient, if no repo lemma already exists
final arbitrary-characteristic ATOM 2: integral ωₙ / divisibility by 2
```

Moderate:

```text
ATOM 5: ωₙ(P)≠0 from φₙ(P)≠0 and equation at Z=0
ATOM 6: dual-number local parameter expansion
```

Easy/mechanical:

```text
ATOM 0: eval wrappers
ATOM 1: ψTwoMulQuot via complEDS₂
char-zero ATOM 2: normalization identity using `2⁻¹`
ATOM 8: assembly once bridge atoms exist
```

## Size estimate after atomization

For a characteristic-zero prototype:

```text
ATOM 0–2:    80–180 lines
ATOM 3/4:   300–700 lines
ATOM 5:      50–120 lines
ATOM 6:      80–180 lines
ATOM 7:     100–300 lines, less if repo already has full/reduced evaluation lemmas
ATOM 8:      50–120 lines
--------------------------------
Total:      700–1600 lines realistic
```

For final arbitrary characteristic, add the integral `ωₙ` construction/divisibility-by-2 work, likely another few hundred lines.

## Final recommendation

Start coding in this order:

```text
1. ψTwoMulQuot + ψ_mul_ψTwoMulQuot     -- quick win using complEDS₂
2. char-zero ω + normalization          -- validates normalization
3. local parameter algebra with abstract φ/ω/ψ values
4. full-vs-reduced ψ coefficient lemma
5. projective formula [φ:ω:ψ]           -- main hard theorem
6. ω≠0 and final assembly
```

This order front-loads the easy atoms and gives you executable interfaces before you enter the hard projective formula proof.
