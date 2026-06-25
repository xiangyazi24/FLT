# Q613 (dm4): `coeff X₀³ formalAddY = 1`

## Executive answer

Yes, this is the right raw-numerator coefficient to prove directly, before touching the normalized quotient.  The proof should unfold

```lean
formalAddY W = (W.map C).addY (formalPointMv W 0) (formalPointMv W 1)
```

and then unfold `Projective.addY` only one more step:

```lean
addY W' P Q = W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]
```

so that, using `negY_eq`, the target becomes

```lean
coeff e03 (formalAddY W)
  = - coeff e03 ((W.map C).negAddY P Q)
    - coeff e03 ((W.map C).a₁ * (W.map C).addX P Q)
    - coeff e03 ((W.map C).a₃ * (W.map C).addZ P Q)
```

The three needed raw facts are:

```lean
coeff e03 ((W.map C).negAddY P Q) = -1
coeff e03 ((W.map C).addX P Q) = 0
coeff e03 ((W.map C).addZ P Q) = 0
```

Then the final theorem is just `simp`/`ring`.

Important correction to the proposed reasoning: for `negAddY`, it is **not** true that all terms involving `w(X₀)` or `w(X₁)` disappear at degree `3`.  The term

```lean
P y * Q y ^ 2 * P z
```

becomes

```lean
(-1) * (-1)^2 * w(X₀) = -w(X₀),
```

and since `w(t) = t^3 + a₁ t^4 + ...`, this contributes `-1` to `coeff X₀³ negAddY`.  This is exactly the `-X₀³` term in

```text
negAddY degree 3 = -(X₀ - X₁)^3.
```

So the correct local bookkeeping is:

```text
negAddY degree 3
  =  3 X₀² X₁          -- from -3 * P.x^2 * Q.x * Q.y
     - 3 X₀ X₁²        -- from  3 * P.x * Q.x^2 * P.y
     + w(X₁)           -- from -P.y^2 * Q.y * Q.z
     - w(X₀)           -- from  P.y * Q.y^2 * P.z
  = -X₀³ + 3X₀²X₁ - 3X₀X₁² + X₁³.
```

For the **axis coefficient** `X₀³`, only the last line contributes `-1`.  The mixed monomials have an `X₁` factor, and `w(X₁)` has no `X₀³` coefficient.

---

## Recommended Lean shape

I would prove the theorem with three local coefficient lemmas.  The following is the shape I would put in the coefficient file.

Adjust the names `formalWMv`, `formalWMv_coeff_axis`, and `formalPointMv` to the exact names in `FormalGroupW.lean`; the algebraic structure is the important part.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic

noncomputable section

open MvPowerSeries Finsupp
open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

local notation "e₀" n => Finsupp.single (0 : Fin 2) n
local notation "e₁" n => Finsupp.single (1 : Fin 2) n

local notation "X₀" => (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R)
local notation "X₁" => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)

/-!
The only formal-`w` facts needed for the `X₀^3` coefficient.
You probably already have these as consequences of the recursion defining `w(t)`.
If not, prove them from:

  w(t) = t^3 + a₁ t^4 + ...

or from the coefficients:

  formalUCoeff W 0 = 0,
  formalUCoeff W 1 = 0,
  formalUCoeff W 2 = 0,
  formalUCoeff W 3 = 1.
-/

-- Suggested local simp-normal-form lemmas.  Replace `formalWMv W i` by the actual
-- Z-coordinate series used by `formalPointMv W i`.
--
-- @[simp] lemma coeff_e03_formalWMv_zero (W : WeierstrassCurve R) :
--     coeff (e₀ 3) (formalWMv W 0) = (1 : R) := ...
--
-- @[simp] lemma coeff_e03_formalWMv_one (W : WeierstrassCurve R) :
--     coeff (e₀ 3) (formalWMv W 1) = (0 : R) := ...
--
-- @[simp] lemma coeff_e00_formalWMv_zero (W : WeierstrassCurve R) :
--     coeff (e₀ 0) (formalWMv W 0) = (0 : R) := ...
--
-- @[simp] lemma coeff_e01_formalWMv_zero (W : WeierstrassCurve R) :
--     coeff (e₀ 1) (formalWMv W 0) = (0 : R) := ...
--
-- @[simp] lemma coeff_e02_formalWMv_zero (W : WeierstrassCurve R) :
--     coeff (e₀ 2) (formalWMv W 0) = (0 : R) := ...
```

The reason I would keep these as separate lemmas is that they isolate the only use of the `w` recursion.  Everything else is just polynomial coefficient arithmetic in `MvPowerSeries (Fin 2) R`.

---

## Core coefficient lemmas

Use the following three statements.  They are intentionally axis-only; this avoids proving the full homogeneous degree-3 polynomial.

```lean
private lemma coeff_e03_negAddY_formalPoint
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 3)
      ((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).negAddY
        (formalPointMv W 0) (formalPointMv W 1))
      = (-1 : R) := by
  classical
  -- After unfolding the projective formula and the two formal points, the degree-3
  -- axis terms are exactly:
  --   3*X₀^2*X₁ - 3*X₀*X₁^2 + w₁ - w₀.
  -- At `e₀ 3`, the two mixed terms and `w₁` vanish, while `w₀` contributes `1`.
  simp [WeierstrassCurve.Projective.negAddY,
    formalPointMv,
    pow_succ,
    MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_X,
    MvPowerSeries.coeff_X_pow,
    MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_mul_C]

private lemma coeff_e03_addX_formalPoint
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 3)
      ((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).addX
        (formalPointMv W 0) (formalPointMv W 1))
      = (0 : R) := by
  classical
  -- Every term in `addX` either has an `X₁` factor, or has a `w` factor multiplied
  -- by at least one positive-degree variable, or has at least two `w` factors.
  -- Since `w` starts in degree 3, no term can contribute to the pure `X₀^3` axis.
  simp [WeierstrassCurve.Projective.addX,
    formalPointMv,
    pow_succ,
    MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_X,
    MvPowerSeries.coeff_X_pow,
    MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_mul_C]

private lemma coeff_e03_addZ_formalPoint
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (e₀ 3)
      ((W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).addZ
        (formalPointMv W 0) (formalPointMv W 1))
      = (0 : R) := by
  classical
  -- `addZ` has no standalone `w₀` term.  Its terms are mixed in `X₁`, quadratic
  -- in `w`, or have an additional positive-degree factor.  Hence the pure `X₀^3`
  -- coefficient is zero.
  simp [WeierstrassCurve.Projective.addZ,
    formalPointMv,
    pow_succ,
    MvPowerSeries.coeff_C,
    MvPowerSeries.coeff_X,
    MvPowerSeries.coeff_X_pow,
    MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_mul_C]
```

Those `simp` proofs rely on the `formalWMv` coefficient lemmas being tagged `[simp]`.  If `simp` does not close the product terms containing `w`, add the following axis-product simp lemmas once:

```lean
private lemma coeff_e03_X₀_mul_of_coeff_e02_zero
    {f : MvPowerSeries (Fin 2) R}
    (hf : MvPowerSeries.coeff (e₀ 2) f = 0) :
    MvPowerSeries.coeff (e₀ 3) (X₀ * f) = 0 := by
  classical
  simpa [X₀, Finsupp.single_add, hf] using
    (MvPowerSeries.coeff_add_monomial_mul
      (m := e₀ 1) (n := e₀ 2) (φ := f) (a := (1 : R)))

private lemma coeff_e03_X₀_sq_mul_of_coeff_e01_zero
    {f : MvPowerSeries (Fin 2) R}
    (hf : MvPowerSeries.coeff (e₀ 1) f = 0) :
    MvPowerSeries.coeff (e₀ 3) (X₀ ^ 2 * f) = 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq]
  simpa [Finsupp.single_add, hf] using
    (MvPowerSeries.coeff_add_monomial_mul
      (m := e₀ 2) (n := e₀ 1) (φ := f) (a := (1 : R)))

private lemma coeff_e03_X₁_mul
    (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (e₀ 3) (X₁ * f) = 0 := by
  classical
  rw [X₁, MvPowerSeries.coeff_monomial_mul]
  simp [Finsupp.single_eq_single_iff]
```

The third lemma is very useful: any term with an explicit factor `X₁` dies immediately for the pure `X₀`-axis coefficient.

---

## Final theorem

Once the three raw coefficient lemmas are available, the target proof is short.

```lean
lemma formalAddY_coeff_X0_cube
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3) (formalAddY W) = (1 : R) := by
  classical
  let Cmv : R →+* MvPowerSeries (Fin 2) R := MvPowerSeries.C
  let Wmv := W.map Cmv
  let P : Fin 3 → MvPowerSeries (Fin 2) R := formalPointMv W 0
  let Q : Fin 3 → MvPowerSeries (Fin 2) R := formalPointMv W 1

  have hneg :
      MvPowerSeries.coeff (e₀ 3) (Wmv.negAddY P Q) = (-1 : R) := by
    simpa [Wmv, P, Q, Cmv] using coeff_e03_negAddY_formalPoint (W := W)

  have hX :
      MvPowerSeries.coeff (e₀ 3) (Wmv.addX P Q) = (0 : R) := by
    simpa [Wmv, P, Q, Cmv] using coeff_e03_addX_formalPoint (W := W)

  have hZ :
      MvPowerSeries.coeff (e₀ 3) (Wmv.addZ P Q) = (0 : R) := by
    simpa [Wmv, P, Q, Cmv] using coeff_e03_addZ_formalPoint (W := W)

  calc
    MvPowerSeries.coeff (e₀ 3) (formalAddY W)
        = MvPowerSeries.coeff (e₀ 3)
            (Wmv.negY ![Wmv.addX P Q, Wmv.negAddY P Q, Wmv.addZ P Q]) := by
              simp [formalAddY, Wmv, P, Q, Cmv]
    _ = MvPowerSeries.coeff (e₀ 3)
            (-Wmv.negAddY P Q - Wmv.a₁ * Wmv.addX P Q - Wmv.a₃ * Wmv.addZ P Q) := by
              rw [WeierstrassCurve.Projective.negY_eq]
    _ = 1 := by
              simp [hneg, hX, hZ, Wmv, Cmv]
```

If the last `simp` leaves scalar-multiplication residue, use this more explicit ending:

```lean
    _ = -(-1 : R) - Wmv.a₁ * 0 - Wmv.a₃ * 0 := by
              simp [hneg, hX, hZ]
    _ = 1 := by ring
```

---

## If `simp` does not see the map coefficients

Sometimes the coefficient ring of `Wmv := W.map Cmv` leaves `Wmv.a₁` as a power series constant rather than exposing it as `C W.a₁`.  Then add this local simp lemma:

```lean
private lemma map_C_a₁
    (W : WeierstrassCurve R) :
    (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).a₁
      = MvPowerSeries.C W.a₁ := by
  rfl

private lemma map_C_a₃
    (W : WeierstrassCurve R) :
    (W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)).a₃
      = MvPowerSeries.C W.a₃ := by
  rfl
```

Then the final coefficient terms reduce by the existing Mathlib simp lemmas:

```lean
MvPowerSeries.coeff_C_mul
MvPowerSeries.coeff_mul_C
```

So `coeff e03 (C W.a₁ * addX) = W.a₁ * coeff e03 addX = 0`, and similarly for the `a₃ * addZ` term.

---

## Minimal checklist

To make the final theorem build, I would add exactly these facts first:

```lean
-- Z-coordinate of the first formal point starts with X₀³.
@[simp] lemma coeff_e03_formalPointMv_0_z
    (W : WeierstrassCurve R) :
    coeff (e₀ 3) ((formalPointMv W 0) 2) = (1 : R) := ...

-- Z-coordinate of the second formal point has no pure X₀³ term.
@[simp] lemma coeff_e03_formalPointMv_1_z
    (W : WeierstrassCurve R) :
    coeff (e₀ 3) ((formalPointMv W 1) 2) = (0 : R) := ...

-- Lower pure-axis coefficients of w(X₀) vanish.
@[simp] lemma coeff_e00_formalPointMv_0_z
    (W : WeierstrassCurve R) :
    coeff (e₀ 0) ((formalPointMv W 0) 2) = (0 : R) := ...

@[simp] lemma coeff_e01_formalPointMv_0_z
    (W : WeierstrassCurve R) :
    coeff (e₀ 1) ((formalPointMv W 0) 2) = (0 : R) := ...

@[simp] lemma coeff_e02_formalPointMv_0_z
    (W : WeierstrassCurve R) :
    coeff (e₀ 2) ((formalPointMv W 0) 2) = (0 : R) := ...
```

Those five formal-point coefficient facts plus the three raw projective-formula facts above give the desired theorem cleanly.

The key point is that the proof should **use** `coeff e03 w(X₀) = 1`; trying to discard all `w` terms will give the wrong sign for `negAddY` and will make the Lean proof fight the actual formula.
