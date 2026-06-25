# Q247 (dm4): coeffε of `ψₙ(Pε)` and the derivative of `preΨ'ₙ`

## Important structural point

The clean Lean proof should separate two layers.

1. **Pure dual-number algebra:** once you have rewritten the evaluated `ψₙ(Pε)` into the parity-normal form

   ```lean
   if Even n then ψ₂(Pε) * preΨ'ₙ(xε) else preΨ'ₙ(xε)
   ```

   and you know the base value `preΨ'ₙ(x) = 0`, the ε-coefficient calculation is a two-line `TrivSqZeroExt.snd_mul` computation.

2. **Elliptic-curve rewrite layer:** raw Mathlib `W.ψ n` is the bivariate EDS polynomial.  The parity-normalized object in Mathlib is documented as `W.Ψ n`, with `preΨ`/`preΨ'` controlling the odd/even formula.  For raw `W.ψ n`, use your local on-curve / coordinate-ring theorem, or `Affine.CoordinateRing.mk_ψ` plus evaluation on a dual-number point satisfying the curve equation, to obtain the parity rewrite used by the pure lemma.

The code below makes that parity rewrite an explicit hypothesis.  That is the right interface: it avoids hiding the coordinate-ring/on-curve proof inside the coefficient algebra.

Mathlib API facts used here:

* `TrivSqZeroExt K K`, projections `.fst` and `.snd`, and constructors `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`;
* `TrivSqZeroExt.snd_mul` for the product rule in the square-zero extension;
* Mathlib defines `WeierstrassCurve.ψ : ℤ → Polynomial (Polynomial R)` and `WeierstrassCurve.preΨ' : ℕ → Polynomial R`; the docs also distinguish the parity-normalized `WeierstrassCurve.Ψ` from raw `ψ`.

## Lean patch

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial

namespace DualPsiCoeff

variable {K : Type*} [Field K]

abbrev Dual (K : Type*) := TrivSqZeroExt K K

/-- The dual number `x + ε dx`. -/
def dualPoint (x dx : K) : Dual K :=
  TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx

/-- Evaluate a univariate polynomial at a dual number. -/
def evalXDual (p : K[X]) (xε : Dual K) : Dual K :=
  (p.map (TrivSqZeroExt.inlHom K K)).eval xε

/-- Evaluate a bivariate polynomial `K[X][Y]` at dual numbers `(xε,yε)`, using the
Mathlib convention that `Polynomial (Polynomial K)` is polynomial in `Y` with coefficients
in `K[X]`. -/
def evalXYDual (F : Polynomial (Polynomial K)) (xε yε : Dual K) : Dual K :=
  F.eval₂ (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom K K) xε) yε

/-- The ε-coefficient. -/
def coeffε (z : Dual K) : K := z.snd

/-- Constant-in-`Y` bivariate evaluation is just the univariate evaluation in `X`. -/
lemma evalXYDual_C (p : K[X]) (xε yε : Dual K) :
    evalXYDual (Polynomial.C p) xε yε = evalXDual p xε := by
  simp [evalXYDual, evalXDual]

/-- Adapter for your existing Taylor lemma for univariate polynomials over dual numbers.

This is the statement used below.  If your local theorem `eval_dualNumber` has exactly this
shape, delete this theorem and replace calls to `evalDual_eq_inl_add_inr_derivative` by
calls to `eval_dualNumber`.  If your theorem has the opposite multiplication order in the
ε-coefficient, `ring` will normalize it. -/
theorem evalDual_eq_inl_add_inr_derivative
    (p : K[X]) (x dx : K) :
    evalXDual p (dualPoint x dx)
      = TrivSqZeroExt.inl (p.eval x)
        + TrivSqZeroExt.inr (p.derivative.eval x * dx) := by
  -- In the project, this should be:
  --   simpa [evalXDual, dualPoint] using
  --     (eval_dualNumber (p := p) (x := x) (dx := dx))
  -- I leave the proof delegated to the already-existing `eval_dualNumber` API.
  simpa [evalXDual, dualPoint] using
    (eval_dualNumber (p := p) (x := x) (dx := dx))

lemma evalXDual_fst
    (p : K[X]) (x dx : K) :
    (evalXDual p (dualPoint x dx)).fst = p.eval x := by
  rw [evalDual_eq_inl_add_inr_derivative]
  simp

lemma evalXDual_snd
    (p : K[X]) (x dx : K) :
    (evalXDual p (dualPoint x dx)).snd = p.derivative.eval x * dx := by
  rw [evalDual_eq_inl_add_inr_derivative]
  simp

lemma evalXDual_snd_dx_one
    (p : K[X]) (x : K) :
    (evalXDual p (dualPoint x 1)).snd = p.derivative.eval x := by
  simpa using evalXDual_snd (p := p) (x := x) (dx := (1 : K))

/-- Odd case: after rewriting `ψₙ(Pε)` to the constant-in-`Y` univariate `preΨ'ₙ(xε)`,
the ε-coefficient is `(preΨ'ₙ)'(x)` when `dx = 1`. -/
theorem coeffε_ψ_odd_from_preΨ
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hψ_odd :
      evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy)
        = evalXDual (W.preΨ' n) (dualPoint x 1)) :
    coeffε (evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy))
      = (W.preΨ' n).derivative.eval x := by
  rw [coeffε, hψ_odd]
  exact evalXDual_snd_dx_one (p := W.preΨ' n) (x := x)

/-- Even case: after rewriting `ψₙ(Pε)` to `ψ₂(Pε) * preΨ'ₙ(xε)`, the hypothesis
`preΨ'ₙ(x)=0` kills the `dψ₂` term in the product rule. -/
theorem coeffε_ψ_even_from_preΨ
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hpre0 : (W.preΨ' n).eval x = 0)
    (hψ_even :
      evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy)
        = evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)
          * evalXDual (W.preΨ' n) (dualPoint x 1)) :
    coeffε (evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy))
      = (evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)).fst
          * (W.preΨ' n).derivative.eval x := by
  rw [coeffε, hψ_even]
  have hpre_fst :
      (evalXDual (W.preΨ' n) (dualPoint x 1)).fst = 0 := by
    simpa [hpre0] using evalXDual_fst (p := W.preΨ' n) (x := x) (dx := (1 : K))
  have hpre_snd :
      (evalXDual (W.preΨ' n) (dualPoint x 1)).snd
        = (W.preΨ' n).derivative.eval x :=
    evalXDual_snd_dx_one (p := W.preΨ' n) (x := x)
  simp [TrivSqZeroExt.snd_mul, hpre_fst, hpre_snd]
  ring

/-- Combined parity lemma.

The hypothesis `hψ_parity` is the exact place where you plug in your local theorem that
raw `W.ψ n`, evaluated at the dual point on the curve, agrees with the parity-normal form.
For odd `n`, the right side is `preΨ'ₙ(xε)`.  For even `n`, it is
`ψ₂(Pε) * preΨ'ₙ(xε)`.

The root hypothesis is the normalized root condition `preΨ'ₙ(x)=0`.  For even `n`, it is
obtained from `ψₙ(P)=0` and non-2-torsion, i.e. `ψ₂(P) ≠ 0`.  For odd `n`, it is just the
base value of the same normalized factor. -/
theorem coeffε_ψ_eq_if_even_ψ₂_mul_preΨ_derivative
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hpre0 : (W.preΨ' n).eval x = 0)
    (hψ_parity :
      evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy)
        = if Even n then
            evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)
              * evalXDual (W.preΨ' n) (dualPoint x 1)
          else
            evalXDual (W.preΨ' n) (dualPoint x 1)) :
    coeffε (evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy))
      = (if Even n then
            (evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)).fst
          else
            1)
          * (W.preΨ' n).derivative.eval x := by
  by_cases hn : Even n
  · have hψ_even :
      evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy)
        = evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)
          * evalXDual (W.preΨ' n) (dualPoint x 1) := by
        simpa [hn] using hψ_parity
    calc
      coeffε (evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy))
          = (evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)).fst
              * (W.preΨ' n).derivative.eval x :=
            coeffε_ψ_even_from_preΨ
              (W := W) (n := n) (x := x) (y := y) (sy := sy) hpre0 hψ_even
      _ = (if Even n then
              (evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)).fst
            else
              1)
            * (W.preΨ' n).derivative.eval x := by
            simp [hn]
  · have hψ_odd :
      evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy)
        = evalXDual (W.preΨ' n) (dualPoint x 1) := by
        simpa [hn] using hψ_parity
    calc
      coeffε (evalXYDual (W.ψ (n : ℤ)) (dualPoint x 1) (dualPoint y sy))
          = (W.preΨ' n).derivative.eval x :=
            coeffε_ψ_odd_from_preΨ
              (W := W) (n := n) (x := x) (y := y) (sy := sy) hψ_odd
      _ = (if Even n then
              (evalXYDual W.ψ₂ (dualPoint x 1) (dualPoint y sy)).fst
            else
              1)
            * (W.preΨ' n).derivative.eval x := by
            simp [hn]

end DualPsiCoeff
```

## How to supply `hψ_parity`

For the odd branch, the target rewrite should be:

```lean
have hψ_odd :
    DualPsiCoeff.evalXYDual (W.ψ (n : ℤ))
      (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)
      = DualPsiCoeff.evalXDual (W.preΨ' n) (DualPsiCoeff.dualPoint x 1) := by
  -- If you are working with `W.Ψ`, this is usually a parity simp lemma.
  -- If you are working with raw `W.ψ`, first use `Affine.CoordinateRing.mk_ψ`
  -- and evaluate on the dual point satisfying the Weierstrass equation.
  sorry
```

For the even branch:

```lean
have hψ_even :
    DualPsiCoeff.evalXYDual (W.ψ (n : ℤ))
      (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)
      = DualPsiCoeff.evalXYDual W.ψ₂
          (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)
        * DualPsiCoeff.evalXDual (W.preΨ' n) (DualPsiCoeff.dualPoint x 1) := by
  -- Same comment: use the normalized parity theorem, or bridge raw `ψ` to `Ψ`
  -- through the coordinate-ring/on-curve equality.
  sorry
```

Then assemble the `if Even n` hypothesis by cases:

```lean
have hψ_parity :
    DualPsiCoeff.evalXYDual (W.ψ (n : ℤ))
      (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)
      = if Even n then
          DualPsiCoeff.evalXYDual W.ψ₂
            (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)
            * DualPsiCoeff.evalXDual (W.preΨ' n) (DualPsiCoeff.dualPoint x 1)
        else
          DualPsiCoeff.evalXDual (W.preΨ' n) (DualPsiCoeff.dualPoint x 1) := by
  by_cases hn : Even n
  · simpa [hn] using hψ_even
  · simpa [hn] using hψ_odd
```

Finally:

```lean
have hcoeff :=
  DualPsiCoeff.coeffε_ψ_eq_if_even_ψ₂_mul_preΨ_derivative
    (W := W) (n := n) (x := x) (y := y) (sy := sy)
    hpre0 hψ_parity
```

This gives exactly

```lean
coeffε(ψₙ(Pε)) = (if Even n then ψ₂(P) else 1) * (preΨ'ₙ).derivative.eval x
```

where `ψ₂(P)` is represented in Lean as

```lean
(DualPsiCoeff.evalXYDual W.ψ₂
  (DualPsiCoeff.dualPoint x 1) (DualPsiCoeff.dualPoint y sy)).fst
```

If desired, you can rewrite that base projection to the ordinary affine formula

```lean
2 * y + W.a₁ * x + W.a₃
```

by `simp [DualPsiCoeff.evalXYDual, DualPsiCoeff.evalXDual, DualPsiCoeff.dualPoint,
WeierstrassCurve.ψ₂]`.
