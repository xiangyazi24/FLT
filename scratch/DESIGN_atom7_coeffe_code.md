# Q320 (dm4): `scratch/Atom7CoeffEpsilon.lean`

Below is the complete proposed file for ATOM 7.  It isolates the fragile/local part into one adapter theorem:

```lean
simpa [evalUnivar_dual, dualNumber] using (eval_dualNumber f x dx)
```

If your `scratch/SeamE1_Dual.lean` exports `eval_dualNumber` inside a namespace, qualify that single call.  The rest of the file is closed dual-number algebra.  The combined `ψₙ` lemma takes the parity/coordinate-ring rewrite for raw `W.ψ n` as a hypothesis, because that rewrite is the separate bridge from Mathlib’s raw bivariate `ψ` to the normalized `preΨ'` factor.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Tactic
import scratch.SeamE1_Dual

noncomputable section

open Polynomial
open scoped Polynomial

namespace Atom7CoeffEpsilon

variable {K : Type*} [Field K]

/-- Dual numbers over `K`, implemented as the trivial square-zero extension `K ⊕ Kε`. -/
abbrev Dual (K : Type*) := TrivSqZeroExt K K

/-- `x + ε dx`. -/
def dualNumber (x dx : K) : Dual K :=
  TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx

/-- ε-coefficient of a dual number. -/
def coeffε (z : Dual K) : K :=
  z.snd

/-- Univariate polynomial evaluation at a dual number. -/
def evalUnivar_dual (f : K[X]) (xε : Dual K) : Dual K :=
  Polynomial.eval₂ (TrivSqZeroExt.inlHom K K) xε f

/-- Bivariate polynomial evaluation at a dual point `(xε,yε)`.  Mathlib represents
`K[X,Y]` as `Polynomial (Polynomial K)`, i.e. outer variable `Y`, coefficients in `K[X]`. -/
def evalBivar_dual (F : Polynomial (Polynomial K)) (xε yε : Dual K) : Dual K :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom K K) xε) yε F

/-- Adapter to the Taylor lemma from `scratch/SeamE1_Dual.lean`.

Expected local shape of `eval_dualNumber`:

```lean
eval_dualNumber f x dx :
  evalUnivar_dual f (dualNumber x dx)
    = inl (f.eval x) + inr (f.derivative.eval x * dx)
```

If your theorem is namespaced, change only the final line of this proof. -/
theorem evalUnivar_dual_eq_taylor
    (f : K[X]) (x dx : K) :
    evalUnivar_dual f (dualNumber x dx)
      = TrivSqZeroExt.inl (f.eval x)
        + TrivSqZeroExt.inr (f.derivative.eval x * dx) := by
  simpa [evalUnivar_dual, dualNumber] using (eval_dualNumber f x dx)

lemma evalUnivar_dual_fst_eq_eval
    (f : K[X]) (x dx : K) :
    (evalUnivar_dual f (dualNumber x dx)).fst = f.eval x := by
  rw [evalUnivar_dual_eq_taylor]
  simp

lemma evalUnivar_dual_snd_eq_derivative_mul
    (f : K[X]) (x dx : K) :
    (evalUnivar_dual f (dualNumber x dx)).snd = f.derivative.eval x * dx := by
  rw [evalUnivar_dual_eq_taylor]
  simp

lemma evalUnivar_dual_snd_eq_derivative_dx_one
    (f : K[X]) (x : K) :
    (evalUnivar_dual f (dualNumber x 1)).snd = f.derivative.eval x := by
  simpa using evalUnivar_dual_snd_eq_derivative_mul (f := f) (x := x) (dx := (1 : K))

/-- Bivariate evaluation of a polynomial constant in `Y` reduces to univariate evaluation
in `X`. -/
lemma evalBivar_dual_C
    (f : K[X]) (xε yε : Dual K) :
    evalBivar_dual (Polynomial.C f) xε yε = evalUnivar_dual f xε := by
  simp [evalBivar_dual, evalUnivar_dual]

/-- Requested odd-branch API lemma: `C f` is constant in `Y`, so its ε-coefficient is
just the ε-coefficient of the univariate evaluation of `f`. -/
lemma snd_evalBivar_dual_C
    (f : K[X]) (xε yε : Dual K) :
    (evalBivar_dual (Polynomial.C f) xε yε).snd = (evalUnivar_dual f xε).snd := by
  rw [evalBivar_dual_C]

/-- Odd branch with `dx = 1`: evaluating `C f` at `(x + ε, y + ε sy)` has
ε-coefficient `f'(x)`. -/
lemma snd_evalBivar_dual_C_dualNumber_dx_one
    (f : K[X]) (x y sy : K) :
    (evalBivar_dual (Polynomial.C f) (dualNumber x 1) (dualNumber y sy)).snd
      = f.derivative.eval x := by
  rw [snd_evalBivar_dual_C]
  exact evalUnivar_dual_snd_eq_derivative_dx_one (f := f) (x := x)

/-- Square-zero product rule in the special form used for the even branch: if the right
factor has zero base part, then only `A.fst * B.snd` contributes to the ε-coefficient. -/
lemma snd_mul_of_right_fst_eq_zero
    (A B : Dual K) (hB : B.fst = 0) :
    (A * B).snd = A.fst * B.snd := by
  rcases A with ⟨a0, a1⟩
  rcases B with ⟨b0, b1⟩
  simp at hB ⊢
  subst b0
  simp

/-- Even-branch algebra.  If `preΨ'ₙ(x)=0`, then the `dψ₂` term in the product rule for
`ψ₂(Pε) * preΨ'ₙ(xε)` vanishes. -/
lemma snd_ψ₂_mul_C_preΨ_of_preΨ_eval_eq_zero
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hroot : (W.preΨ' n).eval x = 0) :
    (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
        * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd
      = (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
          * (W.preΨ' n).derivative.eval x := by
  have hpre_fst :
      (evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).fst = 0 := by
    rw [evalBivar_dual_C]
    simpa [hroot] using
      evalUnivar_dual_fst_eq_eval (f := W.preΨ' n) (x := x) (dx := (1 : K))
  have hpre_snd :
      (evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd
        = (W.preΨ' n).derivative.eval x := by
    rw [snd_evalBivar_dual_C]
    exact evalUnivar_dual_snd_eq_derivative_dx_one (f := W.preΨ' n) (x := x)
  calc
    (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
        * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd
        = (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
            * (evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd := by
            exact snd_mul_of_right_fst_eq_zero
              (A := evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy))
              (B := evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy))
              hpre_fst
    _ = (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
          * (W.preΨ' n).derivative.eval x := by
          rw [hpre_snd]

/-- Combined ATOM 7 coefficient bridge.

`hψ_parity` is the separate coordinate-ring/parity rewrite for raw `W.ψ n` evaluated on the
dual curve point:

* odd `n`: `ψₙ(Pε) = C(preΨ'ₙ)(Pε)`;
* even `n`: `ψₙ(Pε) = ψ₂(Pε) * C(preΨ'ₙ)(Pε)`.

Given this rewrite and the root condition `preΨ'ₙ(x)=0`, the ε-coefficient is

```lean
(if Even n then ψ₂(P) else 1) * (preΨ'ₙ)'(x)
```

where `ψ₂(P)` is represented as the base projection of `ψ₂(Pε)`. -/
theorem coeffε_ψ_eq_if_even_ψ₂_mul_preΨ_derivative
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hroot : (W.preΨ' n).eval x = 0)
    (hψ_parity :
      evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy)
        = if Even n then
            evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
              * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)
          else
            evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)) :
    coeffε (evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy))
      = (if Even n then
            (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
          else
            1)
          * (W.preΨ' n).derivative.eval x := by
  by_cases hn : Even n
  · have hψ_even :
      evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy)
        = evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
            * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy) := by
      simpa [hn] using hψ_parity
    calc
      coeffε (evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy))
          = (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
              * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd := by
              simp [coeffε, hψ_even]
      _ = (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
            * (W.preΨ' n).derivative.eval x := by
            exact snd_ψ₂_mul_C_preΨ_of_preΨ_eval_eq_zero
              (W := W) (n := n) (x := x) (y := y) (sy := sy) hroot
      _ = (if Even n then
              (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
            else
              1)
            * (W.preΨ' n).derivative.eval x := by
            simp [hn]
  · have hψ_odd :
      evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy)
        = evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy) := by
      simpa [hn] using hψ_parity
    calc
      coeffε (evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy))
          = (evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)).snd := by
              simp [coeffε, hψ_odd]
      _ = (W.preΨ' n).derivative.eval x := by
            exact snd_evalBivar_dual_C_dualNumber_dx_one
              (f := W.preΨ' n) (x := x) (y := y) (sy := sy)
      _ = (if Even n then
              (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
            else
              1)
            * (W.preΨ' n).derivative.eval x := by
            simp [hn]

/-- Optional rewrite of the base projection of `ψ₂(Pε)` to the usual affine expression.
This is useful if the target statement uses `ψ₂(P) = 2*y + a₁*x + a₃`. -/
lemma evalBivar_dual_ψ₂_fst
    (W : WeierstrassCurve K) (x y sy : K) :
    (evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)).fst
      = 2 * y + W.a₁ * x + W.a₃ := by
  simp [evalBivar_dual, evalUnivar_dual, dualNumber, WeierstrassCurve.ψ₂]
  ring

/-- Same combined bridge with the `ψ₂(P)` factor rewritten to `2*y + a₁*x + a₃`. -/
theorem coeffε_ψ_eq_if_even_affine_ψ₂_mul_preΨ_derivative
    (W : WeierstrassCurve K) (n : ℕ) (x y sy : K)
    (hroot : (W.preΨ' n).eval x = 0)
    (hψ_parity :
      evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy)
        = if Even n then
            evalBivar_dual W.ψ₂ (dualNumber x 1) (dualNumber y sy)
              * evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)
          else
            evalBivar_dual (Polynomial.C (W.preΨ' n)) (dualNumber x 1) (dualNumber y sy)) :
    coeffε (evalBivar_dual (W.ψ (n : ℤ)) (dualNumber x 1) (dualNumber y sy))
      = (if Even n then 2 * y + W.a₁ * x + W.a₃ else 1)
          * (W.preΨ' n).derivative.eval x := by
  have h := coeffε_ψ_eq_if_even_ψ₂_mul_preΨ_derivative
    (W := W) (n := n) (x := x) (y := y) (sy := sy) hroot hψ_parity
  by_cases hn : Even n
  · simpa [hn, evalBivar_dual_ψ₂_fst (W := W) (x := x) (y := y) (sy := sy)] using h
  · simpa [hn] using h

end Atom7CoeffEpsilon
```

## How to supply `hψ_parity`

The file above deliberately does not prove the raw-`ψ` coordinate-ring rewrite.  In the local Atom 7 integration, prove or import a theorem of the following form:

```lean
have hψ_parity :
    Atom7CoeffEpsilon.evalBivar_dual (W.ψ (n : ℤ))
      (Atom7CoeffEpsilon.dualNumber x 1) (Atom7CoeffEpsilon.dualNumber y sy)
      = if Even n then
          Atom7CoeffEpsilon.evalBivar_dual W.ψ₂
            (Atom7CoeffEpsilon.dualNumber x 1) (Atom7CoeffEpsilon.dualNumber y sy)
            * Atom7CoeffEpsilon.evalBivar_dual (Polynomial.C (W.preΨ' n))
              (Atom7CoeffEpsilon.dualNumber x 1) (Atom7CoeffEpsilon.dualNumber y sy)
        else
          Atom7CoeffEpsilon.evalBivar_dual (Polynomial.C (W.preΨ' n))
            (Atom7CoeffEpsilon.dualNumber x 1) (Atom7CoeffEpsilon.dualNumber y sy) := by
  -- Odd branch: `ψₙ = C(preΨ'ₙ)` on the dual curve point.
  -- Even branch: `ψₙ = ψ₂ * C(preΨ'ₙ)` on the dual curve point.
  -- Use `Affine.CoordinateRing.mk_ψ` / the local on-curve evaluation bridge here.
  sorry
```

Then the combined result is:

```lean
have hcoeff :=
  Atom7CoeffEpsilon.coeffε_ψ_eq_if_even_affine_ψ₂_mul_preΨ_derivative
    (W := W) (n := n) (x := x) (y := y) (sy := sy)
    hroot hψ_parity
```

This gives exactly:

```lean
coeffε(ψₙ(Pε)) = (if Even n then 2*y + W.a₁*x + W.a₃ else 1)
  * (W.preΨ' n).derivative.eval x
```

with `dx = 1`.  For a general deformation `x + ε dx`, replace every `dualNumber x 1` above by `dualNumber x dx`; the derivative term becomes `(W.preΨ' n).derivative.eval x * dx`.
