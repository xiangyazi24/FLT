# Q300 (dm3): ATOMS 5–8 assembly chain and bridge-2 assessment

## Executive verdict

ATOMS 5–7 have a clean Lean chain once the projective X/Y/Z coordinate identities
are available.  They prove the expected formula

```text
coeffε t_O([n]Pε)
  = - φ_n(P) / ω_n(P) · parityUnit(P) · (preΨ'_n)'(x)
```

at a non-2-torsion root of `preΨ'_n`.

But ATOM 8 still needs one extra conceptual bridge:

```text
coeffε t_O([n]Pε) = (n : K) · coeffε t_P(Pε)
```

or equivalently the `TangentO.nsmul₁` / formal differential identification.  The
projective formula alone tells you the output projective coordinates and hence the
local parameter coefficient; it does **not** by itself say that the differential
of `[n]` is multiplication by `n` on tangent vectors.  That is exactly the missing
bridge.

So there are two viable closures:

1. **Tangent closure:** use ATOMS 5–7 plus `TangentO.nsmul₁` / formal-group
   coefficient `formalNsmul_coeff_one` to contradict `(n : K) ≠ 0`.
2. **Bezout closure:** skip ATOMS 5–8 for separability and use
   `IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))` directly.  This is exactly
   what the per-`n` resultant certificates prove.

There is no third free closure “from the projective formula alone”: deriving
`IsCoprime(preΨ'_n, (preΨ'_n)')` from the projective formula requires proving that
`[n]` is unramified at nonzero `n`-torsion, and that is the same tangent/differential
statement in different language.

---

## Imports

The atom file wants only the dual-number API, division polynomials, Jacobian
coordinates, and tactics.  Adjust project-local imports to your actual filenames.

```lean
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

-- Project-local imports, adjust names:
-- import FLT.Scratch.KeystoneProjectiveFormula
-- import FLT.Scratch.KeystoneCoprimality
-- import FLT.Scratch.KeystoneTangentO
```

The `TrivSqZeroExt` field projections below are written as `dualFst` and
`dualSnd`.  If your Mathlib exposes them as `.fst`/`.snd`, these abbreviations are
just wrappers; if it exposes the underlying product fields differently, only these
wrappers need changing.

```lean
namespace WeierstrassCurve

open Polynomial

variable {K : Type*} [Field K]

abbrev Dual (K : Type*) [CommRing K] : Type _ := TrivSqZeroExt K K

-- Replace the RHS by the exact field names in your local Mathlib if needed.
noncomputable abbrev dualFst (z : Dual K) : K := z.fst
noncomputable abbrev dualSnd (z : Dual K) : K := z.snd

/-- Bivariate evaluation convention for `K[X][Y]`: first outer `Y`, then inner `X`. -/
noncomputable def evalBivar (p : Polynomial (Polynomial K)) (x y : K) : K :=
  (p.eval y).eval x

/-- Bivariate evaluation into dual numbers. -/
noncomputable def evalBivarDual
    (p : Polynomial (Polynomial K)) (xε yε : Dual K) : Dual K :=
  Polynomial.eval₂ (Polynomial.eval₂ (algebraMap K (Dual K)) xε) yε p
```

---

## ATOM 5: `ω_n(P) ≠ 0` at `ψ_n(P)=0`, non-2-torsion stratum

Mathematics:

* projective formula and `ψ_n(P)=0` put `[n]P` at `Z=0`;
* the Jacobian equation at `Z=0` is `Y² = X³`;
* if `X = φ_n(P) ≠ 0`, then `Y = ω_n(P) ≠ 0`.

The only curve equation fact needed is the tiny “at infinity” lemma below.

```lean
namespace Atom5

variable (W : WeierstrassCurve K)

/-- At `Z = 0`, the Jacobian equation is `Y² = X³`; hence nonzero `X` forces nonzero `Y`. -/
theorem omega_ne_of_phi_ne_at_infinity
    {φ ω : K}
    (hEq : W.toJacobian.Equation ![φ, ω, 0])
    (hφ : φ ≠ 0) :
    ω ≠ 0 := by
  intro hω
  apply hφ
  have hφ3 : φ ^ 3 = 0 := by
    -- Unfolding the Jacobian equation at `Z = 0` gives `ω^2 - φ^3 = 0`.
    -- The exact simp theorem may be `Jacobian.equation_iff` in your file.
    have hEq' : ω ^ 2 = φ ^ 3 := by
      simpa [WeierstrassCurve.Jacobian.Equation,
        WeierstrassCurve.Jacobian.polynomial,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        hω] using hEq
    simpa [hω] using hEq'.symm
  exact pow_eq_zero hφ3

/-- ATOM 5 packaged for the actual division-polynomial representative. -/
theorem omega_eval_ne_of_phi_eval_ne
    (W : WeierstrassCurve K) (n : ℤ) (x y : K)
    (φn ωn : K)
    (hEqInf : W.toJacobian.Equation ![φn, ωn, 0])
    (hφn : φn ≠ 0) :
    ωn ≠ 0 := by
  exact omega_ne_of_phi_ne_at_infinity (W := W) hEqInf hφn

end Atom5
```

In the real file, `hEqInf` comes from the projective formula plus evaluation at a
point satisfying the curve equation and `ψ_n(P)=0`.  The input `hφn` is the
already-planned consequence of `no_adjacent_preΨ_zero` and the definition of
`φ_n`.

---

## ATOM 6: local parameter coefficient at infinity

Use the weighted-Jacobian local parameter at infinity

```text
t_O([X:Y:Z]) = - X*Z / Y.
```

If `Z.fst = 0` and `Y.fst ≠ 0`, then in dual numbers

```text
snd(-X*Z/Y) = -(fst X / fst Y) * snd Z.
```

The `snd X` and `snd Y` terms vanish from the coefficient because `fst Z = 0`.

```lean
namespace Atom6

/-- Dual-number coefficient of the local parameter `-X*Z/Y` at infinity. -/
theorem dual_snd_neg_mul_div_at_infinity
    {X Y Z : Dual K}
    (hZ0 : dualFst Z = 0)
    (hY0 : dualFst Y ≠ 0) :
    dualSnd (-(X * Z) / Y) = - (dualFst X / dualFst Y) * dualSnd Z := by
  -- This is pure `TrivSqZeroExt` arithmetic.
  -- Recommended proof after fixing projection names:
  --   ext <;> simp [dualFst, dualSnd, hZ0]
  --   field_simp [hY0]
  --   ring
  -- or use local lemmas for `fst_mul`, `snd_mul`, `fst_inv`, `snd_inv`.
  sorry

/-- ATOM 6 in the notation of the projective formula. -/
theorem coeff_t_of_projective_formula_at_root
    {Xε Yε Zε : Dual K}
    (hZ0 : dualFst Zε = 0)
    (hY0 : dualFst Yε ≠ 0) :
    dualSnd (-(Xε * Zε) / Yε)
      = - (dualFst Xε / dualFst Yε) * dualSnd Zε := by
  exact dual_snd_neg_mul_div_at_infinity (X := Xε) (Y := Yε) (Z := Zε) hZ0 hY0

end Atom6
```

For the application:

```text
Xε = φ_n(Pε),
Yε = ω_n(Pε),
Zε = ψ_n(Pε).
```

ATOM 5 supplies `dualFst Yε ≠ 0`.  The hypothesis `ψ_n(P)=0` supplies
`dualFst Zε = 0`.  Therefore

```text
coeffε t_O([n]Pε)
  = -φ_n(P)/ω_n(P) · coeffε(ψ_n(Pε)).
```

---

## ATOM 7: coefficient of `ψ_n(Pε)` is parity unit times `(preΨ'_n)'(x)`

The precise statement should include the tangent lift assumptions for `Pε`:

* `fst Xε = x`;
* `snd Xε = 1` if the infinitesimal is `x + ε`;
* `fst Yε = y`;
* `Pε` satisfies the curve equation over `Dual K`;
* `preΨ'_n(x)=0`.

For even `n`, the bivariate division polynomial is

```text
ψ_n = C(preΨ'_n) * ψ₂.
```

The derivative of the second factor drops out at a root of `preΨ'_n`.  For odd
`n`, the factor is `1`.

```lean
namespace Atom7

variable (W : WeierstrassCurve K)

/-- Parity factor relating bivariate `ψ_n` and reduced univariate `preΨ'_n`. -/
noncomputable def psiParityFactor (W : WeierstrassCurve K) (n : ℕ) (x y : K) : K :=
  if Even n then evalBivar W.ψ₂ x y else 1

/--
Dual evaluation of a univariate polynomial at `x + ε`.

This is the standard Taylor formula modulo `ε²`.
-/
theorem dual_snd_eval_univariate_of_snd_eq_one
    (f : Polynomial K) {xε : Dual K} {x : K}
    (hx0 : dualFst xε = x) (hx1 : dualSnd xε = 1) :
    dualSnd (Polynomial.eval₂ (algebraMap K (Dual K)) xε f)
      = (Polynomial.derivative f).eval x := by
  -- Prove by induction on `f`, or use an existing project lemma `eval_dualNumber`.
  -- The general version is
  --   snd(f(x + ε·u)) = u * f'(x).
  sorry

/--
ATOM 7: coefficient of `ψ_n(Pε)` at a root is the parity factor times
`(preΨ'_n)'(x)`.

The bridge `hψ_eq_Ψ_dual` is the evaluated form of `mk_ψ`: because `Pε` lies on
`W`, bivariate `ψ_n` and the packaged `Ψ_n` have the same dual evaluation.
-/
theorem snd_psi_eval_dual_eq_parity_mul_derivative
    (W : WeierstrassCurve K) (n : ℕ)
    {x y : K} {xε yε : Dual K}
    (hx0 : dualFst xε = x) (hx1 : dualSnd xε = 1)
    (hy0 : dualFst yε = y)
    (hroot : (W.preΨ' n).eval x = 0)
    (hψ_eq_Ψ_dual :
      evalBivarDual (W.ψ n) xε yε
        = evalBivarDual (W.Ψ n) xε yε) :
    dualSnd (evalBivarDual (W.ψ n) xε yε)
      = psiParityFactor W n x y * (Polynomial.derivative (W.preΨ' n)).eval x := by
  rw [hψ_eq_Ψ_dual]
  by_cases hn : Even n
  · -- even case: `Ψ n = C(preΨ' n) * ψ₂`
    simp [WeierstrassCurve.Ψ_ofNat, hn, psiParityFactor, hroot,
      dual_snd_eval_univariate_of_snd_eq_one (f := W.preΨ' n) hx0 hx1,
      hx0, hy0]
    ring
  · -- odd case: `Ψ n = C(preΨ' n)`
    simp [WeierstrassCurve.Ψ_ofNat, hn, psiParityFactor,
      dual_snd_eval_univariate_of_snd_eq_one (f := W.preΨ' n) hx0 hx1,
      hx0, hy0]

end Atom7
```

The only nontrivial bridge in ATOM 7 is `hψ_eq_Ψ_dual`.  It is exactly the
“evaluation through the coordinate ring” version of Mathlib’s
`Affine.CoordinateRing.mk_ψ`.  Since `Pε` satisfies the curve equation in
`Dual K`, the evaluation hom kills `F_W`, so equality in the coordinate ring
implies equality after dual evaluation.

---

## ATOM 8A: tangent closure, if you keep the differential route

Combining ATOMS 6 and 7 gives:

```text
coeffε t_O([n]Pε)
  = -φ_n(P)/ω_n(P) · parityUnit(P) · (preΨ'_n)'(x).
```

If `(preΨ'_n)'(x)=0`, then the output tangent coefficient is zero.  To get a
contradiction you still need:

```text
coeffε t_O([n]Pε) = (n : K) · coeffε t_P(Pε).
```

This is the missing `TangentO` identification lemma.

```lean
namespace Atom8Tangent

/-- Product of nonzero units in the coefficient formula. -/
theorem atom6_atom7_unit_factor_ne_zero
    {φ ω parity : K}
    (hφ : φ ≠ 0) (hω : ω ≠ 0) (hparity : parity ≠ 0) :
    -φ / ω * parity ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hφ hω)) hparity

/-- Schematic final tangent contradiction. -/
theorem bridge2_contradiction_from_tangent
    {n : ℕ} (hn : (n : K) ≠ 0)
    {inputCoeff outputCoeff : K}
    (hinput : inputCoeff = 1)
    (hTangent : outputCoeff = (n : K) * inputCoeff)
    (hOutputZero : outputCoeff = 0) :
    False := by
  have hnzero : (n : K) * inputCoeff ≠ 0 := by
    rw [hinput]
    simpa using hn
  exact hnzero (by simpa [hTangent] using hOutputZero)

/--
What ATOMS 5–7 prove before the tangent bridge.

If the dual root hypothesis gives `(preΨ'_n)'(x)=0`, then the local parameter
coefficient of the output is zero.
-/
theorem output_coeff_zero_of_dual_root
    {φ ω parity deriv : K}
    {outputCoeff : K}
    (hCoeff : outputCoeff = -φ / ω * parity * deriv)
    (hderiv : deriv = 0) :
    outputCoeff = 0 := by
  simp [hCoeff, hderiv]

end Atom8Tangent
```

This is the honest closure: ATOMS 5–7 reduce the problem to tangent nonvanishing,
and `TangentO.nsmul₁` supplies the contradiction.

---

## ATOM 8B: Bezout closure, bypassing the tangent bridge

If you already have

```lean
IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

then bridge-2 closes immediately and does not need projective formula, ATOMS 5–7,
or tangent identification.

```lean
namespace Atom8Bezout

/-- Common evaluated root contradiction from a Bezout/`IsCoprime` certificate. -/
theorem not_root_and_derivative_root_of_isCoprime
    {f : Polynomial K} (hcop : IsCoprime f (Polynomial.derivative f))
    {x : K} :
    ¬ (f.eval x = 0 ∧ (Polynomial.derivative f).eval x = 0) := by
  rcases hcop with ⟨A, B, hAB⟩
  rintro ⟨hf, hdf⟩
  have hEval := congrArg (fun p : Polynomial K => p.eval x) hAB
  -- Depending on your `IsCoprime` orientation, `hAB` may be
  -- `A*f + B*f' = 1` or `f*A + f'*B = 1`; `ring` handles either after rewrites.
  simp [hf, hdf] at hEval

/-- The direct per-`n` bridge-2 closure. -/
theorem bridge2_closed_by_isCoprime
    (W : WeierstrassCurve K) (n : ℕ)
    (hcop : IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)))
    {x : K}
    (hroot : (W.preΨ' n).eval x = 0)
    (hderiv : (Polynomial.derivative (W.preΨ' n)).eval x = 0) :
    False := by
  exact (not_root_and_derivative_root_of_isCoprime (f := W.preΨ' n) hcop)
    ⟨hroot, hderiv⟩

end Atom8Bezout
```

This is why the per-`n` resultant certificates are so effective: they prove the
exact impossibility bridge-2 needs, without any local-parameter or group-law
infrastructure.

---

## Can `IsCoprime(preΨ'_n, (preΨ'_n)')` be proved directly from the projective formula?

Not without proving the tangent/differential statement in some form.

The proposed argument is:

```text
preΨ'_n(x)=0 and (preΨ'_n)'(x)=0
⇒ ψ_n has a double root at P
⇒ [n] ramifies at P
⇒ impossible because d[n] = n ≠ 0.
```

The first two arrows are algebraic and are essentially ATOMS 6–7.  The last arrow
is exactly the tangent theorem:

```text
d[n]_P is multiplication by n on the tangent line.
```

So a theorem

```lean
theorem isCoprime_preΨ'_derivative_of_projective_formula ...
```

would internally need one of the following:

1. the `TangentO.nsmul₁` / formal-group bridge;
2. a scheme-theoretic theorem that `[n]` is étale when `(n : K) ≠ 0`;
3. a resultant/Bezout certificate.

Option 1 is the tangent route.  Option 2 is a larger algebraic-geometry route.
Option 3 is the per-`n` certificate route.  The projective formula by itself only
identifies coordinates of `[n]P`; it does not prove `[n]` is unramified.

---

## Recommended implementation chain

For the tangent route, implement in this order:

1. **ATOM 5:**

   ```lean
   omega_ne_of_phi_ne_at_infinity
   omega_eval_ne_of_phi_eval_ne
   ```

2. **ATOM 6:**

   ```lean
   dual_snd_neg_mul_div_at_infinity
   coeff_t_of_projective_formula_at_root
   ```

3. **ATOM 7:**

   ```lean
   dual_snd_eval_univariate_of_snd_eq_one
   snd_psi_eval_dual_eq_parity_mul_derivative
   ```

4. **ATOM 8 tangent bridge:**

   ```lean
   output_coeff_zero_of_dual_root
   bridge2_contradiction_from_tangent
   ```

The final theorem shape is:

```lean
theorem bridge2_closed_by_tangent
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) (hn : (n : K) ≠ 0)
    {x y : K}
    -- point and non-2-torsion hypotheses
    -- projective formula hypotheses over dual numbers
    -- root and dual-root hypotheses
    : False := by
  -- ATOM 5: `ω_n(P) ≠ 0`
  -- ATOM 6: coefficient of `t_O` is unit times `snd ψ_n(Pε)`
  -- ATOM 7: `snd ψ_n(Pε)` is parity unit times `(preΨ'_n)'(x)`
  -- dual-root hypothesis: derivative is zero, so output coefficient is zero
  -- TangentO/formal group: output coefficient is `(n : K) * inputCoeff`
  -- input tangent chosen with `inputCoeff = 1`; contradiction with `hn`
  sorry
```

For the certificate route, implement only:

```lean
theorem isCoprime_preΨ'_derivative_n
    (W : WeierstrassCurve K) [W.IsElliptic]
    (hn : (n : K) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- per-`n` resultant/Bezout certificate
  ...
```

and close bridge-2 by `bridge2_closed_by_isCoprime`.

## Final assessment

ATOMS 5–7 are worth implementing if you want the local-parameter proof and the
projective formula infrastructure.  They form a clean, reusable chain.  But ATOM 8
cannot be completed from the projective formula alone.  The missing step is not a
coordinate identity; it is the differential identification of `[n]` on the tangent
line.  If the immediate goal is only separability of `preΨ'_n` for the Mazur
range, the per-`n` Bezout certificates remain the shortest closure.

end WeierstrassCurve
```
