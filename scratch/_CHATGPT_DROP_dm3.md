# Q319 (dm3): ATOM 5 complete Lean file — `ω_n(P) ≠ 0` at infinity

Below is the complete file content for

```text
scratch/Atom5OmegaNonzero.lean
```

It uses Mathlib’s existing

```lean
WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
```

which rewrites the Jacobian equation at `Z = 0` to `Y ^ 2 = X ^ 3`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic

/-!
# ATOM 5: nonzero omega at an infinity representative

If a Jacobian representative `[φ : ω : 0]` lies on the Weierstrass curve and
`φ ≠ 0`, then `ω ≠ 0`.  Mathlib already provides the key equation-at-infinity
lemma:

```lean
WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
```

which specializes the Jacobian equation at `Z = 0` to `Y ^ 2 = X ^ 3`.
-/

namespace WeierstrassCurve

open Polynomial

/--
ATOM 5 core lemma.

At `Z = 0`, the Jacobian equation gives `ω² = φ³`.  If `ω = 0`, then
`φ³ = 0`, contradicting `φ ≠ 0` over a field.
-/
theorem omega_ne_zero_of_phi_ne_zero_at_torsion
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {φ_val ω_val : K}
    (hEq : W.toJacobian.Equation ![φ_val, ω_val, 0])
    (hφ : φ_val ≠ 0) :
    ω_val ≠ 0 := by
  have hEqInf : ω_val ^ 2 = φ_val ^ 3 := by
    have h :=
      (WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
        (W' := W.toJacobian)
        (P := ![φ_val, ω_val, 0])
        (by rfl)).mp hEq
    simpa using h
  intro hω
  have hφ3 : φ_val ^ 3 = 0 := by
    simpa [hω] using hEqInf.symm
  exact (pow_ne_zero 3 hφ) hφ3

/--
Bivariate evaluation convention for `K[X][Y]`.

The outer polynomial variable is `Y`; coefficients are polynomials in `X`.
Thus evaluation at `(x,y)` first substitutes `Y := C y`, then evaluates the
remaining univariate polynomial at `X := x`.
-/
noncomputable def evalBivar
    {K : Type*} [CommSemiring K]
    (p : Polynomial (Polynomial K)) (x y : K) : K :=
  (p.eval (Polynomial.C y)).eval x

/--
ATOM 5 evaluated version.

This is the same statement for bivariate polynomials `φ_n, ω_n`, after evaluating
at an affine point `(x,y)`.  The caller supplies the evaluated Jacobian equation
with `Z = 0`; in applications this comes from the projective formula and the
hypothesis `ψ_n(P) = 0`.
-/
theorem omega_eval_ne_zero_of_phi_eval_ne_zero_at_torsion
    {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (φ_poly ω_poly : Polynomial (Polynomial K)) {x y : K}
    (hEq : W.toJacobian.Equation
      ![evalBivar φ_poly x y, evalBivar ω_poly x y, 0])
    (hφ : evalBivar φ_poly x y ≠ 0) :
    evalBivar ω_poly x y ≠ 0 := by
  exact omega_ne_zero_of_phi_ne_zero_at_torsion
    (W := W) hEq hφ

end WeierstrassCurve
```

## Notes

The `[W.IsElliptic]` hypothesis is included to match the downstream ATOM-chain
context, but the proof of this atom uses only the field structure and the
Jacobian equation at `Z = 0`.

If your local file already has a project-wide bivariate evaluation helper, replace
`evalBivar` by that helper and the evaluated theorem becomes the same one-line
wrapper around `omega_ne_zero_of_phi_ne_zero_at_torsion`.
